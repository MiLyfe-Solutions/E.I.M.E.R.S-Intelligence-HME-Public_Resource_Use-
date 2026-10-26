import V185TrunkScan23Chunk1276

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7565850 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_7565850 : Nat := 118140960795 + 7565850 * 2 ^ 59
def prefixEnd_7565850 : Nat := 4983230072969 + 3 ^ 40 * 7565850 * 2
def baseEnd_7565850 : Nat := 431657512202147645642255

theorem tailTrace_7565850 : CollatzResearch.WordTrace tailWord_7565850 prefixEnd_7565850 431657512202147645642255 := by
  unfold tailWord_7565850
  simp only [CollatzResearch.WordTrace]
  refine ⟨68987304910056267288061751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183966146426816712768164669 68987304910056267288061751)
  ·
    refine ⟨103480957365084400932092627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68987304910056267288061751 103480957365084400932092627)
    ·
      refine ⟨155221436047626601398138941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103480957365084400932092627 155221436047626601398138941)
      ·
        refine ⟨58208038517859975524302103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155221436047626601398138941 58208038517859975524302103)
        ·
          refine ⟨87312057776789963286453155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58208038517859975524302103 87312057776789963286453155)
          ·
            refine ⟨130968086665184944929679733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87312057776789963286453155 130968086665184944929679733)
            ·
              refine ⟨12278258124861088587157475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130968086665184944929679733 12278258124861088587157475)
              ·
                refine ⟨18417387187291632880736213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12278258124861088587157475 18417387187291632880736213)
                ·
                  refine ⟨431657512202147645642255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18417387187291632880736213 431657512202147645642255)
                  ·
                    rfl

theorem cell23_7565850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_7565850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565850 prefixEnd_7565850 := by exact prefixLift 7565850
  have htrace : WordTrace (prefixWord ++ tailWord_7565850) baseStart_7565850 baseEnd_7565850 := by
    simpa [prefixWord, tailWord_7565850, baseEnd_7565850] using wordTrace_append hprefix tailTrace_7565850
  have hstable : (prefixWord ++ tailWord_7565850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565850).length < 2 ^ (prefixWord ++ tailWord_7565850).sum := by decide
  have hdescent : baseEnd_7565850 < baseStart_7565850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565861 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 2, 2, 2]
def baseStart_7565861 : Nat := 118140960795 + 7565861 * 2 ^ 59
def prefixEnd_7565861 : Nat := 4983230072969 + 3 ^ 40 * 7565861 * 2
def baseEnd_7565861 : Nat := 3884923258106528267742745

theorem tailTrace_7565861 : CollatzResearch.WordTrace tailWord_7565861 prefixEnd_7565861 3884923258106528267742745 := by
  unfold tailWord_7565861
  simp only [CollatzResearch.WordTrace]
  refine ⟨275949620843185218030897437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183966413895456812020598291 275949620843185218030897437)
  ·
    refine ⟨103481107816194456761586539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275949620843185218030897437 103481107816194456761586539)
    ·
      refine ⟨155221661724291685142379809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103481107816194456761586539 155221661724291685142379809)
      ·
        refine ⟨116416246293218763856784857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155221661724291685142379809 116416246293218763856784857)
        ·
          refine ⟨87312184719914072892588643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116416246293218763856784857 87312184719914072892588643)
          ·
            refine ⟨130968277079871109338882965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87312184719914072892588643 130968277079871109338882965)
            ·
              refine ⟨6139137988118958250260139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130968277079871109338882965 6139137988118958250260139)
              ·
                refine ⟨9208706982178437375390209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139137988118958250260139 9208706982178437375390209)
                ·
                  refine ⟨6906530236633828031542657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208706982178437375390209 6906530236633828031542657)
                  ·
                    refine ⟨5179897677475371023656993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6906530236633828031542657 5179897677475371023656993)
                    ·
                      refine ⟨3884923258106528267742745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179897677475371023656993 3884923258106528267742745)
                      ·
                        rfl

theorem cell23_7565861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_7565861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565861 prefixEnd_7565861 := by exact prefixLift 7565861
  have htrace : WordTrace (prefixWord ++ tailWord_7565861) baseStart_7565861 baseEnd_7565861 := by
    simpa [prefixWord, tailWord_7565861, baseEnd_7565861] using wordTrace_append hprefix tailTrace_7565861
  have hstable : (prefixWord ++ tailWord_7565861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565861).length < 2 ^ (prefixWord ++ tailWord_7565861).sum := by decide
  have hdescent : baseEnd_7565861 < baseStart_7565861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565901 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 5]
def baseStart_7565901 : Nat := 118140960795 + 7565901 * 2 ^ 59
def prefixEnd_7565901 : Nat := 4983230072969 + 3 ^ 40 * 7565901 * 2
def baseEnd_7565901 : Nat := 431660421925856456804729

theorem tailTrace_7565901 : CollatzResearch.WordTrace tailWord_7565901 prefixEnd_7565901 431660421925856456804729 := by
  unfold tailWord_7565901
  simp only [CollatzResearch.WordTrace]
  refine ⟨275951079763040304862353557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183967386508693536574902371 275951079763040304862353557)
  ·
    refine ⟨12935206863892514290422823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275951079763040304862353557 12935206863892514290422823)
    ·
      refine ⟨19402810295838771435634235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12935206863892514290422823 19402810295838771435634235)
      ·
        refine ⟨29104215443758157153451353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19402810295838771435634235 29104215443758157153451353)
        ·
          refine ⟨21828161582818617865088515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29104215443758157153451353 21828161582818617865088515)
          ·
            refine ⟨32742242374227926797632773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21828161582818617865088515 32742242374227926797632773)
            ·
              refine ⟨6139170445167736274556145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32742242374227926797632773 6139170445167736274556145)
              ·
                refine ⟨4604377833875802205917109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139170445167736274556145 4604377833875802205917109)
                ·
                  refine ⟨431660421925856456804729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604377833875802205917109 431660421925856456804729)
                  ·
                    rfl

theorem cell23_7565901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_7565901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565901 prefixEnd_7565901 := by exact prefixLift 7565901
  have htrace : WordTrace (prefixWord ++ tailWord_7565901) baseStart_7565901 baseEnd_7565901 := by
    simpa [prefixWord, tailWord_7565901, baseEnd_7565901] using wordTrace_append hprefix tailTrace_7565901
  have hstable : (prefixWord ++ tailWord_7565901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565901).length < 2 ^ (prefixWord ++ tailWord_7565901).sum := by decide
  have hdescent : baseEnd_7565901 < baseStart_7565901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565934 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_7565934 : Nat := 118140960795 + 7565934 * 2 ^ 59
def prefixEnd_7565934 : Nat := 4983230072969 + 3 ^ 40 * 7565934 * 2
def baseEnd_7565934 : Nat := 3884960742194306482129909

theorem tailTrace_7565934 : CollatzResearch.WordTrace tailWord_7565934 prefixEnd_7565934 3884960742194306482129909 := by
  unfold tailWord_7565934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34494035421490093937288107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183968188914613834332203237 34494035421490093937288107)
  ·
    refine ⟨51741053132235140905932161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34494035421490093937288107 51741053132235140905932161)
    ·
      refine ⟨38805789849176355679449121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51741053132235140905932161 38805789849176355679449121)
      ·
        refine ⟨29104342386882266759586841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38805789849176355679449121 29104342386882266759586841)
        ·
          refine ⟨21828256790161700069690131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29104342386882266759586841 21828256790161700069690131)
          ·
            refine ⟨32742385185242550104535197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21828256790161700069690131 32742385185242550104535197)
            ·
              refine ⟨12278394444465956289200699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32742385185242550104535197 12278394444465956289200699)
              ·
                refine ⟨18417591666698934433801049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12278394444465956289200699 18417591666698934433801049)
                ·
                  refine ⟨13813193750024200825350787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18417591666698934433801049 13813193750024200825350787)
                  ·
                    refine ⟨20719790625036301238026181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13813193750024200825350787 20719790625036301238026181)
                    ·
                      refine ⟨3884960742194306482129909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20719790625036301238026181 3884960742194306482129909)
                      ·
                        rfl

theorem cell23_7565934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_7565934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565934 prefixEnd_7565934 := by exact prefixLift 7565934
  have htrace : WordTrace (prefixWord ++ tailWord_7565934) baseStart_7565934 baseEnd_7565934 := by
    simpa [prefixWord, tailWord_7565934, baseEnd_7565934] using wordTrace_append hprefix tailTrace_7565934
  have hstable : (prefixWord ++ tailWord_7565934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565934).length < 2 ^ (prefixWord ++ tailWord_7565934).sum := by decide
  have hdescent : baseEnd_7565934 < baseStart_7565934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565957 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 6]
def baseStart_7565957 : Nat := 118140960795 + 7565957 * 2 ^ 59
def prefixEnd_7565957 : Nat := 4983230072969 + 3 ^ 40 * 7565957 * 2
def baseEnd_7565957 : Nat := 431663616916595543571367

theorem tailTrace_7565957 : CollatzResearch.WordTrace tailWord_7565957 prefixEnd_7565957 431663616916595543571367 := by
  unfold tailWord_7565957
  simp only [CollatzResearch.WordTrace]
  refine ⟨275953122250837426426392125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183968748167224950950928083 275953122250837426426392125)
  ·
    refine ⟨103482420844064034909897047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275953122250837426426392125 103482420844064034909897047)
    ·
      refine ⟨155223631266096052364845571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103482420844064034909897047 155223631266096052364845571)
      ·
        refine ⟨232835446899144078547268357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155223631266096052364845571 232835446899144078547268357)
        ·
          refine ⟨43656646293589514727612817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232835446899144078547268357 43656646293589514727612817)
          ·
            refine ⟨32742484720192136045709613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43656646293589514727612817 32742484720192136045709613)
            ·
              refine ⟨12278431770072051017141105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32742484720192136045709613 12278431770072051017141105)
              ·
                refine ⟨9208823827554038262855829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12278431770072051017141105 9208823827554038262855829)
                ·
                  refine ⟨431663616916595543571367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9208823827554038262855829 431663616916595543571367)
                  ·
                    rfl

theorem cell23_7565957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_7565957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565957 prefixEnd_7565957 := by exact prefixLift 7565957
  have htrace : WordTrace (prefixWord ++ tailWord_7565957) baseStart_7565957 baseEnd_7565957 := by
    simpa [prefixWord, tailWord_7565957, baseEnd_7565957] using wordTrace_append hprefix tailTrace_7565957
  have hstable : (prefixWord ++ tailWord_7565957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565957).length < 2 ^ (prefixWord ++ tailWord_7565957).sum := by decide
  have hdescent : baseEnd_7565957 < baseStart_7565957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565967 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 3]
def baseStart_7565967 : Nat := 118140960795 + 7565967 * 2 ^ 59
def prefixEnd_7565967 : Nat := 4983230072969 + 3 ^ 40 * 7565967 * 2
def baseEnd_7565967 : Nat := 3884977687055904853017257

theorem tailTrace_7565967 : CollatzResearch.WordTrace tailWord_7565967 prefixEnd_7565967 3884977687055904853017257 := by
  unfold tailWord_7565967
  simp only [CollatzResearch.WordTrace]
  refine ⟨275953486980801198134256155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183968991320534132089504103 275953486980801198134256155)
  ·
    refine ⟨413930230471201797201384233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275953486980801198134256155 413930230471201797201384233)
    ·
      refine ⟨310447672853401347901038175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413930230471201797201384233 310447672853401347901038175)
      ·
        refine ⟨465671509280102021851557263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310447672853401347901038175 465671509280102021851557263)
        ·
          refine ⟨698507263920153032777335895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465671509280102021851557263 698507263920153032777335895)
          ·
            refine ⟨1047760895880229549166003843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698507263920153032777335895 1047760895880229549166003843)
            ·
              refine ⟨1571641343820344323749005765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047760895880229549166003843 1571641343820344323749005765)
              ·
                refine ⟨294682751966314560702938581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1571641343820344323749005765 294682751966314560702938581)
                ·
                  refine ⟨6906626999210497516475123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 294682751966314560702938581 6906626999210497516475123)
                  ·
                    refine ⟨10359940498815746274712685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906626999210497516475123 10359940498815746274712685)
                    ·
                      refine ⟨3884977687055904853017257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10359940498815746274712685 3884977687055904853017257)
                      ·
                        rfl

theorem cell23_7565967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_7565967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565967 prefixEnd_7565967 := by exact prefixLift 7565967
  have htrace : WordTrace (prefixWord ++ tailWord_7565967) baseStart_7565967 baseEnd_7565967 := by
    simpa [prefixWord, tailWord_7565967, baseEnd_7565967] using wordTrace_append hprefix tailTrace_7565967
  have hstable : (prefixWord ++ tailWord_7565967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565967).length < 2 ^ (prefixWord ++ tailWord_7565967).sum := by decide
  have hdescent : baseEnd_7565967 < baseStart_7565967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565977 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 3, 5, 2]
def baseStart_7565977 : Nat := 118140960795 + 7565977 * 2 ^ 59
def prefixEnd_7565977 : Nat := 4983230072969 + 3 ^ 40 * 7565977 * 2
def baseEnd_7565977 : Nat := 3884982821862449813892211

theorem tailTrace_7565977 : CollatzResearch.WordTrace tailWord_7565977 prefixEnd_7565977 3884982821862449813892211 := by
  unfold tailWord_7565977
  simp only [CollatzResearch.WordTrace]
  refine ⟨275953851710764969842120185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183969234473843313228080123 275953851710764969842120185)
  ·
    refine ⟨206965388783073727381590139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275953851710764969842120185 206965388783073727381590139)
    ·
      refine ⟨310448083174610591072385209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206965388783073727381590139 310448083174610591072385209)
      ·
        refine ⟨232836062380957943304288907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310448083174610591072385209 232836062380957943304288907)
        ·
          refine ⟨349254093571436914956433361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232836062380957943304288907 349254093571436914956433361)
          ·
            refine ⟨261940570178577686217325021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349254093571436914956433361 261940570178577686217325021)
            ·
              refine ⟨98227713816966632331496883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261940570178577686217325021 98227713816966632331496883)
              ·
                refine ⟨147341570725449948497245325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98227713816966632331496883 147341570725449948497245325)
                ·
                  refine ⟨55253089022043730686466997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147341570725449948497245325 55253089022043730686466997)
                  ·
                    refine ⟨5179977095816599751856281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55253089022043730686466997 5179977095816599751856281)
                    ·
                      refine ⟨3884982821862449813892211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179977095816599751856281 3884982821862449813892211)
                      ·
                        rfl

theorem cell23_7565977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_7565977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565977 prefixEnd_7565977 := by exact prefixLift 7565977
  have htrace : WordTrace (prefixWord ++ tailWord_7565977) baseStart_7565977 baseEnd_7565977 := by
    simpa [prefixWord, tailWord_7565977, baseEnd_7565977] using wordTrace_append hprefix tailTrace_7565977
  have hstable : (prefixWord ++ tailWord_7565977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565977).length < 2 ^ (prefixWord ++ tailWord_7565977).sum := by decide
  have hdescent : baseEnd_7565977 < baseStart_7565977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566000 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_7566000 : Nat := 118140960795 + 7566000 * 2 ^ 59
def prefixEnd_7566000 : Nat := 4983230072969 + 3 ^ 40 * 7566000 * 2
def baseEnd_7566000 : Nat := 1294998210639167741301535

theorem tailTrace_7566000 : CollatzResearch.WordTrace tailWord_7566000 prefixEnd_7566000 1294998210639167741301535 := by
  unfold tailWord_7566000
  simp only [CollatzResearch.WordTrace]
  refine ⟨137977345294840822385103727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183969793726454429846804969 137977345294840822385103727)
  ·
    refine ⟨206966017942261233577655591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137977345294840822385103727 206966017942261233577655591)
    ·
      refine ⟨310449026913391850366483387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206966017942261233577655591 310449026913391850366483387)
      ·
        refine ⟨465673540370087775549725081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310449026913391850366483387 465673540370087775549725081)
        ·
          refine ⟨349255155277565831662293811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465673540370087775549725081 349255155277565831662293811)
          ·
            refine ⟨523882732916348747493440717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349255155277565831662293811 523882732916348747493440717)
            ·
              refine ⟨196456024843630780310040269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523882732916348747493440717 196456024843630780310040269)
              ·
                refine ⟨73671009316361542616265101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196456024843630780310040269 73671009316361542616265101)
                ·
                  refine ⟨27626628493635578481099413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73671009316361542616265101 27626628493635578481099413)
                  ·
                    refine ⟨1294998210639167741301535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27626628493635578481099413 1294998210639167741301535)
                    ·
                      rfl

theorem cell23_7566000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_7566000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566000 prefixEnd_7566000 := by exact prefixLift 7566000
  have htrace : WordTrace (prefixWord ++ tailWord_7566000) baseStart_7566000 baseEnd_7566000 := by
    simpa [prefixWord, tailWord_7566000, baseEnd_7566000] using wordTrace_append hprefix tailTrace_7566000
  have hstable : (prefixWord ++ tailWord_7566000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566000).length < 2 ^ (prefixWord ++ tailWord_7566000).sum := by decide
  have hdescent : baseEnd_7566000 < baseStart_7566000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566057 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_7566057 : Nat := 118140960795 + 7566057 * 2 ^ 59
def prefixEnd_7566057 : Nat := 4983230072969 + 3 ^ 40 * 7566057 * 2
def baseEnd_7566057 : Nat := 3885023900314809500891843

theorem tailTrace_7566057 : CollatzResearch.WordTrace tailWord_7566057 prefixEnd_7566057 3885023900314809500891843 := by
  unfold tailWord_7566057
  simp only [CollatzResearch.WordTrace]
  refine ⟨275956769550475143505032425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183971179700316762336688283 275956769550475143505032425)
  ·
    refine ⟨206967577162856357628774319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275956769550475143505032425 206967577162856357628774319)
    ·
      refine ⟨310451365744284536443161479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206967577162856357628774319 310451365744284536443161479)
      ·
        refine ⟨465677048616426804664742219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310451365744284536443161479 465677048616426804664742219)
        ·
          refine ⟨698515572924640206997113329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465677048616426804664742219 698515572924640206997113329)
          ·
            refine ⟨523886679693480155247834997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698515572924640206997113329 523886679693480155247834997)
            ·
              refine ⟨49114376221263764554484531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523886679693480155247834997 49114376221263764554484531)
              ·
                refine ⟨73671564331895646831726797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49114376221263764554484531 73671564331895646831726797)
                ·
                  refine ⟨27626836624460867561897549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73671564331895646831726797 27626836624460867561897549)
                  ·
                    refine ⟨10360063734172825335711581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27626836624460867561897549 10360063734172825335711581)
                    ·
                      refine ⟨3885023900314809500891843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360063734172825335711581 3885023900314809500891843)
                      ·
                        rfl

theorem cell23_7566057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_7566057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566057 prefixEnd_7566057 := by exact prefixLift 7566057
  have htrace : WordTrace (prefixWord ++ tailWord_7566057) baseStart_7566057 baseEnd_7566057 := by
    simpa [prefixWord, tailWord_7566057, baseEnd_7566057] using wordTrace_append hprefix tailTrace_7566057
  have hstable : (prefixWord ++ tailWord_7566057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566057).length < 2 ^ (prefixWord ++ tailWord_7566057).sum := by decide
  have hdescent : baseEnd_7566057 < baseStart_7566057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566058 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_7566058 : Nat := 118140960795 + 7566058 * 2 ^ 59
def prefixEnd_7566058 : Nat := 4983230072969 + 3 ^ 40 * 7566058 * 2
def baseEnd_7566058 : Nat := 3885024413795463996979339

theorem tailTrace_7566058 : CollatzResearch.WordTrace tailWord_7566058 prefixEnd_7566058 3885024413795463996979339 := by
  unfold tailWord_7566058
  simp only [CollatzResearch.WordTrace]
  refine ⟨68989201505867880168954707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183971204015647680450545885 68989201505867880168954707)
  ·
    refine ⟨103483802258801820253432061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68989201505867880168954707 103483802258801820253432061)
    ·
      refine ⟨38806425847050682595037023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103483802258801820253432061 38806425847050682595037023)
      ·
        refine ⟨58209638770576023892555535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38806425847050682595037023 58209638770576023892555535)
        ·
          refine ⟨87314458155864035838833303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58209638770576023892555535 87314458155864035838833303)
          ·
            refine ⟨130971687233796053758249955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87314458155864035838833303 130971687233796053758249955)
            ·
              refine ⟨196457530850694080637374933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130971687233796053758249955 196457530850694080637374933)
              ·
                refine ⟨4604473379313142514938475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 196457530850694080637374933 4604473379313142514938475)
                ·
                  refine ⟨6906710068969713772407713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604473379313142514938475 6906710068969713772407713)
                  ·
                    refine ⟨5180032551727285329305785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6906710068969713772407713 5180032551727285329305785)
                    ·
                      refine ⟨3885024413795463996979339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180032551727285329305785 3885024413795463996979339)
                      ·
                        rfl

theorem cell23_7566058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_7566058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566058 prefixEnd_7566058 := by exact prefixLift 7566058
  have htrace : WordTrace (prefixWord ++ tailWord_7566058) baseStart_7566058 baseEnd_7566058 := by
    simpa [prefixWord, tailWord_7566058, baseEnd_7566058] using wordTrace_append hprefix tailTrace_7566058
  have hstable : (prefixWord ++ tailWord_7566058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566058).length < 2 ^ (prefixWord ++ tailWord_7566058).sum := by decide
  have hdescent : baseEnd_7566058 < baseStart_7566058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566074 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_7566074 : Nat := 118140960795 + 7566074 * 2 ^ 59
def prefixEnd_7566074 : Nat := 4983230072969 + 3 ^ 40 * 7566074 * 2
def baseEnd_7566074 : Nat := 3885032629485935934379265

theorem tailTrace_7566074 : CollatzResearch.WordTrace tailWord_7566074 prefixEnd_7566074 3885032629485935934379265 := by
  unfold tailWord_7566074
  simp only [CollatzResearch.WordTrace]
  refine ⟨68989347397853388852100319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183971593060942370272267517 68989347397853388852100319)
  ·
    refine ⟨103484021096780083278150479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68989347397853388852100319 103484021096780083278150479)
    ·
      refine ⟨155226031645170124917225719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103484021096780083278150479 155226031645170124917225719)
      ·
        refine ⟨232839047467755187375838579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155226031645170124917225719 232839047467755187375838579)
        ·
          refine ⟨349258571201632781063757869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232839047467755187375838579 349258571201632781063757869)
          ·
            refine ⟨130971964200612292898909201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349258571201632781063757869 130971964200612292898909201)
            ·
              refine ⟨98228973150459219674181901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130971964200612292898909201 98228973150459219674181901)
              ·
                refine ⟨36835864931422207377818213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98228973150459219674181901 36835864931422207377818213)
                ·
                  refine ⟨6906724674641663883340915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36835864931422207377818213 6906724674641663883340915)
                  ·
                    refine ⟨10360087011962495825011373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906724674641663883340915 10360087011962495825011373)
                    ·
                      refine ⟨3885032629485935934379265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360087011962495825011373 3885032629485935934379265)
                      ·
                        rfl

theorem cell23_7566074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_7566074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566074 prefixEnd_7566074 := by exact prefixLift 7566074
  have htrace : WordTrace (prefixWord ++ tailWord_7566074) baseStart_7566074 baseEnd_7566074 := by
    simpa [prefixWord, tailWord_7566074, baseEnd_7566074] using wordTrace_append hprefix tailTrace_7566074
  have hstable : (prefixWord ++ tailWord_7566074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566074).length < 2 ^ (prefixWord ++ tailWord_7566074).sum := by decide
  have hdescent : baseEnd_7566074 < baseStart_7566074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566101 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_7566101 : Nat := 118140960795 + 7566101 * 2 ^ 59
def prefixEnd_7566101 : Nat := 4983230072969 + 3 ^ 40 * 7566101 * 2
def baseEnd_7566101 : Nat := 3885046493463607328741641

theorem tailTrace_7566101 : CollatzResearch.WordTrace tailWord_7566101 prefixEnd_7566101 3885046493463607328741641 := by
  unfold tailWord_7566101
  simp only [CollatzResearch.WordTrace]
  refine ⟨275958374362315739019634157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183972249574877159346422771 275958374362315739019634157)
  ·
    refine ⟨103484390385868402132362809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275958374362315739019634157 103484390385868402132362809)
    ·
      refine ⟨77613292789401301599272107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103484390385868402132362809 77613292789401301599272107)
      ·
        refine ⟨116419939184101952398908161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77613292789401301599272107 116419939184101952398908161)
        ·
          refine ⟨87314954388076464299181121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116419939184101952398908161 87314954388076464299181121)
          ·
            refine ⟨65486215791057348224385841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87314954388076464299181121 65486215791057348224385841)
            ·
              refine ⟨49114661843293011168289381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65486215791057348224385841 49114661843293011168289381)
              ·
                refine ⟨9208999095617439594054259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49114661843293011168289381 9208999095617439594054259)
                ·
                  refine ⟨13813498643426159391081389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9208999095617439594054259 13813498643426159391081389)
                  ·
                    refine ⟨5180061991284809771655521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13813498643426159391081389 5180061991284809771655521)
                    ·
                      refine ⟨3885046493463607328741641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180061991284809771655521 3885046493463607328741641)
                      ·
                        rfl

theorem cell23_7566101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_7566101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566101 prefixEnd_7566101 := by exact prefixLift 7566101
  have htrace : WordTrace (prefixWord ++ tailWord_7566101) baseStart_7566101 baseEnd_7566101 := by
    simpa [prefixWord, tailWord_7566101, baseEnd_7566101] using wordTrace_append hprefix tailTrace_7566101
  have hstable : (prefixWord ++ tailWord_7566101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566101).length < 2 ^ (prefixWord ++ tailWord_7566101).sum := by decide
  have hdescent : baseEnd_7566101 < baseStart_7566101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566117 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_7566117 : Nat := 118140960795 + 7566117 * 2 ^ 59
def prefixEnd_7566117 : Nat := 4983230072969 + 3 ^ 40 * 7566117 * 2
def baseEnd_7566117 : Nat := 3885054709154079266141567

theorem tailTrace_7566117 : CollatzResearch.WordTrace tailWord_7566117 prefixEnd_7566117 3885054709154079266141567 := by
  unfold tailWord_7566117
  simp only [CollatzResearch.WordTrace]
  refine ⟨275958957930257773752216605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183972638620171849168144403 275958957930257773752216605)
  ·
    refine ⟨103484609223846665157081227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275958957930257773752216605 103484609223846665157081227)
    ·
      refine ⟨155226913835769997735621841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103484609223846665157081227 155226913835769997735621841)
      ·
        refine ⟨116420185376827498301716381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155226913835769997735621841 116420185376827498301716381)
        ·
          refine ⟨43657569516310311863143643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116420185376827498301716381 43657569516310311863143643)
          ·
            refine ⟨65486354274465467794715465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43657569516310311863143643 65486354274465467794715465)
            ·
              refine ⟨49114765705849100846036599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65486354274465467794715465 49114765705849100846036599)
              ·
                refine ⟨73672148558773651269054899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49114765705849100846036599 73672148558773651269054899)
                ·
                  refine ⟨110508222838160476903582349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73672148558773651269054899 110508222838160476903582349)
                  ·
                    refine ⟨41440583564310178838843381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110508222838160476903582349 41440583564310178838843381)
                    ·
                      refine ⟨3885054709154079266141567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41440583564310178838843381 3885054709154079266141567)
                      ·
                        rfl

theorem cell23_7566117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_7566117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566117 prefixEnd_7566117 := by exact prefixLift 7566117
  have htrace : WordTrace (prefixWord ++ tailWord_7566117) baseStart_7566117 baseEnd_7566117 := by
    simpa [prefixWord, tailWord_7566117, baseEnd_7566117] using wordTrace_append hprefix tailTrace_7566117
  have hstable : (prefixWord ++ tailWord_7566117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566117).length < 2 ^ (prefixWord ++ tailWord_7566117).sum := by decide
  have hdescent : baseEnd_7566117 < baseStart_7566117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566125 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7566125 : Nat := 118140960795 + 7566125 * 2 ^ 59
def prefixEnd_7566125 : Nat := 4983230072969 + 3 ^ 40 * 7566125 * 2
def baseEnd_7566125 : Nat := 3885058816999315234841531

theorem tailTrace_7566125 : CollatzResearch.WordTrace tailWord_7566125 prefixEnd_7566125 3885058816999315234841531 := by
  unfold tailWord_7566125
  simp only [CollatzResearch.WordTrace]
  refine ⟨275959249714228791118507829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183972833142819194079005219 275959249714228791118507829)
  ·
    refine ⟨25871179660708949167360109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275959249714228791118507829 25871179660708949167360109)
    ·
      refine ⟨9701692372765855937760041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25871179660708949167360109 9701692372765855937760041)
      ·
        refine ⟨7276269279574391953320031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9701692372765855937760041 7276269279574391953320031)
        ·
          refine ⟨10914403919361587929980047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276269279574391953320031 10914403919361587929980047)
          ·
            refine ⟨16371605879042381894970071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10914403919361587929980047 16371605879042381894970071)
            ·
              refine ⟨24557408818563572842455107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16371605879042381894970071 24557408818563572842455107)
              ·
                refine ⟨36836113227845359263682661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24557408818563572842455107 36836113227845359263682661)
                ·
                  refine ⟨6906771230221004861940499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36836113227845359263682661 6906771230221004861940499)
                  ·
                    refine ⟨10360156845331507292910749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906771230221004861940499 10360156845331507292910749)
                    ·
                      refine ⟨3885058816999315234841531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360156845331507292910749 3885058816999315234841531)
                      ·
                        rfl

theorem cell23_7566125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7566125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566125 prefixEnd_7566125 := by exact prefixLift 7566125
  have htrace : WordTrace (prefixWord ++ tailWord_7566125) baseStart_7566125 baseEnd_7566125 := by
    simpa [prefixWord, tailWord_7566125, baseEnd_7566125] using wordTrace_append hprefix tailTrace_7566125
  have hstable : (prefixWord ++ tailWord_7566125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566125).length < 2 ^ (prefixWord ++ tailWord_7566125).sum := by decide
  have hdescent : baseEnd_7566125 < baseStart_7566125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566184 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_7566184 : Nat := 118140960795 + 7566184 * 2 ^ 59
def prefixEnd_7566184 : Nat := 4983230072969 + 3 ^ 40 * 7566184 * 2
def baseEnd_7566184 : Nat := 1295029704119310168001253

theorem tailTrace_7566184 : CollatzResearch.WordTrace tailWord_7566184 prefixEnd_7566184 1295029704119310168001253 := by
  unfold tailWord_7566184
  simp only [CollatzResearch.WordTrace]
  refine ⟨137980700810507522097452803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183974267747343362796603737 137980700810507522097452803)
  ·
    refine ⟨206971051215761283146179205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137980700810507522097452803 206971051215761283146179205)
    ·
      refine ⟨38807072102955240589908601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206971051215761283146179205 38807072102955240589908601)
      ·
        refine ⟨29105304077216430442431451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38807072102955240589908601 29105304077216430442431451)
        ·
          refine ⟨43657956115824645663647177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29105304077216430442431451 43657956115824645663647177)
          ·
            refine ⟨32743467086868484247735383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43657956115824645663647177 32743467086868484247735383)
            ·
              refine ⟨49115200630302726371603075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32743467086868484247735383 49115200630302726371603075)
              ·
                refine ⟨73672800945454089557404613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49115200630302726371603075 73672800945454089557404613)
                ·
                  refine ⟨13813650177272641792013365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73672800945454089557404613 13813650177272641792013365)
                  ·
                    refine ⟨1295029704119310168001253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13813650177272641792013365 1295029704119310168001253)
                    ·
                      rfl

theorem cell23_7566184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_7566184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566184 prefixEnd_7566184 := by exact prefixLift 7566184
  have htrace : WordTrace (prefixWord ++ tailWord_7566184) baseStart_7566184 baseEnd_7566184 := by
    simpa [prefixWord, tailWord_7566184, baseEnd_7566184] using wordTrace_append hprefix tailTrace_7566184
  have hstable : (prefixWord ++ tailWord_7566184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566184).length < 2 ^ (prefixWord ++ tailWord_7566184).sum := by decide
  have hdescent : baseEnd_7566184 < baseStart_7566184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566227 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 8]
def baseStart_7566227 : Nat := 118140960795 + 7566227 * 2 ^ 59
def prefixEnd_7566227 : Nat := 4983230072969 + 3 ^ 40 * 7566227 * 2
def baseEnd_7566227 : Nat := 431679021336230426196229

theorem tailTrace_7566227 : CollatzResearch.WordTrace tailWord_7566227 prefixEnd_7566227 431679021336230426196229 := by
  unfold tailWord_7566227
  simp only [CollatzResearch.WordTrace]
  refine ⟨275962969959859262538720935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183975313306572841692480623 275962969959859262538720935)
  ·
    refine ⟨413944454939788893808081403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275962969959859262538720935 413944454939788893808081403)
    ·
      refine ⟨620916682409683340712122105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413944454939788893808081403 620916682409683340712122105)
      ·
        refine ⟨465687511807262505534091579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620916682409683340712122105 465687511807262505534091579)
        ·
          refine ⟨698531267710893758301137369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465687511807262505534091579 698531267710893758301137369)
          ·
            refine ⟨523898450783170318725853027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698531267710893758301137369 523898450783170318725853027)
            ·
              refine ⟨785847676174755478088779541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523898450783170318725853027 785847676174755478088779541)
              ·
                refine ⟨36836609820691663035411541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 785847676174755478088779541 36836609820691663035411541)
                ·
                  refine ⟨431679021336230426196229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36836609820691663035411541 431679021336230426196229)
                  ·
                    rfl

theorem cell23_7566227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 8].length) (baseStart_7566227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566227 prefixEnd_7566227 := by exact prefixLift 7566227
  have htrace : WordTrace (prefixWord ++ tailWord_7566227) baseStart_7566227 baseEnd_7566227 := by
    simpa [prefixWord, tailWord_7566227, baseEnd_7566227] using wordTrace_append hprefix tailTrace_7566227
  have hstable : (prefixWord ++ tailWord_7566227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566227).length < 2 ^ (prefixWord ++ tailWord_7566227).sum := by decide
  have hdescent : baseEnd_7566227 < baseStart_7566227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566321 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 1, 6]
def baseStart_7566321 : Nat := 118140960795 + 7566321 * 2 ^ 59
def prefixEnd_7566321 : Nat := 4983230072969 + 3 ^ 40 * 7566321 * 2
def baseEnd_7566321 : Nat := 1295053153069198822663543

theorem tailTrace_7566321 : CollatzResearch.WordTrace tailWord_7566321 prefixEnd_7566321 1295053153069198822663543 := by
  unfold tailWord_7566321
  simp only [CollatzResearch.WordTrace]
  refine ⟨275966398421518716592642817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183977598947679144395095211 275966398421518716592642817)
  ·
    refine ⟨206974798816139037444482113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275966398421518716592642817 206974798816139037444482113)
    ·
      refine ⟨155231099112104278083361585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206974798816139037444482113 155231099112104278083361585)
      ·
        refine ⟨116423324334078208562521189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155231099112104278083361585 116423324334078208562521189)
        ·
          refine ⟨21829373312639664105472723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116423324334078208562521189 21829373312639664105472723)
          ·
            refine ⟨32744059968959496158209085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21829373312639664105472723 32744059968959496158209085)
            ·
              refine ⟨12279022488359811059328407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32744059968959496158209085 12279022488359811059328407)
              ·
                refine ⟨18418533732539716588992611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12279022488359811059328407 18418533732539716588992611)
                ·
                  refine ⟨27627800598809574883488917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18418533732539716588992611 27627800598809574883488917)
                  ·
                    refine ⟨1295053153069198822663543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27627800598809574883488917 1295053153069198822663543)
                    ·
                      rfl

theorem cell23_7566321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_7566321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566321 prefixEnd_7566321 := by exact prefixLift 7566321
  have htrace : WordTrace (prefixWord ++ tailWord_7566321) baseStart_7566321 baseEnd_7566321 := by
    simpa [prefixWord, tailWord_7566321, baseEnd_7566321] using wordTrace_append hprefix tailTrace_7566321
  have hstable : (prefixWord ++ tailWord_7566321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566321).length < 2 ^ (prefixWord ++ tailWord_7566321).sum := by decide
  have hdescent : baseEnd_7566321 < baseStart_7566321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566348 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_7566348 : Nat := 118140960795 + 7566348 * 2 ^ 59
def prefixEnd_7566348 : Nat := 4983230072969 + 3 ^ 40 * 7566348 * 2
def baseEnd_7566348 : Nat := 3885173323185267862353005

theorem tailTrace_7566348 : CollatzResearch.WordTrace tailWord_7566348 prefixEnd_7566348 3885173323185267862353005 := by
  unfold tailWord_7566348
  simp only [CollatzResearch.WordTrace]
  refine ⟨137983691596210450101937849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183978255461613933469250465 137983691596210450101937849)
  ·
    refine ⟨103487768697157837576453387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137983691596210450101937849 103487768697157837576453387)
    ·
      refine ⟨155231653045736756364680081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103487768697157837576453387 155231653045736756364680081)
      ·
        refine ⟨116423739784302567273510061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155231653045736756364680081 116423739784302567273510061)
        ·
          refine ⟨43658902419113462727566273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116423739784302567273510061 43658902419113462727566273)
          ·
            refine ⟨32744176814335097045674705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43658902419113462727566273 32744176814335097045674705)
            ·
              refine ⟨24558132610751322784256029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32744176814335097045674705 24558132610751322784256029)
              ·
                refine ⟨9209299729031746044096011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24558132610751322784256029 9209299729031746044096011)
                ·
                  refine ⟨13813949593547619066144017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209299729031746044096011 13813949593547619066144017)
                  ·
                    refine ⟨10360462195160714299608013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13813949593547619066144017 10360462195160714299608013)
                    ·
                      refine ⟨3885173323185267862353005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360462195160714299608013 3885173323185267862353005)
                      ·
                        rfl

theorem cell23_7566348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_7566348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566348 prefixEnd_7566348 := by exact prefixLift 7566348
  have htrace : WordTrace (prefixWord ++ tailWord_7566348) baseStart_7566348 baseEnd_7566348 := by
    simpa [prefixWord, tailWord_7566348, baseEnd_7566348] using wordTrace_append hprefix tailTrace_7566348
  have hstable : (prefixWord ++ tailWord_7566348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566348).length < 2 ^ (prefixWord ++ tailWord_7566348).sum := by decide
  have hdescent : baseEnd_7566348 < baseStart_7566348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566368 : List Nat := [2, 1, 1, 7, 1, 1, 2, 8]
def baseStart_7566368 : Nat := 118140960795 + 7566368 * 2 ^ 59
def prefixEnd_7566368 : Nat := 4983230072969 + 3 ^ 40 * 7566368 * 2
def baseEnd_7566368 : Nat := 143895688622161399411219

theorem tailTrace_7566368 : CollatzResearch.WordTrace tailWord_7566368 prefixEnd_7566368 143895688622161399411219 := by
  unfold tailWord_7566368
  simp only [CollatzResearch.WordTrace]
  refine ⟨137984056326174221809801879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183978741768232295746402505 137984056326174221809801879)
  ·
    refine ⟨206976084489261332714702819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137984056326174221809801879 206976084489261332714702819)
    ·
      refine ⟨310464126733891999072054229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206976084489261332714702819 310464126733891999072054229)
      ·
        refine ⟨7276502970325593728251271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 310464126733891999072054229 7276502970325593728251271)
        ·
          refine ⟨10914754455488390592376907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276502970325593728251271 10914754455488390592376907)
          ·
            refine ⟨16372131683232585888565361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10914754455488390592376907 16372131683232585888565361)
            ·
              refine ⟨12279098762424439416424021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16372131683232585888565361 12279098762424439416424021)
              ·
                refine ⟨143895688622161399411219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12279098762424439416424021 143895688622161399411219)
                ·
                  rfl

theorem cell23_7566368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 8].length) (baseStart_7566368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566368 prefixEnd_7566368 := by exact prefixLift 7566368
  have htrace : WordTrace (prefixWord ++ tailWord_7566368) baseStart_7566368 baseEnd_7566368 := by
    simpa [prefixWord, tailWord_7566368, baseEnd_7566368] using wordTrace_append hprefix tailTrace_7566368
  have hstable : (prefixWord ++ tailWord_7566368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566368).length < 2 ^ (prefixWord ++ tailWord_7566368).sum := by decide
  have hdescent : baseEnd_7566368 < baseStart_7566368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566372 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_7566372 : Nat := 118140960795 + 7566372 * 2 ^ 59
def prefixEnd_7566372 : Nat := 4983230072969 + 3 ^ 40 * 7566372 * 2
def baseEnd_7566372 : Nat := 1295061882240325256150965

theorem tailTrace_7566372 : CollatzResearch.WordTrace tailWord_7566372 prefixEnd_7566372 1295061882240325256150965 := by
  unfold tailWord_7566372
  simp only [CollatzResearch.WordTrace]
  refine ⟨137984129272166976151374685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183978839029555968201832913 137984129272166976151374685)
  ·
    refine ⟨51744048477062616056765507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137984129272166976151374685 51744048477062616056765507)
    ·
      refine ⟨77616072715593924085148261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51744048477062616056765507 77616072715593924085148261)
      ·
        refine ⟨14553013634173860765965299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77616072715593924085148261 14553013634173860765965299)
        ·
          refine ⟨21829520451260791148947949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14553013634173860765965299 21829520451260791148947949)
          ·
            refine ⟨8186070169222796680855481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21829520451260791148947949 8186070169222796680855481)
            ·
              refine ⟨6139552626917097510641611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186070169222796680855481 6139552626917097510641611)
              ·
                refine ⟨9209328940375646265962417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139552626917097510641611 9209328940375646265962417)
                ·
                  refine ⟨6906996705281734699471813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9209328940375646265962417 6906996705281734699471813)
                  ·
                    refine ⟨1295061882240325256150965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6906996705281734699471813 1295061882240325256150965)
                    ·
                      rfl

theorem cell23_7566372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_7566372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566372 prefixEnd_7566372 := by exact prefixLift 7566372
  have htrace : WordTrace (prefixWord ++ tailWord_7566372) baseStart_7566372 baseEnd_7566372 := by
    simpa [prefixWord, tailWord_7566372, baseEnd_7566372] using wordTrace_append hprefix tailTrace_7566372
  have hstable : (prefixWord ++ tailWord_7566372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566372).length < 2 ^ (prefixWord ++ tailWord_7566372).sum := by decide
  have hdescent : baseEnd_7566372 < baseStart_7566372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566421 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_7566421 : Nat := 118140960795 + 7566421 * 2 ^ 59
def prefixEnd_7566421 : Nat := 4983230072969 + 3 ^ 40 * 7566421 * 2
def baseEnd_7566421 : Nat := 3885210807273046076740169

theorem tailTrace_7566421 : CollatzResearch.WordTrace tailWord_7566421 prefixEnd_7566421 3885210807273046076740169 := by
  unfold tailWord_7566421
  simp only [CollatzResearch.WordTrace]
  refine ⟨275970045721156433671283117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183980030480770955780855411 275970045721156433671283117)
  ·
    refine ⟨103488767145433662626731169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275970045721156433671283117 103488767145433662626731169)
    ·
      refine ⟨77616575359075246970048377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103488767145433662626731169 77616575359075246970048377)
      ·
        refine ⟨58212431519306435227536283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77616575359075246970048377 58212431519306435227536283)
        ·
          refine ⟨87318647278959652841304425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58212431519306435227536283 87318647278959652841304425)
          ·
            refine ⟨65488985459219739630978319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87318647278959652841304425 65488985459219739630978319)
            ·
              refine ⟨98233478188829609446467479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65488985459219739630978319 98233478188829609446467479)
              ·
                refine ⟨147350217283244414169701219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98233478188829609446467479 147350217283244414169701219)
                ·
                  refine ⟨221025325924866621254551829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147350217283244414169701219 221025325924866621254551829)
                  ·
                    refine ⟨10360562152728122871307117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221025325924866621254551829 10360562152728122871307117)
                    ·
                      refine ⟨3885210807273046076740169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360562152728122871307117 3885210807273046076740169)
                      ·
                        rfl

theorem cell23_7566421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_7566421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566421 prefixEnd_7566421 := by exact prefixLift 7566421
  have htrace : WordTrace (prefixWord ++ tailWord_7566421) baseStart_7566421 baseEnd_7566421 := by
    simpa [prefixWord, tailWord_7566421, baseEnd_7566421] using wordTrace_append hprefix tailTrace_7566421
  have hstable : (prefixWord ++ tailWord_7566421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566421).length < 2 ^ (prefixWord ++ tailWord_7566421).sum := by decide
  have hdescent : baseEnd_7566421 < baseStart_7566421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566431 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_7566431 : Nat := 118140960795 + 7566431 * 2 ^ 59
def prefixEnd_7566431 : Nat := 4983230072969 + 3 ^ 40 * 7566431 * 2
def baseEnd_7566431 : Nat := 3885215942079591037615123

theorem tailTrace_7566431 : CollatzResearch.WordTrace tailWord_7566431 prefixEnd_7566431 3885215942079591037615123 := by
  unfold tailWord_7566431
  simp only [CollatzResearch.WordTrace]
  refine ⟨275970410451120205379147147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183980273634080136919431431 275970410451120205379147147)
  ·
    refine ⟨413955615676680308068720721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275970410451120205379147147 413955615676680308068720721)
    ·
      refine ⟨310466711757510231051540541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413955615676680308068720721 310466711757510231051540541)
      ·
        refine ⟨116425016909066336644327703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310466711757510231051540541 116425016909066336644327703)
        ·
          refine ⟨174637525363599504966491555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116425016909066336644327703 174637525363599504966491555)
          ·
            refine ⟨261956288045399257449737333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174637525363599504966491555 261956288045399257449737333)
            ·
              refine ⟨24558402004256180385912875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261956288045399257449737333 24558402004256180385912875)
              ·
                refine ⟨36837603006384270578869313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24558402004256180385912875 36837603006384270578869313)
                ·
                  refine ⟨27628202254788202934151985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36837603006384270578869313 27628202254788202934151985)
                  ·
                    refine ⟨20721151691091152200613989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27628202254788202934151985 20721151691091152200613989)
                    ·
                      refine ⟨3885215942079591037615123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20721151691091152200613989 3885215942079591037615123)
                      ·
                        rfl

theorem cell23_7566431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_7566431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566431 prefixEnd_7566431 := by exact prefixLift 7566431
  have htrace : WordTrace (prefixWord ++ tailWord_7566431) baseStart_7566431 baseEnd_7566431 := by
    simpa [prefixWord, tailWord_7566431, baseEnd_7566431] using wordTrace_append hprefix tailTrace_7566431
  have hstable : (prefixWord ++ tailWord_7566431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566431).length < 2 ^ (prefixWord ++ tailWord_7566431).sum := by decide
  have hdescent : baseEnd_7566431 < baseStart_7566431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566441 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 7]
def baseStart_7566441 : Nat := 118140960795 + 7566441 * 2 ^ 59
def prefixEnd_7566441 : Nat := 4983230072969 + 3 ^ 40 * 7566441 * 2
def baseEnd_7566441 : Nat := 431691230765126222054453

theorem tailTrace_7566441 : CollatzResearch.WordTrace tailWord_7566441 prefixEnd_7566441 431691230765126222054453 := by
  unfold tailWord_7566441
  simp only [CollatzResearch.WordTrace]
  refine ⟨275970775181083977087011177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183980516787389318058007451 275970775181083977087011177)
  ·
    refine ⟨206978081385812982815258383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275970775181083977087011177 206978081385812982815258383)
    ·
      refine ⟨310467122078719474222887575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206978081385812982815258383 310467122078719474222887575)
      ·
        refine ⟨465700683118079211334331363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310467122078719474222887575 465700683118079211334331363)
        ·
          refine ⟨698551024677118817001497045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465700683118079211334331363 698551024677118817001497045)
          ·
            refine ⟨16372289640869972273472587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 698551024677118817001497045 16372289640869972273472587)
            ·
              refine ⟨24558434461304958410208881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16372289640869972273472587 24558434461304958410208881)
              ·
                refine ⟨18418825845978718807656661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24558434461304958410208881 18418825845978718807656661)
                ·
                  refine ⟨431691230765126222054453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18418825845978718807656661 431691230765126222054453)
                  ·
                    rfl

theorem cell23_7566441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_7566441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566441 prefixEnd_7566441 := by exact prefixLift 7566441
  have htrace : WordTrace (prefixWord ++ tailWord_7566441) baseStart_7566441 baseEnd_7566441 := by
    simpa [prefixWord, tailWord_7566441, baseEnd_7566441] using wordTrace_append hprefix tailTrace_7566441
  have hstable : (prefixWord ++ tailWord_7566441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566441).length < 2 ^ (prefixWord ++ tailWord_7566441).sum := by decide
  have hdescent : baseEnd_7566441 < baseStart_7566441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566468 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_7566468 : Nat := 118140960795 + 7566468 * 2 ^ 59
def prefixEnd_7566468 : Nat := 4983230072969 + 3 ^ 40 * 7566468 * 2
def baseEnd_7566468 : Nat := 3885234940863807392852453

theorem tailTrace_7566468 : CollatzResearch.WordTrace tailWord_7566468 prefixEnd_7566468 3885234940863807392852453 := by
  unfold tailWord_7566468
  simp only [CollatzResearch.WordTrace]
  refine ⟨137985879975993080349122029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183981173301324107132162705 137985879975993080349122029)
  ·
    refine ⟨51744704990997405130920761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137985879975993080349122029 51744704990997405130920761)
    ·
      refine ⟨38808528743248053848190571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51744704990997405130920761 38808528743248053848190571)
      ·
        refine ⟨58212793114872080772285857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38808528743248053848190571 58212793114872080772285857)
        ·
          refine ⟨43659594836154060579214393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58212793114872080772285857 43659594836154060579214393)
          ·
            refine ⟨32744696127115545434410795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43659594836154060579214393 32744696127115545434410795)
            ·
              refine ⟨49117044190673318151616193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32744696127115545434410795 49117044190673318151616193)
              ·
                refine ⟨36837783143004988613712145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49117044190673318151616193 36837783143004988613712145)
                ·
                  refine ⟨27628337357253741460284109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36837783143004988613712145 27628337357253741460284109)
                  ·
                    refine ⟨10360626508970153047606541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27628337357253741460284109 10360626508970153047606541)
                    ·
                      refine ⟨3885234940863807392852453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360626508970153047606541 3885234940863807392852453)
                      ·
                        rfl

theorem cell23_7566468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_7566468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566468 prefixEnd_7566468 := by exact prefixLift 7566468
  have htrace : WordTrace (prefixWord ++ tailWord_7566468) baseStart_7566468 baseEnd_7566468 := by
    simpa [prefixWord, tailWord_7566468, baseEnd_7566468] using wordTrace_append hprefix tailTrace_7566468
  have hstable : (prefixWord ++ tailWord_7566468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566468).length < 2 ^ (prefixWord ++ tailWord_7566468).sum := by decide
  have hdescent : baseEnd_7566468 < baseStart_7566468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566469 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 2, 2, 2]
def baseStart_7566469 : Nat := 118140960795 + 7566469 * 2 ^ 59
def prefixEnd_7566469 : Nat := 4983230072969 + 3 ^ 40 * 7566469 * 2
def baseEnd_7566469 : Nat := 3885235454344461888939949

theorem tailTrace_7566469 : CollatzResearch.WordTrace tailWord_7566469 prefixEnd_7566469 3885235454344461888939949 := by
  unfold tailWord_7566469
  simp only [CollatzResearch.WordTrace]
  refine ⟨275971796424982537869030461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183981197616655025246020307 275971796424982537869030461)
  ·
    refine ⟨103489423659368451700886423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275971796424982537869030461 103489423659368451700886423)
    ·
      refine ⟨155234135489052677551329635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103489423659368451700886423 155234135489052677551329635)
      ·
        refine ⟨232851203233579016326994453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155234135489052677551329635 232851203233579016326994453)
        ·
          refine ⟨10914900151574016390327865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232851203233579016326994453 10914900151574016390327865)
          ·
            refine ⟨8186175113680512292745899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10914900151574016390327865 8186175113680512292745899)
            ·
              refine ⟨12279262670520768439118849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8186175113680512292745899 12279262670520768439118849)
              ·
                refine ⟨9209447002890576329339137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12279262670520768439118849 9209447002890576329339137)
                ·
                  refine ⟨6907085252167932247004353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9209447002890576329339137 6907085252167932247004353)
                  ·
                    refine ⟨5180313939125949185253265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6907085252167932247004353 5180313939125949185253265)
                    ·
                      refine ⟨3885235454344461888939949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180313939125949185253265 3885235454344461888939949)
                      ·
                        rfl

theorem cell23_7566469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_7566469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566469 prefixEnd_7566469 := by exact prefixLift 7566469
  have htrace : WordTrace (prefixWord ++ tailWord_7566469) baseStart_7566469 baseEnd_7566469 := by
    simpa [prefixWord, tailWord_7566469, baseEnd_7566469] using wordTrace_append hprefix tailTrace_7566469
  have hstable : (prefixWord ++ tailWord_7566469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566469).length < 2 ^ (prefixWord ++ tailWord_7566469).sum := by decide
  have hdescent : baseEnd_7566469 < baseStart_7566469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566471 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 4, 5]
def baseStart_7566471 : Nat := 118140960795 + 7566471 * 2 ^ 59
def prefixEnd_7566471 : Nat := 4983230072969 + 3 ^ 40 * 7566471 * 2
def baseEnd_7566471 : Nat := 1295078827101923627038313

theorem tailTrace_7566471 : CollatzResearch.WordTrace tailWord_7566471 prefixEnd_7566471 1295078827101923627038313 := by
  unfold tailWord_7566471
  simp only [CollatzResearch.WordTrace]
  refine ⟨275971869370975292210603267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183981246247316861473735511 275971869370975292210603267)
  ·
    refine ⟨413957804056462938315904901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275971869370975292210603267 413957804056462938315904901)
    ·
      refine ⟨77617088260586800934232169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413957804056462938315904901 77617088260586800934232169)
      ·
        refine ⟨58212816195440100700674127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77617088260586800934232169 58212816195440100700674127)
        ·
          refine ⟨87319224293160151051011191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58212816195440100700674127 87319224293160151051011191)
          ·
            refine ⟨130978836439740226576516787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87319224293160151051011191 130978836439740226576516787)
            ·
              refine ⟨196468254659610339864775181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130978836439740226576516787 196468254659610339864775181)
              ·
                refine ⟨73675595497353877449290693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196468254659610339864775181 73675595497353877449290693)
                ·
                  refine ⟨13814174155753852021742005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73675595497353877449290693 13814174155753852021742005)
                  ·
                    refine ⟨1295078827101923627038313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13814174155753852021742005 1295078827101923627038313)
                    ·
                      rfl

theorem cell23_7566471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_7566471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566471 prefixEnd_7566471 := by exact prefixLift 7566471
  have htrace : WordTrace (prefixWord ++ tailWord_7566471) baseStart_7566471 baseEnd_7566471 := by
    simpa [prefixWord, tailWord_7566471, baseEnd_7566471] using wordTrace_append hprefix tailTrace_7566471
  have hstable : (prefixWord ++ tailWord_7566471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566471).length < 2 ^ (prefixWord ++ tailWord_7566471).sum := by decide
  have hdescent : baseEnd_7566471 < baseStart_7566471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566508 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 4, 4, 2]
def baseStart_7566508 : Nat := 118140960795 + 7566508 * 2 ^ 59
def prefixEnd_7566508 : Nat := 4983230072969 + 3 ^ 40 * 7566508 * 2
def baseEnd_7566508 : Nat := 3885255480089987236352269

theorem tailTrace_7566508 : CollatzResearch.WordTrace tailWord_7566508 prefixEnd_7566508 3885255480089987236352269 := by
  unfold tailWord_7566508
  simp only [CollatzResearch.WordTrace]
  refine ⟨137986609435920623764850089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183982145914560831686466785 137986609435920623764850089)
  ·
    refine ⟨103489957076940467823637567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137986609435920623764850089 103489957076940467823637567)
    ·
      refine ⟨155234935615410701735456351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103489957076940467823637567 155234935615410701735456351)
      ·
        refine ⟨232852403423116052603184527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155234935615410701735456351 232852403423116052603184527)
        ·
          refine ⟨349278605134674078904776791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232852403423116052603184527 349278605134674078904776791)
          ·
            refine ⟨523917907702011118357165187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349278605134674078904776791 523917907702011118357165187)
            ·
              refine ⟨785876861553016677535747781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523917907702011118357165187 785876861553016677535747781)
              ·
                refine ⟨147351911541190627037952709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785876861553016677535747781 147351911541190627037952709)
                ·
                  refine ⟨27628483413973242569616133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147351911541190627037952709 27628483413973242569616133)
                  ·
                    refine ⟨5180340640119982981803025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27628483413973242569616133 5180340640119982981803025)
                    ·
                      refine ⟨3885255480089987236352269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180340640119982981803025 3885255480089987236352269)
                      ·
                        rfl

theorem cell23_7566508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_7566508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566508 prefixEnd_7566508 := by exact prefixLift 7566508
  have htrace : WordTrace (prefixWord ++ tailWord_7566508) baseStart_7566508 baseEnd_7566508 := by
    simpa [prefixWord, tailWord_7566508, baseEnd_7566508] using wordTrace_append hprefix tailTrace_7566508
  have hstable : (prefixWord ++ tailWord_7566508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566508).length < 2 ^ (prefixWord ++ tailWord_7566508).sum := by decide
  have hdescent : baseEnd_7566508 < baseStart_7566508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566509 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 5]
def baseStart_7566509 : Nat := 118140960795 + 7566509 * 2 ^ 59
def prefixEnd_7566509 : Nat := 4983230072969 + 3 ^ 40 * 7566509 * 2
def baseEnd_7566509 : Nat := 431695110396737970271085

theorem tailTrace_7566509 : CollatzResearch.WordTrace tailWord_7566509 prefixEnd_7566509 431695110396737970271085 := by
  unfold tailWord_7566509
  simp only [CollatzResearch.WordTrace]
  refine ⟨275973255344837624700486581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183982170229891749800324387 275973255344837624700486581)
  ·
    refine ⟨25872492688578527315670617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275973255344837624700486581 25872492688578527315670617)
    ·
      refine ⟨19404369516433895486752963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25872492688578527315670617 19404369516433895486752963)
      ·
        refine ⟨29106554274650843230129445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19404369516433895486752963 29106554274650843230129445)
        ·
          refine ⟨5457478926497033105649271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29106554274650843230129445 5457478926497033105649271)
          ·
            refine ⟨8186218389745549658473907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457478926497033105649271 8186218389745549658473907)
            ·
              refine ⟨12279327584618324487710861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8186218389745549658473907 12279327584618324487710861)
              ·
                refine ⟨4604747844231871682891573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12279327584618324487710861 4604747844231871682891573)
                ·
                  refine ⟨431695110396737970271085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604747844231871682891573 431695110396737970271085)
                  ·
                    rfl

theorem cell23_7566509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_7566509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566509 prefixEnd_7566509 := by exact prefixLift 7566509
  have htrace : WordTrace (prefixWord ++ tailWord_7566509) baseStart_7566509 baseEnd_7566509 := by
    simpa [prefixWord, tailWord_7566509, baseEnd_7566509] using wordTrace_append hprefix tailTrace_7566509
  have hstable : (prefixWord ++ tailWord_7566509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566509).length < 2 ^ (prefixWord ++ tailWord_7566509).sum := by decide
  have hdescent : baseEnd_7566509 < baseStart_7566509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566535 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 1, 4]
def baseStart_7566535 : Nat := 118140960795 + 7566535 * 2 ^ 59
def prefixEnd_7566535 : Nat := 4983230072969 + 3 ^ 40 * 7566535 * 2
def baseEnd_7566535 : Nat := 1295089781355886210238215

theorem tailTrace_7566535 : CollatzResearch.WordTrace tailWord_7566535 prefixEnd_7566535 1295089781355886210238215 := by
  unfold tailWord_7566535
  simp only [CollatzResearch.WordTrace]
  refine ⟨275974203642743431140933059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183982802428495620760622039 275974203642743431140933059)
  ·
    refine ⟨413961305464115146711399589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275974203642743431140933059 413961305464115146711399589)
    ·
      refine ⟨77617744774521590008387423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413961305464115146711399589 77617744774521590008387423)
      ·
        refine ⟨116426617161782385012581135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77617744774521590008387423 116426617161782385012581135)
        ·
          refine ⟨174639925742673577518871703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116426617161782385012581135 174639925742673577518871703)
          ·
            refine ⟨261959888614010366278307555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174639925742673577518871703 261959888614010366278307555)
            ·
              refine ⟨392939832921015549417461333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261959888614010366278307555 392939832921015549417461333)
              ·
                refine ⟨4604763667043150969735875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 392939832921015549417461333 4604763667043150969735875)
                ·
                  refine ⟨6907145500564726454603813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604763667043150969735875 6907145500564726454603813)
                  ·
                    refine ⟨1295089781355886210238215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907145500564726454603813 1295089781355886210238215)
                    ·
                      rfl

theorem cell23_7566535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_7566535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566535 prefixEnd_7566535 := by exact prefixLift 7566535
  have htrace : WordTrace (prefixWord ++ tailWord_7566535) baseStart_7566535 baseEnd_7566535 := by
    simpa [prefixWord, tailWord_7566535, baseEnd_7566535] using wordTrace_append hprefix tailTrace_7566535
  have hstable : (prefixWord ++ tailWord_7566535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566535).length < 2 ^ (prefixWord ++ tailWord_7566535).sum := by decide
  have hdescent : baseEnd_7566535 < baseStart_7566535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566551 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_7566551 : Nat := 118140960795 + 7566551 * 2 ^ 59
def prefixEnd_7566551 : Nat := 4983230072969 + 3 ^ 40 * 7566551 * 2
def baseEnd_7566551 : Nat := 3885277559758130568114571

theorem tailTrace_7566551 : CollatzResearch.WordTrace tailWord_7566551 prefixEnd_7566551 3885277559758130568114571 := by
  unfold tailWord_7566551
  simp only [CollatzResearch.WordTrace]
  refine ⟨275974787210685465873515507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183983191473790310582343671 275974787210685465873515507)
  ·
    refine ⟨413962180816028198810273261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275974787210685465873515507 413962180816028198810273261)
    ·
      refine ⟨155235817806010574553852473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413962180816028198810273261 155235817806010574553852473)
      ·
        refine ⟨116426863354507930915389355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155235817806010574553852473 116426863354507930915389355)
        ·
          refine ⟨174640295031761896373084033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116426863354507930915389355 174640295031761896373084033)
          ·
            refine ⟨130980221273821422279813025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174640295031761896373084033 130980221273821422279813025)
            ·
              refine ⟨98235165955366066709859769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130980221273821422279813025 98235165955366066709859769)
              ·
                refine ⟨73676374466524550032394827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98235165955366066709859769 73676374466524550032394827)
                ·
                  refine ⟨110514561699786825048592241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73676374466524550032394827 110514561699786825048592241)
                  ·
                    refine ⟨82885921274840118786444181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110514561699786825048592241 82885921274840118786444181)
                    ·
                      refine ⟨3885277559758130568114571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82885921274840118786444181 3885277559758130568114571)
                      ·
                        rfl

theorem cell23_7566551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_7566551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566551 prefixEnd_7566551 := by exact prefixLift 7566551
  have htrace : WordTrace (prefixWord ++ tailWord_7566551) baseStart_7566551 baseEnd_7566551 := by
    simpa [prefixWord, tailWord_7566551, baseEnd_7566551] using wordTrace_append hprefix tailTrace_7566551
  have hstable : (prefixWord ++ tailWord_7566551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566551).length < 2 ^ (prefixWord ++ tailWord_7566551).sum := by decide
  have hdescent : baseEnd_7566551 < baseStart_7566551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566585 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 2, 3, 2]
def baseStart_7566585 : Nat := 118140960795 + 7566585 * 2 ^ 59
def prefixEnd_7566585 : Nat := 4983230072969 + 3 ^ 40 * 7566585 * 2
def baseEnd_7566585 : Nat := 3885295018100383435089415

theorem tailTrace_7566585 : CollatzResearch.WordTrace tailWord_7566585 prefixEnd_7566585 3885295018100383435089415 := by
  unfold tailWord_7566585
  simp only [CollatzResearch.WordTrace]
  refine ⟨275976027292562289680253209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183984018195041526453502139 275976027292562289680253209)
  ·
    refine ⟨206982020469421717260189907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275976027292562289680253209 206982020469421717260189907)
    ·
      refine ⟨310473030704132575890284861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206982020469421717260189907 310473030704132575890284861)
      ·
        refine ⟨116427386514049715958856823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310473030704132575890284861 116427386514049715958856823)
        ·
          refine ⟨174641079771074573938285235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116427386514049715958856823 174641079771074573938285235)
          ·
            refine ⟨261961619656611860907427853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174641079771074573938285235 261961619656611860907427853)
            ·
              refine ⟨98235607371229447840285445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261961619656611860907427853 98235607371229447840285445)
              ·
                refine ⟨18419176382105521470053521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98235607371229447840285445 18419176382105521470053521)
                ·
                  refine ⟨13814382286579141102540141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18419176382105521470053521 13814382286579141102540141)
                  ·
                    refine ⟨5180393357467177913452553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13814382286579141102540141 5180393357467177913452553)
                    ·
                      refine ⟨3885295018100383435089415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180393357467177913452553 3885295018100383435089415)
                      ·
                        rfl

theorem cell23_7566585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_7566585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566585 prefixEnd_7566585 := by exact prefixLift 7566585
  have htrace : WordTrace (prefixWord ++ tailWord_7566585) baseStart_7566585 baseEnd_7566585 := by
    simpa [prefixWord, tailWord_7566585, baseEnd_7566585] using wordTrace_append hprefix tailTrace_7566585
  have hstable : (prefixWord ++ tailWord_7566585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566585).length < 2 ^ (prefixWord ++ tailWord_7566585).sum := by decide
  have hdescent : baseEnd_7566585 < baseStart_7566585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566615 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_7566615 : Nat := 118140960795 + 7566615 * 2 ^ 59
def prefixEnd_7566615 : Nat := 4983230072969 + 3 ^ 40 * 7566615 * 2
def baseEnd_7566615 : Nat := 3885310422520018317714277

theorem tailTrace_7566615 : CollatzResearch.WordTrace tailWord_7566615 prefixEnd_7566615 3885310422520018317714277 := by
  unfold tailWord_7566615
  simp only [CollatzResearch.WordTrace]
  refine ⟨275977121482453604803845299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183984747654969069869230199 275977121482453604803845299)
  ·
    refine ⟨413965682223680407205767949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275977121482453604803845299 413965682223680407205767949)
    ·
      refine ⟨155237130833880152702162981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413965682223680407205767949 155237130833880152702162981)
      ·
        refine ⟨29106962031352528631655559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155237130833880152702162981 29106962031352528631655559)
        ·
          refine ⟨43660443047028792947483339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29106962031352528631655559 43660443047028792947483339)
          ·
            refine ⟨65490664570543189421225009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43660443047028792947483339 65490664570543189421225009)
            ·
              refine ⟨49117998427907392065918757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65490664570543189421225009 49117998427907392065918757)
              ·
                refine ⟨9209624705232636012359767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49117998427907392065918757 9209624705232636012359767)
                ·
                  refine ⟨13814437057848954018539651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209624705232636012359767 13814437057848954018539651)
                  ·
                    refine ⟨20721655586773431027809477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13814437057848954018539651 20721655586773431027809477)
                    ·
                      refine ⟨3885310422520018317714277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20721655586773431027809477 3885310422520018317714277)
                      ·
                        rfl

theorem cell23_7566615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_7566615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566615 prefixEnd_7566615 := by exact prefixLift 7566615
  have htrace : WordTrace (prefixWord ++ tailWord_7566615) baseStart_7566615 baseEnd_7566615 := by
    simpa [prefixWord, tailWord_7566615, baseEnd_7566615] using wordTrace_append hprefix tailTrace_7566615
  have hstable : (prefixWord ++ tailWord_7566615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566615).length < 2 ^ (prefixWord ++ tailWord_7566615).sum := by decide
  have hdescent : baseEnd_7566615 < baseStart_7566615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566626 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_7566626 : Nat := 118140960795 + 7566626 * 2 ^ 59
def prefixEnd_7566626 : Nat := 4983230072969 + 3 ^ 40 * 7566626 * 2
def baseEnd_7566626 : Nat := 3885316070807217774676727

theorem tailTrace_7566626 : CollatzResearch.WordTrace tailWord_7566626 prefixEnd_7566626 3885316070807217774676727 := by
  unfold tailWord_7566626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68994380671353438420623933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183985015123609169121663821 68994380671353438420623933)
  ·
    refine ⟨25872892751757539407733975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68994380671353438420623933 25872892751757539407733975)
    ·
      refine ⟨38809339127636309111600963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25872892751757539407733975 38809339127636309111600963)
      ·
        refine ⟨58214008691454463667401445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38809339127636309111600963 58214008691454463667401445)
        ·
          refine ⟨10915126629647711937637771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58214008691454463667401445 10915126629647711937637771)
          ·
            refine ⟨16372689944471567906456657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10915126629647711937637771 16372689944471567906456657)
            ·
              refine ⟨12279517458353675929842493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16372689944471567906456657 12279517458353675929842493)
              ·
                refine ⟨4604819046882628473690935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12279517458353675929842493 4604819046882628473690935)
                ·
                  refine ⟨6907228570323942710536403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604819046882628473690935 6907228570323942710536403)
                  ·
                    refine ⟨10360842855485914065804605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907228570323942710536403 10360842855485914065804605)
                    ·
                      refine ⟨3885316070807217774676727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360842855485914065804605 3885316070807217774676727)
                      ·
                        rfl

theorem cell23_7566626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_7566626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566626 prefixEnd_7566626 := by exact prefixLift 7566626
  have htrace : WordTrace (prefixWord ++ tailWord_7566626) baseStart_7566626 baseEnd_7566626 := by
    simpa [prefixWord, tailWord_7566626, baseEnd_7566626] using wordTrace_append hprefix tailTrace_7566626
  have hstable : (prefixWord ++ tailWord_7566626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566626).length < 2 ^ (prefixWord ++ tailWord_7566626).sum := by decide
  have hdescent : baseEnd_7566626 < baseStart_7566626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566632 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_7566632 : Nat := 118140960795 + 7566632 * 2 ^ 59
def prefixEnd_7566632 : Nat := 4983230072969 + 3 ^ 40 * 7566632 * 2
def baseEnd_7566632 : Nat := 3885319151691144751201699

theorem tailTrace_7566632 : CollatzResearch.WordTrace tailWord_7566632 prefixEnd_7566632 3885319151691144751201699 := by
  unfold tailWord_7566632
  simp only [CollatzResearch.WordTrace]
  refine ⟨137988870761696008353607075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183985161015594677804809433 137988870761696008353607075)
  ·
    refine ⟨206983306142544012530410613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137988870761696008353607075 206983306142544012530410613)
    ·
      refine ⟨19404684950863501174725995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206983306142544012530410613 19404684950863501174725995)
      ·
        refine ⟨29107027426295251762088993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19404684950863501174725995 29107027426295251762088993)
        ·
          refine ⟨21830270569721438821566745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29107027426295251762088993 21830270569721438821566745)
          ·
            refine ⟨16372702927291079116175059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21830270569721438821566745 16372702927291079116175059)
            ·
              refine ⟨24559054390936618674262589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16372702927291079116175059 24559054390936618674262589)
              ·
                refine ⟨9209645396601232002848471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24559054390936618674262589 9209645396601232002848471)
                ·
                  refine ⟨13814468094901848004272707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209645396601232002848471 13814468094901848004272707)
                  ·
                    refine ⟨20721702142352772006409061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13814468094901848004272707 20721702142352772006409061)
                    ·
                      refine ⟨3885319151691144751201699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20721702142352772006409061 3885319151691144751201699)
                      ·
                        rfl

theorem cell23_7566632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_7566632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566632 prefixEnd_7566632 := by exact prefixLift 7566632
  have htrace : WordTrace (prefixWord ++ tailWord_7566632) baseStart_7566632 baseEnd_7566632 := by
    simpa [prefixWord, tailWord_7566632, baseEnd_7566632] using wordTrace_append hprefix tailTrace_7566632
  have hstable : (prefixWord ++ tailWord_7566632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566632).length < 2 ^ (prefixWord ++ tailWord_7566632).sum := by decide
  have hdescent : baseEnd_7566632 < baseStart_7566632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566642 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_7566642 : Nat := 118140960795 + 7566642 * 2 ^ 59
def prefixEnd_7566642 : Nat := 4983230072969 + 3 ^ 40 * 7566642 * 2
def baseEnd_7566642 : Nat := 1295108095499229904025551

theorem tailTrace_7566642 : CollatzResearch.WordTrace tailWord_7566642 prefixEnd_7566642 1295108095499229904025551 := by
  unfold tailWord_7566642
  simp only [CollatzResearch.WordTrace]
  refine ⟨68994526563338947103769545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183985404168903858943385453 68994526563338947103769545)
  ·
    refine ⟨51745894922504210327827159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68994526563338947103769545 51745894922504210327827159)
    ·
      refine ⟨77618842383756315491740739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51745894922504210327827159 77618842383756315491740739)
      ·
        refine ⟨116428263575634473237611109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77618842383756315491740739 116428263575634473237611109)
        ·
          refine ⟨21830299420431463732052083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116428263575634473237611109 21830299420431463732052083)
          ·
            refine ⟨32745449130647195598078125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21830299420431463732052083 32745449130647195598078125)
            ·
              refine ⟨12279543423992698349279297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32745449130647195598078125 12279543423992698349279297)
              ·
                refine ⟨9209657567994523761959473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12279543423992698349279297 9209657567994523761959473)
                ·
                  refine ⟨6907243175995892821469605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9209657567994523761959473 6907243175995892821469605)
                  ·
                    refine ⟨1295108095499229904025551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907243175995892821469605 1295108095499229904025551)
                    ·
                      rfl

theorem cell23_7566642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_7566642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566642 prefixEnd_7566642 := by exact prefixLift 7566642
  have htrace : WordTrace (prefixWord ++ tailWord_7566642) baseStart_7566642 baseEnd_7566642 := by
    simpa [prefixWord, tailWord_7566642, baseEnd_7566642] using wordTrace_append hprefix tailTrace_7566642
  have hstable : (prefixWord ++ tailWord_7566642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566642).length < 2 ^ (prefixWord ++ tailWord_7566642).sum := by decide
  have hdescent : baseEnd_7566642 < baseStart_7566642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566665 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_7566665 : Nat := 118140960795 + 7566665 * 2 ^ 59
def prefixEnd_7566665 : Nat := 4983230072969 + 3 ^ 40 * 7566665 * 2
def baseEnd_7566665 : Nat := 3885336096552743122089047

theorem tailTrace_7566665 : CollatzResearch.WordTrace tailWord_7566665 prefixEnd_7566665 3885336096552743122089047 := by
  unfold tailWord_7566665
  simp only [CollatzResearch.WordTrace]
  refine ⟨275978945132272463343165449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183985963421514975562110299 275978945132272463343165449)
  ·
    refine ⟨206984208849204347507374087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275978945132272463343165449 206984208849204347507374087)
    ·
      refine ⟨310476313273806521261061131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206984208849204347507374087 310476313273806521261061131)
      ·
        refine ⟨465714469910709781891591697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310476313273806521261061131 465714469910709781891591697)
        ·
          refine ⟨349285852433032336418693773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465714469910709781891591697 349285852433032336418693773)
          ·
            refine ⟨130982194662387126157010165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349285852433032336418693773 130982194662387126157010165)
            ·
              refine ⟨12279580749598793077219703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130982194662387126157010165 12279580749598793077219703)
              ·
                refine ⟨18419371124398189615829555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12279580749598793077219703 18419371124398189615829555)
                ·
                  refine ⟨27629056686597284423744333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18419371124398189615829555 27629056686597284423744333)
                  ·
                    refine ⟨10360896257473981658904125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27629056686597284423744333 10360896257473981658904125)
                    ·
                      refine ⟨3885336096552743122089047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10360896257473981658904125 3885336096552743122089047)
                      ·
                        rfl

theorem cell23_7566665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_7566665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566665 prefixEnd_7566665 := by exact prefixLift 7566665
  have htrace : WordTrace (prefixWord ++ tailWord_7566665) baseStart_7566665 baseEnd_7566665 := by
    simpa [prefixWord, tailWord_7566665, baseEnd_7566665] using wordTrace_append hprefix tailTrace_7566665
  have hstable : (prefixWord ++ tailWord_7566665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566665).length < 2 ^ (prefixWord ++ tailWord_7566665).sum := by decide
  have hdescent : baseEnd_7566665 < baseStart_7566665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566755 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 3]
def baseStart_7566755 : Nat := 118140960795 + 7566755 * 2 ^ 59
def prefixEnd_7566755 : Nat := 4983230072969 + 3 ^ 40 * 7566755 * 2
def baseEnd_7566755 : Nat := 3885382309811647769963633

theorem tailTrace_7566755 : CollatzResearch.WordTrace tailWord_7566755 prefixEnd_7566755 3885382309811647769963633 := by
  unfold tailWord_7566755
  simp only [CollatzResearch.WordTrace]
  refine ⟨275982227701946408713941719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183988151801297605809294479 275982227701946408713941719)
  ·
    refine ⟨413973341552919613070912579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275982227701946408713941719 413973341552919613070912579)
    ·
      refine ⟨620960012329379419606368869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413973341552919613070912579 620960012329379419606368869)
      ·
        refine ⟨116430002311758641176194163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 620960012329379419606368869 116430002311758641176194163)
        ·
          refine ⟨174645003467637961764291245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116430002311758641176194163 174645003467637961764291245)
          ·
            refine ⟨65491876300364235661609217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174645003467637961764291245 65491876300364235661609217)
            ·
              refine ⟨49118907225273176746206913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65491876300364235661609217 49118907225273176746206913)
              ·
                refine ⟨36839180418954882559655185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49118907225273176746206913 36839180418954882559655185)
                ·
                  refine ⟨27629385314216161919741389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36839180418954882559655185 27629385314216161919741389)
                  ·
                    refine ⟨10361019492831060719903021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27629385314216161919741389 10361019492831060719903021)
                    ·
                      refine ⟨3885382309811647769963633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361019492831060719903021 3885382309811647769963633)
                      ·
                        rfl

theorem cell23_7566755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_7566755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566755 prefixEnd_7566755 := by exact prefixLift 7566755
  have htrace : WordTrace (prefixWord ++ tailWord_7566755) baseStart_7566755 baseEnd_7566755 := by
    simpa [prefixWord, tailWord_7566755, baseEnd_7566755] using wordTrace_append hprefix tailTrace_7566755
  have hstable : (prefixWord ++ tailWord_7566755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566755).length < 2 ^ (prefixWord ++ tailWord_7566755).sum := by decide
  have hdescent : baseEnd_7566755 < baseStart_7566755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566768 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_7566768 : Nat := 118140960795 + 7566768 * 2 ^ 59
def prefixEnd_7566768 : Nat := 4983230072969 + 3 ^ 40 * 7566768 * 2
def baseEnd_7566768 : Nat := 3885388985060156219101073

theorem tailTrace_7566768 : CollatzResearch.WordTrace tailWord_7566768 prefixEnd_7566768 3885388985060156219101073 := by
  unfold tailWord_7566768
  simp only [CollatzResearch.WordTrace]
  refine ⟨137991350925449655967082479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183988467900599541289443305 137991350925449655967082479)
  ·
    refine ⟨206987026388174483950623719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137991350925449655967082479 206987026388174483950623719)
    ·
      refine ⟨310480539582261725925935579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206987026388174483950623719 310480539582261725925935579)
      ·
        refine ⟨465720809373392588888903369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310480539582261725925935579 465720809373392588888903369)
        ·
          refine ⟨349290607030044441666677527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465720809373392588888903369 349290607030044441666677527)
          ·
            refine ⟨523935910545066662500016291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349290607030044441666677527 523935910545066662500016291)
            ·
              refine ⟨785903865817599993750024437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523935910545066662500016291 785903865817599993750024437)
              ·
                refine ⟨73678487420399999414064791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 785903865817599993750024437 73678487420399999414064791)
                ·
                  refine ⟨110517731130599999121097187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73678487420399999414064791 110517731130599999121097187)
                  ·
                    refine ⟨165776596695899998681645781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110517731130599999121097187 165776596695899998681645781)
                    ·
                      refine ⟨3885388985060156219101073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165776596695899998681645781 3885388985060156219101073)
                      ·
                        rfl

theorem cell23_7566768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_7566768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566768 prefixEnd_7566768 := by exact prefixLift 7566768
  have htrace : WordTrace (prefixWord ++ tailWord_7566768) baseStart_7566768 baseEnd_7566768 := by
    simpa [prefixWord, tailWord_7566768, baseEnd_7566768] using wordTrace_append hprefix tailTrace_7566768
  have hstable : (prefixWord ++ tailWord_7566768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566768).length < 2 ^ (prefixWord ++ tailWord_7566768).sum := by decide
  have hdescent : baseEnd_7566768 < baseStart_7566768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566782 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_7566782 : Nat := 118140960795 + 7566782 * 2 ^ 59
def prefixEnd_7566782 : Nat := 4983230072969 + 3 ^ 40 * 7566782 * 2
def baseEnd_7566782 : Nat := 3885396173789319164326009

theorem tailTrace_7566782 : CollatzResearch.WordTrace tailWord_7566782 prefixEnd_7566782 3885396173789319164326009 := by
  unfold tailWord_7566782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34497901559106074040646825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183988808315232394883449733 34497901559106074040646825)
  ·
    refine ⟨25873426169329555530485119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34497901559106074040646825 25873426169329555530485119)
    ·
      refine ⟨38810139253994333295727679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25873426169329555530485119 38810139253994333295727679)
      ·
        refine ⟨58215208880991499943591519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38810139253994333295727679 58215208880991499943591519)
        ·
          refine ⟨87322813321487249915387279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58215208880991499943591519 87322813321487249915387279)
          ·
            refine ⟨130984219982230874873080919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87322813321487249915387279 130984219982230874873080919)
            ·
              refine ⟨196476329973346312309621379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130984219982230874873080919 196476329973346312309621379)
              ·
                refine ⟨294714494960019468464432069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196476329973346312309621379 294714494960019468464432069)
                ·
                  refine ⟨55258967805003650337081013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294714494960019468464432069 55258967805003650337081013)
                  ·
                    refine ⟨5180528231719092219101345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55258967805003650337081013 5180528231719092219101345)
                    ·
                      refine ⟨3885396173789319164326009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180528231719092219101345 3885396173789319164326009)
                      ·
                        rfl

theorem cell23_7566782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_7566782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566782 prefixEnd_7566782 := by exact prefixLift 7566782
  have htrace : WordTrace (prefixWord ++ tailWord_7566782) baseStart_7566782 baseEnd_7566782 := by
    simpa [prefixWord, tailWord_7566782, baseEnd_7566782] using wordTrace_append hprefix tailTrace_7566782
  have hstable : (prefixWord ++ tailWord_7566782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566782).length < 2 ^ (prefixWord ++ tailWord_7566782).sum := by decide
  have hdescent : baseEnd_7566782 < baseStart_7566782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566879 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 3]
def baseStart_7566879 : Nat := 118140960795 + 7566879 * 2 ^ 59
def prefixEnd_7566879 : Nat := 4983230072969 + 3 ^ 40 * 7566879 * 2
def baseEnd_7566879 : Nat := 3885445981412805284813063

theorem tailTrace_7566879 : CollatzResearch.WordTrace tailWord_7566879 prefixEnd_7566879 3885445981412805284813063 := by
  unfold tailWord_7566879
  simp only [CollatzResearch.WordTrace]
  refine ⟨275986750353497177891455691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183991166902331451927637127 275986750353497177891455691)
  ·
    refine ⟨413980125530245766837183537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275986750353497177891455691 413980125530245766837183537)
    ·
      refine ⟨310485094147684325127887653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413980125530245766837183537 310485094147684325127887653)
      ·
        refine ⟨58215955152690810961478935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310485094147684325127887653 58215955152690810961478935)
        ·
          refine ⟨87323932729036216442218403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58215955152690810961478935 87323932729036216442218403)
          ·
            refine ⟨130985899093554324663327605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87323932729036216442218403 130985899093554324663327605)
            ·
              refine ⟨12279928040020717937186963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130985899093554324663327605 12279928040020717937186963)
              ·
                refine ⟨18419892060031076905780445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12279928040020717937186963 18419892060031076905780445)
                ·
                  refine ⟨6907459522511653839667667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18419892060031076905780445 6907459522511653839667667)
                  ·
                    refine ⟨10361189283767480759501501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907459522511653839667667 10361189283767480759501501)
                    ·
                      refine ⟨3885445981412805284813063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361189283767480759501501 3885445981412805284813063)
                      ·
                        rfl

theorem cell23_7566879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_7566879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566879 prefixEnd_7566879 := by exact prefixLift 7566879
  have htrace : WordTrace (prefixWord ++ tailWord_7566879) baseStart_7566879 baseEnd_7566879 := by
    simpa [prefixWord, tailWord_7566879, baseEnd_7566879] using wordTrace_append hprefix tailTrace_7566879
  have hstable : (prefixWord ++ tailWord_7566879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566879).length < 2 ^ (prefixWord ++ tailWord_7566879).sum := by decide
  have hdescent : baseEnd_7566879 < baseStart_7566879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566885 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_7566885 : Nat := 118140960795 + 7566885 * 2 ^ 59
def prefixEnd_7566885 : Nat := 4983230072969 + 3 ^ 40 * 7566885 * 2
def baseEnd_7566885 : Nat := 3885449062296732261338035

theorem tailTrace_7566885 : CollatzResearch.WordTrace tailWord_7566885 prefixEnd_7566885 3885449062296732261338035 := by
  unfold tailWord_7566885
  simp only [CollatzResearch.WordTrace]
  refine ⟨275986969191475440916174109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183991312794316960610782739 275986969191475440916174109)
  ·
    refine ⟨103495113446803290343565291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275986969191475440916174109 103495113446803290343565291)
    ·
      refine ⟨155242670170204935515347937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103495113446803290343565291 155242670170204935515347937)
      ·
        refine ⟨116432002627653701636510953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155242670170204935515347937 116432002627653701636510953)
        ·
          refine ⟨87324001970740276227383215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116432002627653701636510953 87324001970740276227383215)
          ·
            refine ⟨130986002956110414341074823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87324001970740276227383215 130986002956110414341074823)
            ·
              refine ⟨196479004434165621511612235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130986002956110414341074823 196479004434165621511612235)
              ·
                refine ⟨294718506651248432267418353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196479004434165621511612235 294718506651248432267418353)
                ·
                  refine ⟨221038879988436324200563765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294718506651248432267418353 221038879988436324200563765)
                  ·
                    refine ⟨20722394998915905393802853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221038879988436324200563765 20722394998915905393802853)
                    ·
                      refine ⟨3885449062296732261338035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20722394998915905393802853 3885449062296732261338035)
                      ·
                        rfl

theorem cell23_7566885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_7566885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566885 prefixEnd_7566885 := by exact prefixLift 7566885
  have htrace : WordTrace (prefixWord ++ tailWord_7566885) baseStart_7566885 baseEnd_7566885 := by
    simpa [prefixWord, tailWord_7566885, baseEnd_7566885] using wordTrace_append hprefix tailTrace_7566885
  have hstable : (prefixWord ++ tailWord_7566885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566885).length < 2 ^ (prefixWord ++ tailWord_7566885).sum := by decide
  have hdescent : baseEnd_7566885 < baseStart_7566885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566899 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 1, 5]
def baseStart_7566899 : Nat := 118140960795 + 7566899 * 2 ^ 59
def prefixEnd_7566899 : Nat := 4983230072969 + 3 ^ 40 * 7566899 * 2
def baseEnd_7566899 : Nat := 1295152083675298402187657

theorem tailTrace_7566899 : CollatzResearch.WordTrace tailWord_7566899 prefixEnd_7566899 1295152083675298402187657 := by
  unfold tailWord_7566899
  simp only [CollatzResearch.WordTrace]
  refine ⟨275987479813424721307183751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183991653208949814204789167 275987479813424721307183751)
  ·
    refine ⟨413981219720137081960775627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275987479813424721307183751 413981219720137081960775627)
    ·
      refine ⟨620971829580205622941163441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413981219720137081960775627 620971829580205622941163441)
      ·
        refine ⟨465728872185154217205872581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620971829580205622941163441 465728872185154217205872581)
        ·
          refine ⟨87324163534716415726101109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465728872185154217205872581 87324163534716415726101109)
          ·
            refine ⟨8186640331379663974321979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87324163534716415726101109 8186640331379663974321979)
            ·
              refine ⟨12279960497069495961482969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8186640331379663974321979 12279960497069495961482969)
              ·
                refine ⟨9209970372802121971112227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12279960497069495961482969 9209970372802121971112227)
                ·
                  refine ⟨13814955559203182956668341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209970372802121971112227 13814955559203182956668341)
                  ·
                    refine ⟨1295152083675298402187657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13814955559203182956668341 1295152083675298402187657)
                    ·
                      rfl

theorem cell23_7566899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 5].length) (baseStart_7566899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566899 prefixEnd_7566899 := by exact prefixLift 7566899
  have htrace : WordTrace (prefixWord ++ tailWord_7566899) baseStart_7566899 baseEnd_7566899 := by
    simpa [prefixWord, tailWord_7566899, baseEnd_7566899] using wordTrace_append hprefix tailTrace_7566899
  have hstable : (prefixWord ++ tailWord_7566899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566899).length < 2 ^ (prefixWord ++ tailWord_7566899).sum := by decide
  have hdescent : baseEnd_7566899 < baseStart_7566899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566929 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 2, 4]
def baseStart_7566929 : Nat := 118140960795 + 7566929 * 2 ^ 59
def prefixEnd_7566929 : Nat := 4983230072969 + 3 ^ 40 * 7566929 * 2
def baseEnd_7566929 : Nat := 1295157218481843363062611

theorem tailTrace_7566929 : CollatzResearch.WordTrace tailWord_7566929 prefixEnd_7566929 1295157218481843363062611 := by
  unfold tailWord_7566929
  simp only [CollatzResearch.WordTrace]
  refine ⟨275988574003316036430775841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183992382668877357620517227 275988574003316036430775841)
  ·
    refine ⟨206991430502487027323081881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275988574003316036430775841 206991430502487027323081881)
    ·
      refine ⟨155243572876865270492311411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206991430502487027323081881 155243572876865270492311411)
      ·
        refine ⟨232865359315297905738467117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155243572876865270492311411 232865359315297905738467117)
        ·
          refine ⟨87324509743236714651925169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232865359315297905738467117 87324509743236714651925169)
          ·
            refine ⟨65493382307427535988943877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87324509743236714651925169 65493382307427535988943877)
            ·
              refine ⟨12280009182642662997926977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65493382307427535988943877 12280009182642662997926977)
              ·
                refine ⟨9210006886981997248445233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12280009182642662997926977 9210006886981997248445233)
                ·
                  refine ⟨6907505165236497936333925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9210006886981997248445233 6907505165236497936333925)
                  ·
                    refine ⟨1295157218481843363062611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907505165236497936333925 1295157218481843363062611)
                    ·
                      rfl

theorem cell23_7566929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_7566929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566929 prefixEnd_7566929 := by exact prefixLift 7566929
  have htrace : WordTrace (prefixWord ++ tailWord_7566929) baseStart_7566929 baseEnd_7566929 := by
    simpa [prefixWord, tailWord_7566929, baseEnd_7566929] using wordTrace_append hprefix tailTrace_7566929
  have hstable : (prefixWord ++ tailWord_7566929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566929).length < 2 ^ (prefixWord ++ tailWord_7566929).sum := by decide
  have hdescent : baseEnd_7566929 < baseStart_7566929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566930 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_7566930 : Nat := 118140960795 + 7566930 * 2 ^ 59
def prefixEnd_7566930 : Nat := 4983230072969 + 3 ^ 40 * 7566930 * 2
def baseEnd_7566930 : Nat := 3885472168926184585275329

theorem tailTrace_7566930 : CollatzResearch.WordTrace tailWord_7566930 prefixEnd_7566930 3885472168926184585275329 := by
  unfold tailWord_7566930
  simp only [CollatzResearch.WordTrace]
  refine ⟨68997152619078103400390561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183992406984208275734374829 68997152619078103400390561)
  ·
    refine ⟨51747864464308577550292921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68997152619078103400390561 51747864464308577550292921)
    ·
      refine ⟨38810898348231433162719691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51747864464308577550292921 38810898348231433162719691)
      ·
        refine ⟨58216347522347149744079537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38810898348231433162719691 58216347522347149744079537)
        ·
          refine ⟨43662260641760362308059653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58216347522347149744079537 43662260641760362308059653)
          ·
            refine ⟨8186673870330067932761185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43662260641760362308059653 8186673870330067932761185)
            ·
              refine ⟨6140005402747550949570889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186673870330067932761185 6140005402747550949570889)
              ·
                refine ⟨4605004052060663212178167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6140005402747550949570889 4605004052060663212178167)
                ·
                  refine ⟨6907506078090994818267251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605004052060663212178167 6907506078090994818267251)
                  ·
                    refine ⟨10361259117136492227400877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907506078090994818267251 10361259117136492227400877)
                    ·
                      refine ⟨3885472168926184585275329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361259117136492227400877 3885472168926184585275329)
                      ·
                        rfl

theorem cell23_7566930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_7566930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566930 prefixEnd_7566930 := by exact prefixLift 7566930
  have htrace : WordTrace (prefixWord ++ tailWord_7566930) baseStart_7566930 baseEnd_7566930 := by
    simpa [prefixWord, tailWord_7566930, baseEnd_7566930] using wordTrace_append hprefix tailTrace_7566930
  have hstable : (prefixWord ++ tailWord_7566930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566930).length < 2 ^ (prefixWord ++ tailWord_7566930).sum := by decide
  have hdescent : baseEnd_7566930 < baseStart_7566930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566932 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_7566932 : Nat := 118140960795 + 7566932 * 2 ^ 59
def prefixEnd_7566932 : Nat := 4983230072969 + 3 ^ 40 * 7566932 * 2
def baseEnd_7566932 : Nat := 3885473195887493577450319

theorem tailTrace_7566932 : CollatzResearch.WordTrace tailWord_7566932 prefixEnd_7566932 3885473195887493577450319 := by
  unfold tailWord_7566932
  simp only [CollatzResearch.WordTrace]
  refine ⟨137994341711152583971567525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183992455614870111962090033 137994341711152583971567525)
  ·
    refine ⟨25873939070841109494668911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137994341711152583971567525 25873939070841109494668911)
    ·
      refine ⟨38810908606261664242003367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25873939070841109494668911 38810908606261664242003367)
      ·
        refine ⟨58216362909392496363005051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38810908606261664242003367 58216362909392496363005051)
        ·
          refine ⟨87324544364088744544507577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58216362909392496363005051 87324544364088744544507577)
          ·
            refine ⟨65493408273066558408380683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87324544364088744544507577 65493408273066558408380683)
            ·
              refine ⟨98240112409599837612571025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65493408273066558408380683 98240112409599837612571025)
              ·
                refine ⟨73680084307199878209428269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98240112409599837612571025 73680084307199878209428269)
                ·
                  refine ⟨27630031615199954328535601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73680084307199878209428269 27630031615199954328535601)
                  ·
                    refine ⟨20722523711399965746401701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27630031615199954328535601 20722523711399965746401701)
                    ·
                      refine ⟨3885473195887493577450319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20722523711399965746401701 3885473195887493577450319)
                      ·
                        rfl

theorem cell23_7566932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_7566932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566932 prefixEnd_7566932 := by exact prefixLift 7566932
  have htrace : WordTrace (prefixWord ++ tailWord_7566932) baseStart_7566932 baseEnd_7566932 := by
    simpa [prefixWord, tailWord_7566932, baseEnd_7566932] using wordTrace_append hprefix tailTrace_7566932
  have hstable : (prefixWord ++ tailWord_7566932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566932).length < 2 ^ (prefixWord ++ tailWord_7566932).sum := by decide
  have hdescent : baseEnd_7566932 < baseStart_7566932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566949 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_7566949 : Nat := 118140960795 + 7566949 * 2 ^ 59
def prefixEnd_7566949 : Nat := 4983230072969 + 3 ^ 40 * 7566949 * 2
def baseEnd_7566949 : Nat := 3885481925058620010937741

theorem tailTrace_7566949 : CollatzResearch.WordTrace tailWord_7566949 prefixEnd_7566949 3885481925058620010937741 := by
  unfold tailWord_7566949
  simp only [CollatzResearch.WordTrace]
  refine ⟨275989303463243579846503901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183992868975495719897669267 275989303463243579846503901)
  ·
    refine ⟨103495988798716342442438963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275989303463243579846503901 103495988798716342442438963)
    ·
      refine ⟨155243983198074513663658445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103495988798716342442438963 155243983198074513663658445)
      ·
        refine ⟨58216493699277942623871917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155243983198074513663658445 58216493699277942623871917)
        ·
          refine ⟨21831185137229228483951969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58216493699277942623871917 21831185137229228483951969)
          ·
            refine ⟨16373388852921921362963977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21831185137229228483951969 16373388852921921362963977)
            ·
              refine ⟨12280041639691441022222983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16373388852921921362963977 12280041639691441022222983)
              ·
                refine ⟨18420062459537161533334475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12280041639691441022222983 18420062459537161533334475)
                ·
                  refine ⟨27630093689305742300001713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18420062459537161533334475 27630093689305742300001713)
                  ·
                    refine ⟨20722570266979306725001285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27630093689305742300001713 20722570266979306725001285)
                    ·
                      refine ⟨3885481925058620010937741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20722570266979306725001285 3885481925058620010937741)
                      ·
                        rfl

theorem cell23_7566949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_7566949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566949 prefixEnd_7566949 := by exact prefixLift 7566949
  have htrace : WordTrace (prefixWord ++ tailWord_7566949) baseStart_7566949 baseEnd_7566949 := by
    simpa [prefixWord, tailWord_7566949, baseEnd_7566949] using wordTrace_append hprefix tailTrace_7566949
  have hstable : (prefixWord ++ tailWord_7566949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566949).length < 2 ^ (prefixWord ++ tailWord_7566949).sum := by decide
  have hdescent : baseEnd_7566949 < baseStart_7566949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566969 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 3]
def baseStart_7566969 : Nat := 118140960795 + 7566969 * 2 ^ 59
def prefixEnd_7566969 : Nat := 4983230072969 + 3 ^ 40 * 7566969 * 2
def baseEnd_7566969 : Nat := 3885492194671709932687649

theorem tailTrace_7566969 : CollatzResearch.WordTrace tailWord_7566969 prefixEnd_7566969 3885492194671709932687649 := by
  unfold tailWord_7566969
  simp only [CollatzResearch.WordTrace]
  refine ⟨275990032923171123262231961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183993355282114082174821307 275990032923171123262231961)
  ·
    refine ⟨206992524692378342446673971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275990032923171123262231961 206992524692378342446673971)
    ·
      refine ⟨310488787038567513670010957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206992524692378342446673971 310488787038567513670010957)
      ·
        refine ⟨116433295139462817626254109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310488787038567513670010957 116433295139462817626254109)
        ·
          refine ⟨43662485677298556609845291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116433295139462817626254109 43662485677298556609845291)
          ·
            refine ⟨65493728515947834914767937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43662485677298556609845291 65493728515947834914767937)
            ·
              refine ⟨49120296386960876186075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65493728515947834914767937 49120296386960876186075953)
              ·
                refine ⟨36840222290220657139556965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49120296386960876186075953 36840222290220657139556965)
                ·
                  refine ⟨6907541679416373213666931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36840222290220657139556965 6907541679416373213666931)
                  ·
                    refine ⟨10361312519124559820500397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907541679416373213666931 10361312519124559820500397)
                    ·
                      refine ⟨3885492194671709932687649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361312519124559820500397 3885492194671709932687649)
                      ·
                        rfl

theorem cell23_7566969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_7566969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566969 prefixEnd_7566969 := by exact prefixLift 7566969
  have htrace : WordTrace (prefixWord ++ tailWord_7566969) baseStart_7566969 baseEnd_7566969 := by
    simpa [prefixWord, tailWord_7566969, baseEnd_7566969] using wordTrace_append hprefix tailTrace_7566969
  have hstable : (prefixWord ++ tailWord_7566969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566969).length < 2 ^ (prefixWord ++ tailWord_7566969).sum := by decide
  have hdescent : baseEnd_7566969 < baseStart_7566969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566973 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_7566973 : Nat := 118140960795 + 7566973 * 2 ^ 59
def prefixEnd_7566973 : Nat := 4983230072969 + 3 ^ 40 * 7566973 * 2
def baseEnd_7566973 : Nat := 3885494248594327917037631

theorem tailTrace_7566973 : CollatzResearch.WordTrace tailWord_7566973 prefixEnd_7566973 3885494248594327917037631 := by
  unfold tailWord_7566973
  simp only [CollatzResearch.WordTrace]
  refine ⟨275990178815156631945377573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183993452543437754630251715 275990178815156631945377573)
  ·
    refine ⟨51748158527841868489758295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275990178815156631945377573 51748158527841868489758295)
    ·
      refine ⟨77622237791762802734637443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51748158527841868489758295 77622237791762802734637443)
      ·
        refine ⟨116433356687644204101956165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77622237791762802734637443 116433356687644204101956165)
        ·
          refine ⟨21831254378933288269116781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116433356687644204101956165 21831254378933288269116781)
          ·
            refine ⟨8186720392099983100918793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21831254378933288269116781 8186720392099983100918793)
            ·
              refine ⟨6140040294074987325689095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186720392099983100918793 6140040294074987325689095)
              ·
                refine ⟨9210060441112480988533643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140040294074987325689095 9210060441112480988533643)
                ·
                  refine ⟨13815090661668721482800465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210060441112480988533643 13815090661668721482800465)
                  ·
                    refine ⟨10361317996251541112100349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13815090661668721482800465 10361317996251541112100349)
                    ·
                      refine ⟨3885494248594327917037631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361317996251541112100349 3885494248594327917037631)
                      ·
                        rfl

theorem cell23_7566973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_7566973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566973 prefixEnd_7566973 := by exact prefixLift 7566973
  have htrace : WordTrace (prefixWord ++ tailWord_7566973) baseStart_7566973 baseEnd_7566973 := by
    simpa [prefixWord, tailWord_7566973, baseEnd_7566973] using wordTrace_append hprefix tailTrace_7566973
  have hstable : (prefixWord ++ tailWord_7566973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566973).length < 2 ^ (prefixWord ++ tailWord_7566973).sum := by decide
  have hdescent : baseEnd_7566973 < baseStart_7566973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7566986 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_7566986 : Nat := 118140960795 + 7566986 * 2 ^ 59
def prefixEnd_7566986 : Nat := 4983230072969 + 3 ^ 40 * 7566986 * 2
def baseEnd_7566986 : Nat := 3885500923842836366175071

theorem tailTrace_7566986 : CollatzResearch.WordTrace tailWord_7566986 prefixEnd_7566986 3885500923842836366175071 := by
  unfold tailWord_7566986
  simp only [CollatzResearch.WordTrace]
  refine ⟨68997663241027383791400203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183993768642739690110400541 68997663241027383791400203)
  ·
    refine ⟨103496494861541075687100305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68997663241027383791400203 103496494861541075687100305)
    ·
      refine ⟨77622371146155806765325229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103496494861541075687100305 77622371146155806765325229)
      ·
        refine ⟨29108389179808427536996961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77622371146155806765325229 29108389179808427536996961)
        ·
          refine ⟨21831291884856320652747721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29108389179808427536996961 21831291884856320652747721)
          ·
            refine ⟨16373468913642240489560791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21831291884856320652747721 16373468913642240489560791)
            ·
              refine ⟨24560203370463360734341187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16373468913642240489560791 24560203370463360734341187)
              ·
                refine ⟨36840305055695041101511781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24560203370463360734341187 36840305055695041101511781)
                ·
                  refine ⟨6907557197942820206533459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36840305055695041101511781 6907557197942820206533459)
                  ·
                    refine ⟨10361335796914230309800189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907557197942820206533459 10361335796914230309800189)
                    ·
                      refine ⟨3885500923842836366175071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361335796914230309800189 3885500923842836366175071)
                      ·
                        rfl

theorem cell23_7566986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_7566986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7566986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7566986 prefixEnd_7566986 := by exact prefixLift 7566986
  have htrace : WordTrace (prefixWord ++ tailWord_7566986) baseStart_7566986 baseEnd_7566986 := by
    simpa [prefixWord, tailWord_7566986, baseEnd_7566986] using wordTrace_append hprefix tailTrace_7566986
  have hstable : (prefixWord ++ tailWord_7566986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7566986).length < 2 ^ (prefixWord ++ tailWord_7566986).sum := by decide
  have hdescent : baseEnd_7566986 < baseStart_7566986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7566986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567026 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_7567026 : Nat := 118140960795 + 7567026 * 2 ^ 59
def prefixEnd_7567026 : Nat := 4983230072969 + 3 ^ 40 * 7567026 * 2
def baseEnd_7567026 : Nat := 3885521463069016209674887

theorem tailTrace_7567026 : CollatzResearch.WordTrace tailWord_7567026 prefixEnd_7567026 3885521463069016209674887 := by
  unfold tailWord_7567026
  simp only [CollatzResearch.WordTrace]
  refine ⟨68998027970991155499264233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183994741255976414664704621 68998027970991155499264233)
  ·
    refine ⟨51748520978243366624448175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68998027970991155499264233 51748520978243366624448175)
    ·
      refine ⟨77622781467365049936672263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51748520978243366624448175 77622781467365049936672263)
      ·
        refine ⟨116434172201047574905008395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77622781467365049936672263 116434172201047574905008395)
        ·
          refine ⟨174651258301571362357512593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116434172201047574905008395 174651258301571362357512593)
          ·
            refine ⟨130988443726178521768134445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174651258301571362357512593 130988443726178521768134445)
            ·
              refine ⟨49120666397316945663050417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130988443726178521768134445 49120666397316945663050417)
              ·
                refine ⟨36840499797987709247287813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49120666397316945663050417 36840499797987709247287813)
                ·
                  refine ⟨6907593712122695483866465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36840499797987709247287813 6907593712122695483866465)
                  ·
                    refine ⟨5180695284092021612899849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6907593712122695483866465 5180695284092021612899849)
                    ·
                      refine ⟨3885521463069016209674887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180695284092021612899849 3885521463069016209674887)
                      ·
                        rfl

theorem cell23_7567026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_7567026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567026 prefixEnd_7567026 := by exact prefixLift 7567026
  have htrace : WordTrace (prefixWord ++ tailWord_7567026) baseStart_7567026 baseEnd_7567026 := by
    simpa [prefixWord, tailWord_7567026, baseEnd_7567026] using wordTrace_append hprefix tailTrace_7567026
  have hstable : (prefixWord ++ tailWord_7567026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567026).length < 2 ^ (prefixWord ++ tailWord_7567026).sum := by decide
  have hdescent : baseEnd_7567026 < baseStart_7567026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567030 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7567030 : Nat := 118140960795 + 7567030 * 2 ^ 59
def prefixEnd_7567030 : Nat := 4983230072969 + 3 ^ 40 * 7567030 * 2
def baseEnd_7567030 : Nat := 3885523516991634194024869

theorem tailTrace_7567030 : CollatzResearch.WordTrace tailWord_7567030 prefixEnd_7567030 3885523516991634194024869 := by
  unfold tailWord_7567030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249516110996883167512659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183994838517300087120135029 17249516110996883167512659)
  ·
    refine ⟨25874274166495324751268989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17249516110996883167512659 25874274166495324751268989)
    ·
      refine ⟨9702852812435746781725871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25874274166495324751268989 9702852812435746781725871)
      ·
        refine ⟨14554279218653620172588807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9702852812435746781725871 14554279218653620172588807)
        ·
          refine ⟨21831418827980430258883211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14554279218653620172588807 21831418827980430258883211)
          ·
            refine ⟨32747128241970645388324817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21831418827980430258883211 32747128241970645388324817)
            ·
              refine ⟨24560346181477984041243613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32747128241970645388324817 24560346181477984041243613)
              ·
                refine ⟨9210129818054244015466355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24560346181477984041243613 9210129818054244015466355)
                ·
                  refine ⟨13815194727081366023199533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210129818054244015466355 13815194727081366023199533)
                  ·
                    refine ⟨5180698022655512258699825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13815194727081366023199533 5180698022655512258699825)
                    ·
                      refine ⟨3885523516991634194024869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180698022655512258699825 3885523516991634194024869)
                      ·
                        rfl

theorem cell23_7567030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7567030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567030 prefixEnd_7567030 := by exact prefixLift 7567030
  have htrace : WordTrace (prefixWord ++ tailWord_7567030) baseStart_7567030 baseEnd_7567030 := by
    simpa [prefixWord, tailWord_7567030, baseEnd_7567030] using wordTrace_append hprefix tailTrace_7567030
  have hstable : (prefixWord ++ tailWord_7567030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567030).length < 2 ^ (prefixWord ++ tailWord_7567030).sum := by decide
  have hdescent : baseEnd_7567030 < baseStart_7567030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567060 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7567060 : Nat := 118140960795 + 7567060 * 2 ^ 59
def prefixEnd_7567060 : Nat := 4983230072969 + 3 ^ 40 * 7567060 * 2
def baseEnd_7567060 : Nat := 3885538921411269076649731

theorem tailTrace_7567060 : CollatzResearch.WordTrace tailWord_7567060 prefixEnd_7567060 3885538921411269076649731 := by
  unfold tailWord_7567060
  simp only [CollatzResearch.WordTrace]
  refine ⟨137996675982920722901897317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183995567977227630535863089 137996675982920722901897317)
  ·
    refine ⟨25874376746797635544105747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137996675982920722901897317 25874376746797635544105747)
    ·
      refine ⟨38811565120196453316158621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25874376746797635544105747 38811565120196453316158621)
      ·
        refine ⟨14554336920073669993559483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38811565120196453316158621 14554336920073669993559483)
        ·
          refine ⟨21831505380110504990339225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14554336920073669993559483 21831505380110504990339225)
          ·
            refine ⟨16373629035082878742754419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21831505380110504990339225 16373629035082878742754419)
            ·
              refine ⟨24560443552624318114131629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16373629035082878742754419 24560443552624318114131629)
              ·
                refine ⟨9210166332234119292799361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24560443552624318114131629 9210166332234119292799361)
                ·
                  refine ⟨6907624749175589469599521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9210166332234119292799361 6907624749175589469599521)
                  ·
                    refine ⟨5180718561881692102199641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6907624749175589469599521 5180718561881692102199641)
                    ·
                      refine ⟨3885538921411269076649731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180718561881692102199641 3885538921411269076649731)
                      ·
                        rfl

theorem cell23_7567060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7567060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567060 prefixEnd_7567060 := by exact prefixLift 7567060
  have htrace : WordTrace (prefixWord ++ tailWord_7567060) baseStart_7567060 baseEnd_7567060 := by
    simpa [prefixWord, tailWord_7567060, baseEnd_7567060] using wordTrace_append hprefix tailTrace_7567060
  have hstable : (prefixWord ++ tailWord_7567060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567060).length < 2 ^ (prefixWord ++ tailWord_7567060).sum := by decide
  have hdescent : baseEnd_7567060 < baseStart_7567060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567156 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 8]
def baseStart_7567156 : Nat := 118140960795 + 7567156 * 2 ^ 59
def prefixEnd_7567156 : Nat := 4983230072969 + 3 ^ 40 * 7567156 * 2
def baseEnd_7567156 : Nat := 431732023950455633449921

theorem tailTrace_7567156 : CollatzResearch.WordTrace tailWord_7567156 prefixEnd_7567156 431732023950455633449921 := by
  unfold tailWord_7567156
  simp only [CollatzResearch.WordTrace]
  refine ⟨137998426686746827099644661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183997902248995769466192881 137998426686746827099644661)
  ·
    refine ⟨12937352501882515040591687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137998426686746827099644661 12937352501882515040591687)
    ·
      refine ⟨19406028752823772560887531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12937352501882515040591687 19406028752823772560887531)
      ·
        refine ⟨29109043129235658841331297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19406028752823772560887531 29109043129235658841331297)
        ·
          refine ⟨21831782346926744130998473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29109043129235658841331297 21831782346926744130998473)
          ·
            refine ⟨16373836760195058098248855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21831782346926744130998473 16373836760195058098248855)
            ·
              refine ⟨24560755140292587147373283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16373836760195058098248855 24560755140292587147373283)
              ·
                refine ⟨36841132710438880721059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24560755140292587147373283 36841132710438880721059925)
                ·
                  refine ⟨431732023950455633449921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36841132710438880721059925 431732023950455633449921)
                  ·
                    rfl

theorem cell23_7567156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_7567156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567156 prefixEnd_7567156 := by exact prefixLift 7567156
  have htrace : WordTrace (prefixWord ++ tailWord_7567156) baseStart_7567156 baseEnd_7567156 := by
    simpa [prefixWord, tailWord_7567156, baseEnd_7567156] using wordTrace_append hprefix tailTrace_7567156
  have hstable : (prefixWord ++ tailWord_7567156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567156).length < 2 ^ (prefixWord ++ tailWord_7567156).sum := by decide
  have hdescent : baseEnd_7567156 < baseStart_7567156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567176 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_7567176 : Nat := 118140960795 + 7567176 * 2 ^ 59
def prefixEnd_7567176 : Nat := 4983230072969 + 3 ^ 40 * 7567176 * 2
def baseEnd_7567176 : Nat := 3885598485167190622799197

theorem tailTrace_7567176 : CollatzResearch.WordTrace tailWord_7567176 prefixEnd_7567176 3885598485167190622799197 := by
  unfold tailWord_7567176
  simp only [CollatzResearch.WordTrace]
  refine ⟨137998791416710598807508691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183998388555614131743344921 137998791416710598807508691)
  ·
    refine ⟨206998187125065898211263037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137998791416710598807508691 206998187125065898211263037)
    ·
      refine ⟨77624320171899711829223639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206998187125065898211263037 77624320171899711829223639)
      ·
        refine ⟨116436480257849567743835459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77624320171899711829223639 116436480257849567743835459)
        ·
          refine ⟨174654720386774351615753189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116436480257849567743835459 174654720386774351615753189)
          ·
            refine ⟨32747760072520190927953723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174654720386774351615753189 32747760072520190927953723)
            ·
              refine ⟨49121640108780286391930585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32747760072520190927953723 49121640108780286391930585)
              ·
                refine ⟨36841230081585214793947939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49121640108780286391930585 36841230081585214793947939)
                ·
                  refine ⟨55261845122377822190921909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36841230081585214793947939 55261845122377822190921909)
                  ·
                    refine ⟨5180797980222920830398929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55261845122377822190921909 5180797980222920830398929)
                    ·
                      refine ⟨3885598485167190622799197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180797980222920830398929 3885598485167190622799197)
                      ·
                        rfl

theorem cell23_7567176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_7567176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567176 prefixEnd_7567176 := by exact prefixLift 7567176
  have htrace : WordTrace (prefixWord ++ tailWord_7567176) baseStart_7567176 baseEnd_7567176 := by
    simpa [prefixWord, tailWord_7567176, baseEnd_7567176] using wordTrace_append hprefix tailTrace_7567176
  have hstable : (prefixWord ++ tailWord_7567176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567176).length < 2 ^ (prefixWord ++ tailWord_7567176).sum := by decide
  have hdescent : baseEnd_7567176 < baseStart_7567176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567186 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_7567186 : Nat := 118140960795 + 7567186 * 2 ^ 59
def prefixEnd_7567186 : Nat := 4983230072969 + 3 ^ 40 * 7567186 * 2
def baseEnd_7567186 : Nat := 1295201206657911861224717

theorem tailTrace_7567186 : CollatzResearch.WordTrace tailWord_7567186 prefixEnd_7567186 1295201206657911861224717 := by
  unfold tailWord_7567186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68999486890846242330720353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183998631708923312881920941 68999486890846242330720353)
  ·
    refine ⟨51749615168134681748040265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68999486890846242330720353 51749615168134681748040265)
    ·
      refine ⟨38812211376101011311030199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51749615168134681748040265 38812211376101011311030199)
      ·
        refine ⟨58218317064151516966545299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38812211376101011311030199 58218317064151516966545299)
        ·
          refine ⟨87327475596227275449817949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58218317064151516966545299 87327475596227275449817949)
          ·
            refine ⟨32747803348585228293681731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87327475596227275449817949 32747803348585228293681731)
            ·
              refine ⟨49121705022877842440522597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32747803348585228293681731 49121705022877842440522597)
              ·
                refine ⟨9210319691789595457597987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49121705022877842440522597 9210319691789595457597987)
                ·
                  refine ⟨13815479537684393186396981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210319691789595457597987 13815479537684393186396981)
                  ·
                    refine ⟨1295201206657911861224717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13815479537684393186396981 1295201206657911861224717)
                    ·
                      rfl

theorem cell23_7567186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_7567186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567186 prefixEnd_7567186 := by exact prefixLift 7567186
  have htrace : WordTrace (prefixWord ++ tailWord_7567186) baseStart_7567186 baseEnd_7567186 := by
    simpa [prefixWord, tailWord_7567186, baseEnd_7567186] using wordTrace_append hprefix tailTrace_7567186
  have hstable : (prefixWord ++ tailWord_7567186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567186).length < 2 ^ (prefixWord ++ tailWord_7567186).sum := by decide
  have hdescent : baseEnd_7567186 < baseStart_7567186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567200 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 1, 1, 3]
def baseStart_7567200 : Nat := 118140960795 + 7567200 * 2 ^ 59
def prefixEnd_7567200 : Nat := 4983230072969 + 3 ^ 40 * 7567200 * 2
def baseEnd_7567200 : Nat := 3885610808702898528899087

theorem tailTrace_7567200 : CollatzResearch.WordTrace tailWord_7567200 prefixEnd_7567200 3885610808702898528899087 := by
  unfold tailWord_7567200
  simp only [CollatzResearch.WordTrace]
  refine ⟨137999229092667124856945527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183998972123556166475927369 137999229092667124856945527)
  ·
    refine ⟨206998843639000687285418291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137999229092667124856945527 206998843639000687285418291)
    ·
      refine ⟨310498265458501030928127437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206998843639000687285418291 310498265458501030928127437)
      ·
        refine ⟨116436849546937886598047789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310498265458501030928127437 116436849546937886598047789)
        ·
          refine ⟨43663818580101707474267921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116436849546937886598047789 43663818580101707474267921)
          ·
            refine ⟨32747863935076280605700941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43663818580101707474267921 32747863935076280605700941)
            ·
              refine ⟨12280448975653605227137853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32747863935076280605700941 12280448975653605227137853)
              ·
                refine ⟨4605168365870101960176695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12280448975653605227137853 4605168365870101960176695)
                ·
                  refine ⟨6907752548805152940265043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605168365870101960176695 6907752548805152940265043)
                  ·
                    refine ⟨10361628823207729410397565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907752548805152940265043 10361628823207729410397565)
                    ·
                      refine ⟨3885610808702898528899087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361628823207729410397565 3885610808702898528899087)
                      ·
                        rfl

theorem cell23_7567200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_7567200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567200 prefixEnd_7567200 := by exact prefixLift 7567200
  have htrace : WordTrace (prefixWord ++ tailWord_7567200) baseStart_7567200 baseEnd_7567200 := by
    simpa [prefixWord, tailWord_7567200, baseEnd_7567200] using wordTrace_append hprefix tailTrace_7567200
  have hstable : (prefixWord ++ tailWord_7567200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567200).length < 2 ^ (prefixWord ++ tailWord_7567200).sum := by decide
  have hdescent : baseEnd_7567200 < baseStart_7567200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567216 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 2, 4]
def baseStart_7567216 : Nat := 118140960795 + 7567216 * 2 ^ 59
def prefixEnd_7567216 : Nat := 4983230072969 + 3 ^ 40 * 7567216 * 2
def baseEnd_7567216 : Nat := 1295206341464456822099671

theorem tailTrace_7567216 : CollatzResearch.WordTrace tailWord_7567216 prefixEnd_7567216 1295206341464456822099671 := by
  unfold tailWord_7567216
  simp only [CollatzResearch.WordTrace]
  refine ⟨137999520876638142223236751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183999361168850856297649001 137999520876638142223236751)
  ·
    refine ⟨206999281314957213334855127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137999520876638142223236751 206999281314957213334855127)
    ·
      refine ⟨310498921972435820002282691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206999281314957213334855127 310498921972435820002282691)
      ·
        refine ⟨465748382958653730003424037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310498921972435820002282691 465748382958653730003424037)
        ·
          refine ⟨87327821804747574375642007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465748382958653730003424037 87327821804747574375642007)
          ·
            refine ⟨130991732707121361563463011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87327821804747574375642007 130991732707121361563463011)
            ·
              refine ⟨196487599060682042345194517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130991732707121361563463011 196487599060682042345194517)
              ·
                refine ⟨9210356205969470734930993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196487599060682042345194517 9210356205969470734930993)
                ·
                  refine ⟨6907767154477103051198245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9210356205969470734930993 6907767154477103051198245)
                  ·
                    refine ⟨1295206341464456822099671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907767154477103051198245 1295206341464456822099671)
                    ·
                      rfl

theorem cell23_7567216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_7567216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567216 prefixEnd_7567216 := by exact prefixLift 7567216
  have htrace : WordTrace (prefixWord ++ tailWord_7567216) baseStart_7567216 baseEnd_7567216 := by
    simpa [prefixWord, tailWord_7567216, baseEnd_7567216] using wordTrace_append hprefix tailTrace_7567216
  have hstable : (prefixWord ++ tailWord_7567216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567216).length < 2 ^ (prefixWord ++ tailWord_7567216).sum := by decide
  have hdescent : baseEnd_7567216 < baseStart_7567216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567240 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7567240 : Nat := 118140960795 + 7567240 * 2 ^ 59
def prefixEnd_7567240 : Nat := 4983230072969 + 3 ^ 40 * 7567240 * 2
def baseEnd_7567240 : Nat := 3885631347929078372398903

theorem tailTrace_7567240 : CollatzResearch.WordTrace tailWord_7567240 prefixEnd_7567240 3885631347929078372398903 := by
  unfold tailWord_7567240
  simp only [CollatzResearch.WordTrace]
  refine ⟨137999958552594668272673587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183999944736792891030231449 137999958552594668272673587)
  ·
    refine ⟨206999937828892002409010381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137999958552594668272673587 206999937828892002409010381)
    ·
      refine ⟨77624976685834500903378893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206999937828892002409010381 77624976685834500903378893)
      ·
        refine ⟨29109366257187937838767085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77624976685834500903378893 29109366257187937838767085)
        ·
          refine ⟨10916012346445476689537657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29109366257187937838767085 10916012346445476689537657)
          ·
            refine ⟨8187009259834107517153243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10916012346445476689537657 8187009259834107517153243)
            ·
              refine ⟨12280513889751161275729865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187009259834107517153243 12280513889751161275729865)
              ·
                refine ⟨9210385417313370956797399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12280513889751161275729865 9210385417313370956797399)
                ·
                  refine ⟨13815578125970056435196099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210385417313370956797399 13815578125970056435196099)
                  ·
                    refine ⟨20723367188955084652794149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13815578125970056435196099 20723367188955084652794149)
                    ·
                      refine ⟨3885631347929078372398903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20723367188955084652794149 3885631347929078372398903)
                      ·
                        rfl

theorem cell23_7567240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7567240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567240 prefixEnd_7567240 := by exact prefixLift 7567240
  have htrace : WordTrace (prefixWord ++ tailWord_7567240) baseStart_7567240 baseEnd_7567240 := by
    simpa [prefixWord, tailWord_7567240, baseEnd_7567240] using wordTrace_append hprefix tailTrace_7567240
  have hstable : (prefixWord ++ tailWord_7567240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567240).length < 2 ^ (prefixWord ++ tailWord_7567240).sum := by decide
  have hdescent : baseEnd_7567240 < baseStart_7567240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567254 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7567254 : Nat := 118140960795 + 7567254 * 2 ^ 59
def prefixEnd_7567254 : Nat := 4983230072969 + 3 ^ 40 * 7567254 * 2
def baseEnd_7567254 : Nat := 1295212845552747105874613

theorem tailTrace_7567254 : CollatzResearch.WordTrace tailWord_7567254 prefixEnd_7567254 1295212845552747105874613 := by
  unfold tailWord_7567254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17250026732946163558522301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184000285151425744624237877 17250026732946163558522301)
  ·
    refine ⟨6468760024854811334445863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17250026732946163558522301 6468760024854811334445863)
    ·
      refine ⟨9703140037282217001668795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468760024854811334445863 9703140037282217001668795)
      ·
        refine ⟨14554710055923325502503193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703140037282217001668795 14554710055923325502503193)
        ·
          refine ⟨10916032541942494126877395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14554710055923325502503193 10916032541942494126877395)
          ·
            refine ⟨16374048812913741190316093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916032541942494126877395 16374048812913741190316093)
            ·
              refine ⟨6140268304842652946368535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16374048812913741190316093 6140268304842652946368535)
              ·
                refine ⟨9210402457263979419552803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140268304842652946368535 9210402457263979419552803)
                ·
                  refine ⟨13815603685895969129329205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210402457263979419552803 13815603685895969129329205)
                  ·
                    refine ⟨1295212845552747105874613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13815603685895969129329205 1295212845552747105874613)
                    ·
                      rfl

theorem cell23_7567254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7567254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567254 prefixEnd_7567254 := by exact prefixLift 7567254
  have htrace : WordTrace (prefixWord ++ tailWord_7567254) baseStart_7567254 baseEnd_7567254 := by
    simpa [prefixWord, tailWord_7567254, baseEnd_7567254] using wordTrace_append hprefix tailTrace_7567254
  have hstable : (prefixWord ++ tailWord_7567254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567254).length < 2 ^ (prefixWord ++ tailWord_7567254).sum := by decide
  have hdescent : baseEnd_7567254 < baseStart_7567254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567269 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_7567269 : Nat := 118140960795 + 7567269 * 2 ^ 59
def prefixEnd_7567269 : Nat := 4983230072969 + 3 ^ 40 * 7567269 * 2
def baseEnd_7567269 : Nat := 3885646238868058758936269

theorem tailTrace_7567269 : CollatzResearch.WordTrace tailWord_7567269 prefixEnd_7567269 3885646238868058758936269 := by
  unfold tailWord_7567269
  simp only [CollatzResearch.WordTrace]
  refine ⟨276000974822084274498152861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184000649881389516332101907 276000974822084274498152861)
  ·
    refine ⟨103500365558281602936807323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276000974822084274498152861 103500365558281602936807323)
    ·
      refine ⟨155250548337422404405210985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103500365558281602936807323 155250548337422404405210985)
      ·
        refine ⟨116437911253066803303908239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155250548337422404405210985 116437911253066803303908239)
        ·
          refine ⟨174656866879600204955862359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116437911253066803303908239 174656866879600204955862359)
          ·
            refine ⟨261985300319400307433793539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174656866879600204955862359 261985300319400307433793539)
            ·
              refine ⟨392977950479100461150690309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261985300319400307433793539 392977950479100461150690309)
              ·
                refine ⟨73683365714831336465754433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392977950479100461150690309 73683365714831336465754433)
                ·
                  refine ⟨55262524286123502349315825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73683365714831336465754433 55262524286123502349315825)
                  ·
                    refine ⟨41446893214592626761986869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55262524286123502349315825 41446893214592626761986869)
                    ·
                      refine ⟨3885646238868058758936269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41446893214592626761986869 3885646238868058758936269)
                      ·
                        rfl

theorem cell23_7567269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_7567269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567269 prefixEnd_7567269 := by exact prefixLift 7567269
  have htrace : WordTrace (prefixWord ++ tailWord_7567269) baseStart_7567269 baseEnd_7567269 := by
    simpa [prefixWord, tailWord_7567269, baseEnd_7567269] using wordTrace_append hprefix tailTrace_7567269
  have hstable : (prefixWord ++ tailWord_7567269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567269).length < 2 ^ (prefixWord ++ tailWord_7567269).sum := by decide
  have hdescent : baseEnd_7567269 < baseStart_7567269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567279 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_7567279 : Nat := 118140960795 + 7567279 * 2 ^ 59
def prefixEnd_7567279 : Nat := 4983230072969 + 3 ^ 40 * 7567279 * 2
def baseEnd_7567279 : Nat := 3885651373674603719811223

theorem tailTrace_7567279 : CollatzResearch.WordTrace tailWord_7567279 prefixEnd_7567279 3885651373674603719811223 := by
  unfold tailWord_7567279
  simp only [CollatzResearch.WordTrace]
  refine ⟨276001339552048046206016891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184000893034698697470677927 276001339552048046206016891)
  ·
    refine ⟨414002009328072069309025337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276001339552048046206016891 414002009328072069309025337)
    ·
      refine ⟨310501506996054051981769003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414002009328072069309025337 310501506996054051981769003)
      ·
        refine ⟨465752260494081077972653505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310501506996054051981769003 465752260494081077972653505)
        ·
          refine ⟨349314195370560808479490129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465752260494081077972653505 349314195370560808479490129)
          ·
            refine ⟨261985646527920606359617597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349314195370560808479490129 261985646527920606359617597)
            ·
              refine ⟨98244617447970227384856599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261985646527920606359617597 98244617447970227384856599)
              ·
                refine ⟨147366926171955341077284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98244617447970227384856599 147366926171955341077284899)
                ·
                  refine ⟨221050389257933011615927349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147366926171955341077284899 221050389257933011615927349)
                  ·
                    refine ⟨20723473992931219838993189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221050389257933011615927349 20723473992931219838993189)
                    ·
                      refine ⟨3885651373674603719811223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20723473992931219838993189 3885651373674603719811223)
                      ·
                        rfl

theorem cell23_7567279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_7567279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567279 prefixEnd_7567279 := by exact prefixLift 7567279
  have htrace : WordTrace (prefixWord ++ tailWord_7567279) baseStart_7567279 baseEnd_7567279 := by
    simpa [prefixWord, tailWord_7567279, baseEnd_7567279] using wordTrace_append hprefix tailTrace_7567279
  have hstable : (prefixWord ++ tailWord_7567279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567279).length < 2 ^ (prefixWord ++ tailWord_7567279).sum := by decide
  have hdescent : baseEnd_7567279 < baseStart_7567279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567316 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7567316 : Nat := 118140960795 + 7567316 * 2 ^ 59
def prefixEnd_7567316 : Nat := 4983230072969 + 3 ^ 40 * 7567316 * 2
def baseEnd_7567316 : Nat := 3885670372458820075048553

theorem tailTrace_7567316 : CollatzResearch.WordTrace tailWord_7567316 prefixEnd_7567316 3885670372458820075048553 := by
  unfold tailWord_7567316
  simp only [CollatzResearch.WordTrace]
  refine ⟨138001344526457000762556901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184001792701942667683409201 138001344526457000762556901)
  ·
    refine ⟨25875252098710687642979419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138001344526457000762556901 25875252098710687642979419)
    ·
      refine ⟨38812878148066031464469129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25875252098710687642979419 38812878148066031464469129)
      ·
        refine ⟨29109658611049523598351847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38812878148066031464469129 29109658611049523598351847)
        ·
          refine ⟨43664487916574285397527771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29109658611049523598351847 43664487916574285397527771)
          ·
            refine ⟨65496731874861428096291657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43664487916574285397527771 65496731874861428096291657)
            ·
              refine ⟨49122548906146071072218743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65496731874861428096291657 49122548906146071072218743)
              ·
                refine ⟨73683823359219106608328115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49122548906146071072218743 73683823359219106608328115)
                ·
                  refine ⟨110525735038828659912492173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73683823359219106608328115 110525735038828659912492173)
                  ·
                    refine ⟨41447150639560747467184565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110525735038828659912492173 41447150639560747467184565)
                    ·
                      refine ⟨3885670372458820075048553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41447150639560747467184565 3885670372458820075048553)
                      ·
                        rfl

theorem cell23_7567316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7567316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567316 prefixEnd_7567316 := by exact prefixLift 7567316
  have htrace : WordTrace (prefixWord ++ tailWord_7567316) baseStart_7567316 baseEnd_7567316 := by
    simpa [prefixWord, tailWord_7567316, baseEnd_7567316] using wordTrace_append hprefix tailTrace_7567316
  have hstable : (prefixWord ++ tailWord_7567316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567316).length < 2 ^ (prefixWord ++ tailWord_7567316).sum := by decide
  have hdescent : baseEnd_7567316 < baseStart_7567316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567317 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_7567317 : Nat := 118140960795 + 7567317 * 2 ^ 59
def prefixEnd_7567317 : Nat := 4983230072969 + 3 ^ 40 * 7567317 * 2
def baseEnd_7567317 : Nat := 3885670885939474571136049

theorem tailTrace_7567317 : CollatzResearch.WordTrace tailWord_7567317 prefixEnd_7567317 3885670885939474571136049 := by
  unfold tailWord_7567317
  simp only [CollatzResearch.WordTrace]
  refine ⟨276002725525910378695900205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184001817017273585797266803 276002725525910378695900205)
  ·
    refine ⟨103501022072216392010962577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276002725525910378695900205 103501022072216392010962577)
    ·
      refine ⟨77625766554162294008221933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103501022072216392010962577 77625766554162294008221933)
      ·
        refine ⟨29109662457810860253083225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77625766554162294008221933 29109662457810860253083225)
        ·
          refine ⟨21832246843358145189812419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29109662457810860253083225 21832246843358145189812419)
          ·
            refine ⟨32748370265037217784718629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21832246843358145189812419 32748370265037217784718629)
            ·
              refine ⟨6140319424694478334634743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32748370265037217784718629 6140319424694478334634743)
              ·
                refine ⟨9210479137041717501952115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140319424694478334634743 9210479137041717501952115)
                ·
                  refine ⟨13815718705562576252928173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210479137041717501952115 13815718705562576252928173)
                  ·
                    refine ⟨5180894514585966094848065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13815718705562576252928173 5180894514585966094848065)
                    ·
                      refine ⟨3885670885939474571136049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5180894514585966094848065 3885670885939474571136049)
                      ·
                        rfl

theorem cell23_7567317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_7567317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567317 prefixEnd_7567317 := by exact prefixLift 7567317
  have htrace : WordTrace (prefixWord ++ tailWord_7567317) baseStart_7567317 baseEnd_7567317 := by
    simpa [prefixWord, tailWord_7567317, baseEnd_7567317] using wordTrace_append hprefix tailTrace_7567317
  have hstable : (prefixWord ++ tailWord_7567317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567317).length < 2 ^ (prefixWord ++ tailWord_7567317).sum := by decide
  have hdescent : baseEnd_7567317 < baseStart_7567317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567319 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 9]
def baseStart_7567319 : Nat := 118140960795 + 7567319 * 2 ^ 59
def prefixEnd_7567319 : Nat := 4983230072969 + 3 ^ 40 * 7567319 * 2
def baseEnd_7567319 : Nat := 431741323655642618145671

theorem tailTrace_7567319 : CollatzResearch.WordTrace tailWord_7567319 prefixEnd_7567319 431741323655642618145671 := by
  unfold tailWord_7567319
  simp only [CollatzResearch.WordTrace]
  refine ⟨276002798471903133037473011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184001865647935422024982007 276002798471903133037473011)
  ·
    refine ⟨414004197707854699556209517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276002798471903133037473011 414004197707854699556209517)
    ·
      refine ⟨155251574140445512333578569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414004197707854699556209517 155251574140445512333578569)
      ·
        refine ⟨116438680605334134250183927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155251574140445512333578569 116438680605334134250183927)
        ·
          refine ⟨174658020908001201375275891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116438680605334134250183927 174658020908001201375275891)
          ·
            refine ⟨261987031362001802062913837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174658020908001201375275891 261987031362001802062913837)
            ·
              refine ⟨98245136760750675773592689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261987031362001802062913837 98245136760750675773592689)
              ·
                refine ⟨73683852570563006830194517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98245136760750675773592689 73683852570563006830194517)
                ·
                  refine ⟨431741323655642618145671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73683852570563006830194517 431741323655642618145671)
                  ·
                    rfl

theorem cell23_7567319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 9].length) (baseStart_7567319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567319 prefixEnd_7567319 := by exact prefixLift 7567319
  have htrace : WordTrace (prefixWord ++ tailWord_7567319) baseStart_7567319 baseEnd_7567319 := by
    simpa [prefixWord, tailWord_7567319, baseEnd_7567319] using wordTrace_append hprefix tailTrace_7567319
  have hstable : (prefixWord ++ tailWord_7567319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567319).length < 2 ^ (prefixWord ++ tailWord_7567319).sum := by decide
  have hdescent : baseEnd_7567319 < baseStart_7567319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567324 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7567324 : Nat := 118140960795 + 7567324 * 2 ^ 59
def prefixEnd_7567324 : Nat := 4983230072969 + 3 ^ 40 * 7567324 * 2
def baseEnd_7567324 : Nat := 3885674480304056043748517

theorem tailTrace_7567324 : CollatzResearch.WordTrace tailWord_7567324 prefixEnd_7567324 3885674480304056043748517 := by
  unfold tailWord_7567324
  simp only [CollatzResearch.WordTrace]
  refine ⟨138001490418442509445702513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184001987224590012594270017 138001490418442509445702513)
  ·
    refine ⟨103501117813831882084276885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138001490418442509445702513 103501117813831882084276885)
    ·
      refine ⟨4851614897523369472700479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103501117813831882084276885 4851614897523369472700479)
      ·
        refine ⟨7277422346285054209050719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851614897523369472700479 7277422346285054209050719)
        ·
          refine ⟨10916133519427581313576079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277422346285054209050719 10916133519427581313576079)
          ·
            refine ⟨16374200279141371970364119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916133519427581313576079 16374200279141371970364119)
            ·
              refine ⟨24561300418712057955546179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16374200279141371970364119 24561300418712057955546179)
              ·
                refine ⟨36841950628068086933319269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24561300418712057955546179 36841950628068086933319269)
                ·
                  refine ⟨6907865742762766299997363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36841950628068086933319269 6907865742762766299997363)
                  ·
                    refine ⟨10361798614144149449996045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907865742762766299997363 10361798614144149449996045)
                    ·
                      refine ⟨3885674480304056043748517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361798614144149449996045 3885674480304056043748517)
                      ·
                        rfl

theorem cell23_7567324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7567324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567324 prefixEnd_7567324 := by exact prefixLift 7567324
  have htrace : WordTrace (prefixWord ++ tailWord_7567324) baseStart_7567324 baseEnd_7567324 := by
    simpa [prefixWord, tailWord_7567324, baseEnd_7567324] using wordTrace_append hprefix tailTrace_7567324
  have hstable : (prefixWord ++ tailWord_7567324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567324).length < 2 ^ (prefixWord ++ tailWord_7567324).sum := by decide
  have hdescent : baseEnd_7567324 < baseStart_7567324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567393 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_7567393 : Nat := 118140960795 + 7567393 * 2 ^ 59
def prefixEnd_7567393 : Nat := 4983230072969 + 3 ^ 40 * 7567393 * 2
def baseEnd_7567393 : Nat := 3885709910469216273785699

theorem tailTrace_7567393 : CollatzResearch.WordTrace tailWord_7567393 prefixEnd_7567393 3885709910469216273785699 := by
  unfold tailWord_7567393
  simp only [CollatzResearch.WordTrace]
  refine ⟨276005497473635043675666833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184003664982423362450444555 276005497473635043675666833)
  ·
    refine ⟨207004123105226282756750125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276005497473635043675666833 207004123105226282756750125)
    ·
      refine ⟨77626546164459856033781297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207004123105226282756750125 77626546164459856033781297)
      ·
        refine ⟨58219909623344892025335973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77626546164459856033781297 58219909623344892025335973)
        ·
          refine ⟨10916233054377167254750495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58219909623344892025335973 10916233054377167254750495)
          ·
            refine ⟨16374349581565750882125743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916233054377167254750495 16374349581565750882125743)
            ·
              refine ⟨24561524372348626323188615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16374349581565750882125743 24561524372348626323188615)
              ·
                refine ⟨36842286558522939484782923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24561524372348626323188615 36842286558522939484782923)
                ·
                  refine ⟨55263429837784409227174385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36842286558522939484782923 55263429837784409227174385)
                  ·
                    refine ⟨41447572378338306920380789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55263429837784409227174385 41447572378338306920380789)
                    ·
                      refine ⟨3885709910469216273785699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41447572378338306920380789 3885709910469216273785699)
                      ·
                        rfl

theorem cell23_7567393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_7567393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567393 prefixEnd_7567393 := by exact prefixLift 7567393
  have htrace : WordTrace (prefixWord ++ tailWord_7567393) baseStart_7567393 baseEnd_7567393 := by
    simpa [prefixWord, tailWord_7567393, baseEnd_7567393] using wordTrace_append hprefix tailTrace_7567393
  have hstable : (prefixWord ++ tailWord_7567393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567393).length < 2 ^ (prefixWord ++ tailWord_7567393).sum := by decide
  have hdescent : baseEnd_7567393 < baseStart_7567393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567413 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7567413 : Nat := 118140960795 + 7567413 * 2 ^ 59
def prefixEnd_7567413 : Nat := 4983230072969 + 3 ^ 40 * 7567413 * 2
def baseEnd_7567413 : Nat := 1295240060027435398511869

theorem tailTrace_7567413 : CollatzResearch.WordTrace tailWord_7567413 prefixEnd_7567413 1295240060027435398511869 := by
  unfold tailWord_7567413
  simp only [CollatzResearch.WordTrace]
  refine ⟨276006226933562587091394893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184004151289041724727596595 276006226933562587091394893)
  ·
    refine ⟨103502335100085970159273085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276006226933562587091394893 103502335100085970159273085)
    ·
      refine ⟨38813375662532238809727407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103502335100085970159273085 38813375662532238809727407)
      ·
        refine ⟨58220063493798358214591111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38813375662532238809727407 58220063493798358214591111)
        ·
          refine ⟨87330095240697537321886667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58220063493798358214591111 87330095240697537321886667)
          ·
            refine ⟨130995142861046305982830001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87330095240697537321886667 130995142861046305982830001)
            ·
              refine ⟨98246357145784729487122501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130995142861046305982830001 98246357145784729487122501)
              ·
                refine ⟨18421191964834636778835469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98246357145784729487122501 18421191964834636778835469)
                ·
                  refine ⟨6907946986812988792063301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18421191964834636778835469 6907946986812988792063301)
                  ·
                    refine ⟨1295240060027435398511869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907946986812988792063301 1295240060027435398511869)
                    ·
                      rfl

theorem cell23_7567413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7567413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567413 prefixEnd_7567413 := by exact prefixLift 7567413
  have htrace : WordTrace (prefixWord ++ tailWord_7567413) baseStart_7567413 baseEnd_7567413 := by
    simpa [prefixWord, tailWord_7567413, baseEnd_7567413] using wordTrace_append hprefix tailTrace_7567413
  have hstable : (prefixWord ++ tailWord_7567413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567413).length < 2 ^ (prefixWord ++ tailWord_7567413).sum := by decide
  have hdescent : baseEnd_7567413 < baseStart_7567413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567423 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_7567423 : Nat := 118140960795 + 7567423 * 2 ^ 59
def prefixEnd_7567423 : Nat := 4983230072969 + 3 ^ 40 * 7567423 * 2
def baseEnd_7567423 : Nat := 3885725314888851156410561

theorem tailTrace_7567423 : CollatzResearch.WordTrace tailWord_7567423 prefixEnd_7567423 3885725314888851156410561 := by
  unfold tailWord_7567423
  simp only [CollatzResearch.WordTrace]
  refine ⟨276006591663526358799258923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184004394442350905866172615 276006591663526358799258923)
  ·
    refine ⟨414009887495289538198888385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276006591663526358799258923 414009887495289538198888385)
    ·
      refine ⟨310507415621467153649166289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414009887495289538198888385 310507415621467153649166289)
      ·
        refine ⟨232880561716100365236874717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310507415621467153649166289 232880561716100365236874717)
        ·
          refine ⟨87330210643537636963828019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232880561716100365236874717 87330210643537636963828019)
          ·
            refine ⟨130995315965306455445742029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87330210643537636963828019 130995315965306455445742029)
            ·
              refine ⟨49123243486989920792153261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130995315965306455445742029 49123243486989920792153261)
              ·
                refine ⟨18421216307621220297057473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49123243486989920792153261 18421216307621220297057473)
                ·
                  refine ⟨13815912230715915222793105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18421216307621220297057473 13815912230715915222793105)
                  ·
                    refine ⟨10361934173036936417094829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13815912230715915222793105 10361934173036936417094829)
                    ·
                      refine ⟨3885725314888851156410561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10361934173036936417094829 3885725314888851156410561)
                      ·
                        rfl

theorem cell23_7567423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_7567423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567423 prefixEnd_7567423 := by exact prefixLift 7567423
  have htrace : WordTrace (prefixWord ++ tailWord_7567423) baseStart_7567423 baseEnd_7567423 := by
    simpa [prefixWord, tailWord_7567423, baseEnd_7567423] using wordTrace_append hprefix tailTrace_7567423
  have hstable : (prefixWord ++ tailWord_7567423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567423).length < 2 ^ (prefixWord ++ tailWord_7567423).sum := by decide
  have hdescent : baseEnd_7567423 < baseStart_7567423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567447 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 1, 4]
def baseStart_7567447 : Nat := 118140960795 + 7567447 * 2 ^ 59
def prefixEnd_7567447 : Nat := 4983230072969 + 3 ^ 40 * 7567447 * 2
def baseEnd_7567447 : Nat := 1295245879474853020836817

theorem tailTrace_7567447 : CollatzResearch.WordTrace tailWord_7567447 prefixEnd_7567447 1295245879474853020836817 := by
  unfold tailWord_7567447
  simp only [CollatzResearch.WordTrace]
  refine ⟨276007467015439410898132595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184004978010292940598755063 276007467015439410898132595)
  ·
    refine ⟨414011200523159116347198893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276007467015439410898132595 414011200523159116347198893)
    ·
      refine ⟨155254200196184668630199585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414011200523159116347198893 155254200196184668630199585)
      ·
        refine ⟨116440650147138501472649689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155254200196184668630199585 116440650147138501472649689)
        ·
          refine ⟨87330487610353876104487267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116440650147138501472649689 87330487610353876104487267)
          ·
            refine ⟨130995731415530814156730901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87330487610353876104487267 130995731415530814156730901)
            ·
              refine ⟨6140424910103006913596761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130995731415530814156730901 6140424910103006913596761)
              ·
                refine ⟨4605318682577255185197571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6140424910103006913596761 4605318682577255185197571)
                ·
                  refine ⟨6907978023865882777796357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605318682577255185197571 6907978023865882777796357)
                  ·
                    refine ⟨1295245879474853020836817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907978023865882777796357 1295245879474853020836817)
                    ·
                      rfl

theorem cell23_7567447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_7567447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567447 prefixEnd_7567447 := by exact prefixLift 7567447
  have htrace : WordTrace (prefixWord ++ tailWord_7567447) baseStart_7567447 baseEnd_7567447 := by
    simpa [prefixWord, tailWord_7567447, baseEnd_7567447] using wordTrace_append hprefix tailTrace_7567447
  have hstable : (prefixWord ++ tailWord_7567447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567447).length < 2 ^ (prefixWord ++ tailWord_7567447).sum := by decide
  have hdescent : baseEnd_7567447 < baseStart_7567447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567473 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 1, 5]
def baseStart_7567473 : Nat := 118140960795 + 7567473 * 2 ^ 59
def prefixEnd_7567473 : Nat := 4983230072969 + 3 ^ 40 * 7567473 * 2
def baseEnd_7567473 : Nat := 1295250329640525320261777

theorem tailTrace_7567473 : CollatzResearch.WordTrace tailWord_7567473 prefixEnd_7567473 1295250329640525320261777 := by
  unfold tailWord_7567473
  simp only [CollatzResearch.WordTrace]
  refine ⟨276008415313345217338579073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184005610208896811559052715 276008415313345217338579073)
  ·
    refine ⟨207006311485008913003934305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276008415313345217338579073 207006311485008913003934305)
    ·
      refine ⟨155254733613756684752950729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207006311485008913003934305 155254733613756684752950729)
      ·
        refine ⟨116441050210317513564713047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155254733613756684752950729 116441050210317513564713047)
        ·
          refine ⟨174661575315476270347069571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116441050210317513564713047 174661575315476270347069571)
          ·
            refine ⟨261992362973214405520604357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174661575315476270347069571 261992362973214405520604357)
            ·
              refine ⟨49123568057477701035113317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261992362973214405520604357 49123568057477701035113317)
              ·
                refine ⟨9210669010777068944083747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49123568057477701035113317 9210669010777068944083747)
                ·
                  refine ⟨13816003516165603416125621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210669010777068944083747 13816003516165603416125621)
                  ·
                    refine ⟨1295250329640525320261777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13816003516165603416125621 1295250329640525320261777)
                    ·
                      rfl

theorem cell23_7567473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_7567473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567473 prefixEnd_7567473 := by exact prefixLift 7567473
  have htrace : WordTrace (prefixWord ++ tailWord_7567473) baseStart_7567473 baseEnd_7567473 := by
    simpa [prefixWord, tailWord_7567473, baseEnd_7567473] using wordTrace_append hprefix tailTrace_7567473
  have hstable : (prefixWord ++ tailWord_7567473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567473).length < 2 ^ (prefixWord ++ tailWord_7567473).sum := by decide
  have hdescent : baseEnd_7567473 < baseStart_7567473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567513 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_7567513 : Nat := 118140960795 + 7567513 * 2 ^ 59
def prefixEnd_7567513 : Nat := 4983230072969 + 3 ^ 40 * 7567513 * 2
def baseEnd_7567513 : Nat := 3885771528147755804285147

theorem tailTrace_7567513 : CollatzResearch.WordTrace tailWord_7567513 prefixEnd_7567513 3885771528147755804285147 := by
  unfold tailWord_7567513
  simp only [CollatzResearch.WordTrace]
  refine ⟨276009874233200304170035193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184006582822133536113356795 276009874233200304170035193)
  ·
    refine ⟨207007405674900228127526395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276009874233200304170035193 207007405674900228127526395)
    ·
      refine ⟨310511108512350342191289593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207007405674900228127526395 310511108512350342191289593)
      ·
        refine ⟨232883331384262756643467195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310511108512350342191289593 232883331384262756643467195)
        ·
          refine ⟨349324997076394134965200793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232883331384262756643467195 349324997076394134965200793)
          ·
            refine ⟨261993747807295601223900595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349324997076394134965200793 261993747807295601223900595)
            ·
              refine ⟨392990621710943401835850893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261993747807295601223900595 392990621710943401835850893)
              ·
                refine ⟨147371483141603775688444085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392990621710943401835850893 147371483141603775688444085)
                ·
                  refine ⟨13816076544525353970791633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147371483141603775688444085 13816076544525353970791633)
                  ·
                    refine ⟨10362057408394015478093725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13816076544525353970791633 10362057408394015478093725)
                    ·
                      refine ⟨3885771528147755804285147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362057408394015478093725 3885771528147755804285147)
                      ·
                        rfl

theorem cell23_7567513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_7567513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567513 prefixEnd_7567513 := by exact prefixLift 7567513
  have htrace : WordTrace (prefixWord ++ tailWord_7567513) baseStart_7567513 baseEnd_7567513 := by
    simpa [prefixWord, tailWord_7567513, baseEnd_7567513] using wordTrace_append hprefix tailTrace_7567513
  have hstable : (prefixWord ++ tailWord_7567513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567513).length < 2 ^ (prefixWord ++ tailWord_7567513).sum := by decide
  have hdescent : baseEnd_7567513 < baseStart_7567513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567520 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 1, 6]
def baseStart_7567520 : Nat := 118140960795 + 7567520 * 2 ^ 59
def prefixEnd_7567520 : Nat := 4983230072969 + 3 ^ 40 * 7567520 * 2
def baseEnd_7567520 : Nat := 1295258374170779092299205

theorem tailTrace_7567520 : CollatzResearch.WordTrace tailWord_7567520 prefixEnd_7567520 1295258374170779092299205 := by
  unfold tailWord_7567520
  simp only [CollatzResearch.WordTrace]
  refine ⟨138005064772087472182770007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184006753029449962910360009 138005064772087472182770007)
  ·
    refine ⟨207007597158131208274155011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138005064772087472182770007 207007597158131208274155011)
    ·
      refine ⟨310511395737196812411232517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207007597158131208274155011 310511395737196812411232517)
      ·
        refine ⟨58220886700724402327106097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310511395737196812411232517 58220886700724402327106097)
        ·
          refine ⟨43665665025543301745329573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58220886700724402327106097 43665665025543301745329573)
          ·
            refine ⟨8187312192289369077249295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43665665025543301745329573 8187312192289369077249295)
            ·
              refine ⟨12280968288434053615873943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187312192289369077249295 12280968288434053615873943)
              ·
                refine ⟨18421452432651080423810915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12280968288434053615873943 18421452432651080423810915)
                ·
                  refine ⟨27632178648976620635716373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18421452432651080423810915 27632178648976620635716373)
                  ·
                    refine ⟨1295258374170779092299205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27632178648976620635716373 1295258374170779092299205)
                    ·
                      rfl

theorem cell23_7567520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_7567520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567520 prefixEnd_7567520 := by exact prefixLift 7567520
  have htrace : WordTrace (prefixWord ++ tailWord_7567520) baseStart_7567520 baseEnd_7567520 := by
    simpa [prefixWord, tailWord_7567520, baseEnd_7567520] using wordTrace_append hprefix tailTrace_7567520
  have hstable : (prefixWord ++ tailWord_7567520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567520).length < 2 ^ (prefixWord ++ tailWord_7567520).sum := by decide
  have hdescent : baseEnd_7567520 < baseStart_7567520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567550 : List Nat := [4, 2, 1, 1, 4, 2, 9]
def baseStart_7567550 : Nat := 118140960795 + 7567550 * 2 ^ 59
def prefixEnd_7567550 : Nat := 4983230072969 + 3 ^ 40 * 7567550 * 2
def baseEnd_7567550 : Nat := 47972722554715705673117

theorem tailTrace_7567550 : CollatzResearch.WordTrace tailWord_7567550 prefixEnd_7567550 47972722554715705673117 := by
  unfold tailWord_7567550
  simp only [CollatzResearch.WordTrace]
  refine ⟨34501402966758282436141513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184007482489377506326088069 34501402966758282436141513)
  ·
    refine ⟨25876052225068711827106135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34501402966758282436141513 25876052225068711827106135)
    ·
      refine ⟨38814078337603067740659203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25876052225068711827106135 38814078337603067740659203)
      ·
        refine ⟨58221117506404601610988805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38814078337603067740659203 58221117506404601610988805)
        ·
          refine ⟨10916459532450862802060401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58221117506404601610988805 10916459532450862802060401)
          ·
            refine ⟨8187344649338147101545301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10916459532450862802060401 8187344649338147101545301)
            ·
              refine ⟨47972722554715705673117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8187344649338147101545301 47972722554715705673117)
              ·
                rfl

theorem cell23_7567550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 9].length) (baseStart_7567550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567550 prefixEnd_7567550 := by exact prefixLift 7567550
  have htrace : WordTrace (prefixWord ++ tailWord_7567550) baseStart_7567550 baseEnd_7567550 := by
    simpa [prefixWord, tailWord_7567550, baseEnd_7567550] using wordTrace_append hprefix tailTrace_7567550
  have hstable : (prefixWord ++ tailWord_7567550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567550).length < 2 ^ (prefixWord ++ tailWord_7567550).sum := by decide
  have hdescent : baseEnd_7567550 < baseStart_7567550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567554 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_7567554 : Nat := 118140960795 + 7567554 * 2 ^ 59
def prefixEnd_7567554 : Nat := 4983230072969 + 3 ^ 40 * 7567554 * 2
def baseEnd_7567554 : Nat := 1295264193618196714624153

theorem tailTrace_7567554 : CollatzResearch.WordTrace tailWord_7567554 prefixEnd_7567554 1295264193618196714624153 := by
  unfold tailWord_7567554
  simp only [CollatzResearch.WordTrace]
  refine ⟨69002842406512942043069429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184007579750701178781518477 69002842406512942043069429)
  ·
    refine ⟨6469016475610588316537759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69002842406512942043069429 6469016475610588316537759)
    ·
      refine ⟨9703524713415882474806639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469016475610588316537759 9703524713415882474806639)
      ·
        refine ⟨14555287070123823712209959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703524713415882474806639 14555287070123823712209959)
        ·
          refine ⟨21832930605185735568314939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14555287070123823712209959 21832930605185735568314939)
          ·
            refine ⟨32749395907778603352472409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21832930605185735568314939 32749395907778603352472409)
            ·
              refine ⟨24562046930833952514354307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32749395907778603352472409 24562046930833952514354307)
              ·
                refine ⟨36843070396250928771531461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24562046930833952514354307 36843070396250928771531461)
                ·
                  refine ⟨6908075699297049144662149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36843070396250928771531461 6908075699297049144662149)
                  ·
                    refine ⟨1295264193618196714624153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6908075699297049144662149 1295264193618196714624153)
                    ·
                      rfl

theorem cell23_7567554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_7567554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567554 prefixEnd_7567554 := by exact prefixLift 7567554
  have htrace : WordTrace (prefixWord ++ tailWord_7567554) baseStart_7567554 baseEnd_7567554 := by
    simpa [prefixWord, tailWord_7567554, baseEnd_7567554] using wordTrace_append hprefix tailTrace_7567554
  have hstable : (prefixWord ++ tailWord_7567554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567554).length < 2 ^ (prefixWord ++ tailWord_7567554).sum := by decide
  have hdescent : baseEnd_7567554 < baseStart_7567554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567603 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5]
def baseStart_7567603 : Nat := 118140960795 + 7567603 * 2 ^ 59
def prefixEnd_7567603 : Nat := 4983230072969 + 3 ^ 40 * 7567603 * 2
def baseEnd_7567603 : Nat := 3885817741406660452159733

theorem tailTrace_7567603 : CollatzResearch.WordTrace tailWord_7567603 prefixEnd_7567603 3885817741406660452159733 := by
  unfold tailWord_7567603
  simp only [CollatzResearch.WordTrace]
  refine ⟨276013156802874249540811463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184008771201916166360540975 276013156802874249540811463)
  ·
    refine ⟨414019735204311374311217195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276013156802874249540811463 414019735204311374311217195)
    ·
      refine ⟨621029602806467061466825793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414019735204311374311217195 621029602806467061466825793)
      ·
        refine ⟨465772202104850296100119345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621029602806467061466825793 465772202104850296100119345)
        ·
          refine ⟨349329151578637722075089509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465772202104850296100119345 349329151578637722075089509)
          ·
            refine ⟨65499215920994572889079283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349329151578637722075089509 65499215920994572889079283)
            ·
              refine ⟨98248823881491859333618925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65499215920994572889079283 98248823881491859333618925)
              ·
                refine ⟨36843308955559447250107097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98248823881491859333618925 36843308955559447250107097)
                ·
                  refine ⟨27632481716669585437580323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36843308955559447250107097 27632481716669585437580323)
                  ·
                    refine ⟨41448722575004378156370485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27632481716669585437580323 41448722575004378156370485)
                    ·
                      refine ⟨3885817741406660452159733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41448722575004378156370485 3885817741406660452159733)
                      ·
                        rfl

theorem cell23_7567603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_7567603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567603 prefixEnd_7567603 := by exact prefixLift 7567603
  have htrace : WordTrace (prefixWord ++ tailWord_7567603) baseStart_7567603 baseEnd_7567603 := by
    simpa [prefixWord, tailWord_7567603, baseEnd_7567603] using wordTrace_append hprefix tailTrace_7567603
  have hstable : (prefixWord ++ tailWord_7567603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567603).length < 2 ^ (prefixWord ++ tailWord_7567603).sum := by decide
  have hdescent : baseEnd_7567603 < baseStart_7567603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567613 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_7567613 : Nat := 118140960795 + 7567613 * 2 ^ 59
def prefixEnd_7567613 : Nat := 4983230072969 + 3 ^ 40 * 7567613 * 2
def baseEnd_7567613 : Nat := 3885822876213205413034687

theorem tailTrace_7567613 : CollatzResearch.WordTrace tailWord_7567613 prefixEnd_7567613 3885822876213205413034687 := by
  unfold tailWord_7567613
  simp only [CollatzResearch.WordTrace]
  refine ⟨276013521532838021248675493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184009014355225347499116995 276013521532838021248675493)
  ·
    refine ⟨51752535287407128984126655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276013521532838021248675493 51752535287407128984126655)
    ·
      refine ⟨77628802931110693476189983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51752535287407128984126655 77628802931110693476189983)
      ·
        refine ⟨116443204396666040214284975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77628802931110693476189983 116443204396666040214284975)
        ·
          refine ⟨174664806594999060321427463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116443204396666040214284975 174664806594999060321427463)
          ·
            refine ⟨261997209892498590482141195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174664806594999060321427463 261997209892498590482141195)
            ·
              refine ⟨392995814838747885723211793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261997209892498590482141195 392995814838747885723211793)
              ·
                refine ⟨294746861129060914292408845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392995814838747885723211793 294746861129060914292408845)
                ·
                  refine ⟨110530072923397842859653317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294746861129060914292408845 110530072923397842859653317)
                  ·
                    refine ⟨20724388673137095536184997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110530072923397842859653317 20724388673137095536184997)
                    ·
                      refine ⟨3885822876213205413034687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20724388673137095536184997 3885822876213205413034687)
                      ·
                        rfl

theorem cell23_7567613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_7567613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567613 prefixEnd_7567613 := by exact prefixLift 7567613
  have htrace : WordTrace (prefixWord ++ tailWord_7567613) baseStart_7567613 baseEnd_7567613 := by
    simpa [prefixWord, tailWord_7567613, baseEnd_7567613] using wordTrace_append hprefix tailTrace_7567613
  have hstable : (prefixWord ++ tailWord_7567613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567613).length < 2 ^ (prefixWord ++ tailWord_7567613).sum := by decide
  have hdescent : baseEnd_7567613 < baseStart_7567613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567630 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7567630 : Nat := 118140960795 + 7567630 * 2 ^ 59
def prefixEnd_7567630 : Nat := 4983230072969 + 3 ^ 40 * 7567630 * 2
def baseEnd_7567630 : Nat := 3885831605384331846522109

theorem tailTrace_7567630 : CollatzResearch.WordTrace tailWord_7567630 prefixEnd_7567630 3885831605384331846522109 := by
  unfold tailWord_7567630
  simp only [CollatzResearch.WordTrace]
  refine ⟨34501767696722054144005543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184009427715850955434696229 34501767696722054144005543)
  ·
    refine ⟨51752651545083081216008315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34501767696722054144005543 51752651545083081216008315)
    ·
      refine ⟨77628977317624621824012473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51752651545083081216008315 77628977317624621824012473)
      ·
        refine ⟨58221732988218466368009355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77628977317624621824012473 58221732988218466368009355)
        ·
          refine ⟨87332599482327699552014033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58221732988218466368009355 87332599482327699552014033)
          ·
            refine ⟨65499449611745774664010525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87332599482327699552014033 65499449611745774664010525)
            ·
              refine ⟨24562293604404665499003947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65499449611745774664010525 24562293604404665499003947)
              ·
                refine ⟨36843440406606998248505921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24562293604404665499003947 36843440406606998248505921)
                ·
                  refine ⟨27632580304955248686379441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36843440406606998248505921 27632580304955248686379441)
                  ·
                    refine ⟨20724435228716436514784581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27632580304955248686379441 20724435228716436514784581)
                    ·
                      refine ⟨3885831605384331846522109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20724435228716436514784581 3885831605384331846522109)
                      ·
                        rfl

theorem cell23_7567630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7567630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567630 prefixEnd_7567630 := by exact prefixLift 7567630
  have htrace : WordTrace (prefixWord ++ tailWord_7567630) baseStart_7567630 baseEnd_7567630 := by
    simpa [prefixWord, tailWord_7567630, baseEnd_7567630] using wordTrace_append hprefix tailTrace_7567630
  have hstable : (prefixWord ++ tailWord_7567630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567630).length < 2 ^ (prefixWord ++ tailWord_7567630).sum := by decide
  have hdescent : baseEnd_7567630 < baseStart_7567630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567663 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_7567663 : Nat := 118140960795 + 7567663 * 2 ^ 59
def prefixEnd_7567663 : Nat := 4983230072969 + 3 ^ 40 * 7567663 * 2
def baseEnd_7567663 : Nat := 3885848550245930217409457

theorem tailTrace_7567663 : CollatzResearch.WordTrace tailWord_7567663 prefixEnd_7567663 3885848550245930217409457 := by
  unfold tailWord_7567663
  simp only [CollatzResearch.WordTrace]
  refine ⟨276015345182656879787995643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184010230121771253191997095 276015345182656879787995643)
  ·
    refine ⟨414023017773985319681993465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276015345182656879787995643 414023017773985319681993465)
    ·
      refine ⟨310517263330488989761495099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414023017773985319681993465 310517263330488989761495099)
      ·
        refine ⟨465775894995733484642242649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310517263330488989761495099 465775894995733484642242649)
        ·
          refine ⟨349331921246800113481681987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465775894995733484642242649 349331921246800113481681987)
          ·
            refine ⟨523997881870200170222522981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349331921246800113481681987 523997881870200170222522981)
            ·
              refine ⟨98249602850662531916723059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 523997881870200170222522981 98249602850662531916723059)
              ·
                refine ⟨147374404275993797875084589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98249602850662531916723059 147374404275993797875084589)
                ·
                  refine ⟨55265401603497674203156721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147374404275993797875084589 55265401603497674203156721)
                  ·
                    refine ⟨41449051202623255652367541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55265401603497674203156721 41449051202623255652367541)
                    ·
                      refine ⟨3885848550245930217409457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41449051202623255652367541 3885848550245930217409457)
                      ·
                        rfl

theorem cell23_7567663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_7567663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567663 prefixEnd_7567663 := by exact prefixLift 7567663
  have htrace : WordTrace (prefixWord ++ tailWord_7567663) baseStart_7567663 baseEnd_7567663 := by
    simpa [prefixWord, tailWord_7567663, baseEnd_7567663] using wordTrace_append hprefix tailTrace_7567663
  have hstable : (prefixWord ++ tailWord_7567663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567663).length < 2 ^ (prefixWord ++ tailWord_7567663).sum := by decide
  have hdescent : baseEnd_7567663 < baseStart_7567663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567668 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_7567668 : Nat := 118140960795 + 7567668 * 2 ^ 59
def prefixEnd_7567668 : Nat := 4983230072969 + 3 ^ 40 * 7567668 * 2
def baseEnd_7567668 : Nat := 3885851117649202697846935

theorem tailTrace_7567668 : CollatzResearch.WordTrace tailWord_7567668 prefixEnd_7567668 3885851117649202697846935 := by
  unfold tailWord_7567668
  simp only [CollatzResearch.WordTrace]
  refine ⟨138007763773819382820963829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184010351698425843761285105 138007763773819382820963829)
  ·
    refine ⟨12938227853795567139465359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138007763773819382820963829 12938227853795567139465359)
    ·
      refine ⟨19407341780693350709198039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12938227853795567139465359 19407341780693350709198039)
      ·
        refine ⟨29111012671040026063797059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19407341780693350709198039 29111012671040026063797059)
        ·
          refine ⟨43666519006560039095695589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29111012671040026063797059 43666519006560039095695589)
          ·
            refine ⟨8187472313730007330442923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43666519006560039095695589 8187472313730007330442923)
            ·
              refine ⟨12281208470595010995664385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187472313730007330442923 12281208470595010995664385)
              ·
                refine ⟨9210906352946258246748289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12281208470595010995664385 9210906352946258246748289)
                ·
                  refine ⟨6908179764709693685061217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9210906352946258246748289 6908179764709693685061217)
                  ·
                    refine ⟨5181134823532270263795913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6908179764709693685061217 5181134823532270263795913)
                    ·
                      refine ⟨3885851117649202697846935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181134823532270263795913 3885851117649202697846935)
                      ·
                        rfl

theorem cell23_7567668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_7567668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567668 prefixEnd_7567668 := by exact prefixLift 7567668
  have htrace : WordTrace (prefixWord ++ tailWord_7567668) baseStart_7567668 baseEnd_7567668 := by
    simpa [prefixWord, tailWord_7567668, baseEnd_7567668] using wordTrace_append hprefix tailTrace_7567668
  have hstable : (prefixWord ++ tailWord_7567668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567668).length < 2 ^ (prefixWord ++ tailWord_7567668).sum := by decide
  have hdescent : baseEnd_7567668 < baseStart_7567668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567708 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 5]
def baseStart_7567708 : Nat := 118140960795 + 7567708 * 2 ^ 59
def prefixEnd_7567708 : Nat := 4983230072969 + 3 ^ 40 * 7567708 * 2
def baseEnd_7567708 : Nat := 431763517430598060149639

theorem tailTrace_7567708 : CollatzResearch.WordTrace tailWord_7567708 prefixEnd_7567708 431763517430598060149639 := by
  unfold tailWord_7567708
  simp only [CollatzResearch.WordTrace]
  refine ⟨138008493233746926236691889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184011324311662568315589185 138008493233746926236691889)
  ·
    refine ⟨103506369925310194677518917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138008493233746926236691889 103506369925310194677518917)
    ·
      refine ⟨19407444360995661502034797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103506369925310194677518917 19407444360995661502034797)
      ·
        refine ⟨7277791635373373063263049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19407444360995661502034797 7277791635373373063263049)
        ·
          refine ⟨5458343726530029797447287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277791635373373063263049 5458343726530029797447287)
          ·
            refine ⟨8187515589795044696170931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458343726530029797447287 8187515589795044696170931)
            ·
              refine ⟨12281273384692567044256397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187515589795044696170931 12281273384692567044256397)
              ·
                refine ⟨4605477519259712641596149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12281273384692567044256397 4605477519259712641596149)
                ·
                  refine ⟨431763517430598060149639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4605477519259712641596149 431763517430598060149639)
                  ·
                    rfl

theorem cell23_7567708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_7567708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567708 prefixEnd_7567708 := by exact prefixLift 7567708
  have htrace : WordTrace (prefixWord ++ tailWord_7567708) baseStart_7567708 baseEnd_7567708 := by
    simpa [prefixWord, tailWord_7567708, baseEnd_7567708] using wordTrace_append hprefix tailTrace_7567708
  have hstable : (prefixWord ++ tailWord_7567708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567708).length < 2 ^ (prefixWord ++ tailWord_7567708).sum := by decide
  have hdescent : baseEnd_7567708 < baseStart_7567708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567730 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_7567730 : Nat := 118140960795 + 7567730 * 2 ^ 59
def prefixEnd_7567730 : Nat := 4983230072969 + 3 ^ 40 * 7567730 * 2
def baseEnd_7567730 : Nat := 431764772605531272807961

theorem tailTrace_7567730 : CollatzResearch.WordTrace tailWord_7567730 prefixEnd_7567730 431764772605531272807961 := by
  unfold tailWord_7567730
  simp only [CollatzResearch.WordTrace]
  refine ⟨69004447218353537557671161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184011859248942766820456429 69004447218353537557671161)
  ·
    refine ⟨51753335413765153168253371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69004447218353537557671161 51753335413765153168253371)
    ·
      refine ⟨77630003120647729752380057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51753335413765153168253371 77630003120647729752380057)
      ·
        refine ⟨58222502340485797314285043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77630003120647729752380057 58222502340485797314285043)
        ·
          refine ⟨87333753510728695971427565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58222502340485797314285043 87333753510728695971427565)
          ·
            refine ⟨32750157566523260989285337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87333753510728695971427565 32750157566523260989285337)
            ·
              refine ⟨24562618174892445741964003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32750157566523260989285337 24562618174892445741964003)
              ·
                refine ⟨36843927262338668612946005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24562618174892445741964003 36843927262338668612946005)
                ·
                  refine ⟨431764772605531272807961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36843927262338668612946005 431764772605531272807961)
                  ·
                    rfl

theorem cell23_7567730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_7567730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567730 prefixEnd_7567730 := by exact prefixLift 7567730
  have htrace : WordTrace (prefixWord ++ tailWord_7567730) baseStart_7567730 baseEnd_7567730 := by
    simpa [prefixWord, tailWord_7567730, baseEnd_7567730] using wordTrace_append hprefix tailTrace_7567730
  have hstable : (prefixWord ++ tailWord_7567730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567730).length < 2 ^ (prefixWord ++ tailWord_7567730).sum := by decide
  have hdescent : baseEnd_7567730 < baseStart_7567730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567740 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_7567740 : Nat := 118140960795 + 7567740 * 2 ^ 59
def prefixEnd_7567740 : Nat := 4983230072969 + 3 ^ 40 * 7567740 * 2
def baseEnd_7567740 : Nat := 3885888088256326416146603

theorem tailTrace_7567740 : CollatzResearch.WordTrace tailWord_7567740 prefixEnd_7567740 3885888088256326416146603 := by
  unfold tailWord_7567740
  simp only [CollatzResearch.WordTrace]
  refine ⟨138009076801688960969274337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184012102402251947959032449 138009076801688960969274337)
  ·
    refine ⟨103506807601266720726955753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138009076801688960969274337 103506807601266720726955753)
    ·
      refine ⟨77630105700950040545216815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103506807601266720726955753 77630105700950040545216815)
      ·
        refine ⟨116445158551425060817825223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77630105700950040545216815 116445158551425060817825223)
        ·
          refine ⟨174667737827137591226737835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116445158551425060817825223 174667737827137591226737835)
          ·
            refine ⟨262001606740706386840106753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174667737827137591226737835 262001606740706386840106753)
            ·
              refine ⟨196501205055529790130080065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262001606740706386840106753 196501205055529790130080065)
              ·
                refine ⟨147375903791647342597560049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196501205055529790130080065 147375903791647342597560049)
                ·
                  refine ⟨110531927843735506948170037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147375903791647342597560049 110531927843735506948170037)
                  ·
                    refine ⟨10362368235350203776390941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110531927843735506948170037 10362368235350203776390941)
                    ·
                      refine ⟨3885888088256326416146603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362368235350203776390941 3885888088256326416146603)
                      ·
                        rfl

theorem cell23_7567740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_7567740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567740 prefixEnd_7567740 := by exact prefixLift 7567740
  have htrace : WordTrace (prefixWord ++ tailWord_7567740) baseStart_7567740 baseEnd_7567740 := by
    simpa [prefixWord, tailWord_7567740, baseEnd_7567740] using wordTrace_append hprefix tailTrace_7567740
  have hstable : (prefixWord ++ tailWord_7567740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567740).length < 2 ^ (prefixWord ++ tailWord_7567740).sum := by decide
  have hdescent : baseEnd_7567740 < baseStart_7567740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567747 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 6]
def baseStart_7567747 : Nat := 118140960795 + 7567747 * 2 ^ 59
def prefixEnd_7567747 : Nat := 4983230072969 + 3 ^ 40 * 7567747 * 2
def baseEnd_7567747 : Nat := 431765742513434209862119

theorem tailTrace_7567747 : CollatzResearch.WordTrace tailWord_7567747 prefixEnd_7567747 431765742513434209862119 := by
  unfold tailWord_7567747
  simp only [CollatzResearch.WordTrace]
  refine ⟨276018408914352562134053495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184012272609568374756035663 276018408914352562134053495)
  ·
    refine ⟨414027613371528843201080243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276018408914352562134053495 414027613371528843201080243)
    ·
      refine ⟨621041420057293264801620365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414027613371528843201080243 621041420057293264801620365)
      ·
        refine ⟨232890532521484974300607637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621041420057293264801620365 232890532521484974300607637)
        ·
          refine ⟨10916743711944608170340983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232890532521484974300607637 10916743711944608170340983)
          ·
            refine ⟨16375115567916912255511475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916743711944608170340983 16375115567916912255511475)
            ·
              refine ⟨24562673351875368383267213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16375115567916912255511475 24562673351875368383267213)
              ·
                refine ⟨9211002506953263143725205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24562673351875368383267213 9211002506953263143725205)
                ·
                  refine ⟨431765742513434209862119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9211002506953263143725205 431765742513434209862119)
                  ·
                    rfl

theorem cell23_7567747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 6].length) (baseStart_7567747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567747 prefixEnd_7567747 := by exact prefixLift 7567747
  have htrace : WordTrace (prefixWord ++ tailWord_7567747) baseStart_7567747 baseEnd_7567747 := by
    simpa [prefixWord, tailWord_7567747, baseEnd_7567747] using wordTrace_append hprefix tailTrace_7567747
  have hstable : (prefixWord ++ tailWord_7567747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567747).length < 2 ^ (prefixWord ++ tailWord_7567747).sum := by decide
  have hdescent : baseEnd_7567747 < baseStart_7567747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567767 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 1, 5, 2]
def baseStart_7567767 : Nat := 118140960795 + 7567767 * 2 ^ 59
def prefixEnd_7567767 : Nat := 4983230072969 + 3 ^ 40 * 7567767 * 2
def baseEnd_7567767 : Nat := 3885901952233997810508979

theorem tailTrace_7567767 : CollatzResearch.WordTrace tailWord_7567767 prefixEnd_7567767 3885901952233997810508979 := by
  unfold tailWord_7567767
  simp only [CollatzResearch.WordTrace]
  refine ⟨276019138374280105549781555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184012758916186737033187703 276019138374280105549781555)
  ·
    refine ⟨414028707561420158324672333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276019138374280105549781555 414028707561420158324672333)
    ·
      refine ⟨155260765335532559371752125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414028707561420158324672333 155260765335532559371752125)
      ·
        refine ⟨58222787000824709764407047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155260765335532559371752125 58222787000824709764407047)
        ·
          refine ⟨87334180501237064646610571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58222787000824709764407047 87334180501237064646610571)
          ·
            refine ⟨131001270751855596969915857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87334180501237064646610571 131001270751855596969915857)
            ·
              refine ⟨98250953063891697727436893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131001270751855596969915857 98250953063891697727436893)
              ·
                refine ⟨36844107398959386647788835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98250953063891697727436893 36844107398959386647788835)
                ·
                  refine ⟨55266161098439079971683253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36844107398959386647788835 55266161098439079971683253)
                  ·
                    refine ⟨5181202602978663747345305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55266161098439079971683253 5181202602978663747345305)
                    ·
                      refine ⟨3885901952233997810508979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181202602978663747345305 3885901952233997810508979)
                      ·
                        rfl

theorem cell23_7567767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_7567767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567767 prefixEnd_7567767 := by exact prefixLift 7567767
  have htrace : WordTrace (prefixWord ++ tailWord_7567767) baseStart_7567767 baseEnd_7567767 := by
    simpa [prefixWord, tailWord_7567767, baseEnd_7567767] using wordTrace_append hprefix tailTrace_7567767
  have hstable : (prefixWord ++ tailWord_7567767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567767).length < 2 ^ (prefixWord ++ tailWord_7567767).sum := by decide
  have hdescent : baseEnd_7567767 < baseStart_7567767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567800 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_7567800 : Nat := 118140960795 + 7567800 * 2 ^ 59
def prefixEnd_7567800 : Nat := 4983230072969 + 3 ^ 40 * 7567800 * 2
def baseEnd_7567800 : Nat := 3885918897095596181396327

theorem tailTrace_7567800 : CollatzResearch.WordTrace tailWord_7567800 prefixEnd_7567800 3885918897095596181396327 := by
  unfold tailWord_7567800
  simp only [CollatzResearch.WordTrace]
  refine ⟨138010170991580276092866427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184013561322107034790488569 138010170991580276092866427)
  ·
    refine ⟨207015256487370414139299641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138010170991580276092866427 207015256487370414139299641)
    ·
      refine ⟨155261442365527810604474731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207015256487370414139299641 155261442365527810604474731)
      ·
        refine ⟨232892163548291715906712097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155261442365527810604474731 232892163548291715906712097)
        ·
          refine ⟨174669122661218786930034073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232892163548291715906712097 174669122661218786930034073)
          ·
            refine ⟨131001841995914090197525555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174669122661218786930034073 131001841995914090197525555)
            ·
              refine ⟨196502762993871135296288333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131001841995914090197525555 196502762993871135296288333)
              ·
                refine ⟨73688536122701675736108125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196502762993871135296288333 73688536122701675736108125)
                ·
                  refine ⟨27633201046013128401040547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73688536122701675736108125 27633201046013128401040547)
                  ·
                    refine ⟨41449801569019692601560821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27633201046013128401040547 41449801569019692601560821)
                    ·
                      refine ⟨3885918897095596181396327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41449801569019692601560821 3885918897095596181396327)
                      ·
                        rfl

theorem cell23_7567800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_7567800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567800 prefixEnd_7567800 := by exact prefixLift 7567800
  have htrace : WordTrace (prefixWord ++ tailWord_7567800) baseStart_7567800 baseEnd_7567800 := by
    simpa [prefixWord, tailWord_7567800, baseEnd_7567800] using wordTrace_append hprefix tailTrace_7567800
  have hstable : (prefixWord ++ tailWord_7567800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567800).length < 2 ^ (prefixWord ++ tailWord_7567800).sum := by decide
  have hdescent : baseEnd_7567800 < baseStart_7567800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567817 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_7567817 : Nat := 118140960795 + 7567817 * 2 ^ 59
def prefixEnd_7567817 : Nat := 4983230072969 + 3 ^ 40 * 7567817 * 2
def baseEnd_7567817 : Nat := 3885927626266722614883749

theorem tailTrace_7567817 : CollatzResearch.WordTrace tailWord_7567817 prefixEnd_7567817 3885927626266722614883749 := by
  unfold tailWord_7567817
  simp only [CollatzResearch.WordTrace]
  refine ⟨276020962024098964089101705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184013974682732642726067803 276020962024098964089101705)
  ·
    refine ⟨207015721518074223066826279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276020962024098964089101705 207015721518074223066826279)
    ·
      refine ⟨310523582277111334600239419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207015721518074223066826279 310523582277111334600239419)
      ·
        refine ⟨465785373415667001900359129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310523582277111334600239419 465785373415667001900359129)
        ·
          refine ⟨349339030061750251425269347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465785373415667001900359129 349339030061750251425269347)
          ·
            refine ⟨524008545092625377137904021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349339030061750251425269347 524008545092625377137904021)
            ·
              refine ⟨24562900551216814553339251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 524008545092625377137904021 24562900551216814553339251)
              ·
                refine ⟨36844350826825221830008877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24562900551216814553339251 36844350826825221830008877)
                ·
                  refine ⟨13816631560059458186253329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36844350826825221830008877 13816631560059458186253329)
                  ·
                    refine ⟨10362473670044593639689997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13816631560059458186253329 10362473670044593639689997)
                    ·
                      refine ⟨3885927626266722614883749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362473670044593639689997 3885927626266722614883749)
                      ·
                        rfl

theorem cell23_7567817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_7567817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567817 prefixEnd_7567817 := by exact prefixLift 7567817
  have htrace : WordTrace (prefixWord ++ tailWord_7567817) baseStart_7567817 baseEnd_7567817 := by
    simpa [prefixWord, tailWord_7567817, baseEnd_7567817] using wordTrace_append hprefix tailTrace_7567817
  have hstable : (prefixWord ++ tailWord_7567817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567817).length < 2 ^ (prefixWord ++ tailWord_7567817).sum := by decide
  have hdescent : baseEnd_7567817 < baseStart_7567817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567834 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_7567834 : Nat := 118140960795 + 7567834 * 2 ^ 59
def prefixEnd_7567834 : Nat := 4983230072969 + 3 ^ 40 * 7567834 * 2
def baseEnd_7567834 : Nat := 3885936355437849048371171

theorem tailTrace_7567834 : CollatzResearch.WordTrace tailWord_7567834 prefixEnd_7567834 3885936355437849048371171 := by
  unfold tailWord_7567834
  simp only [CollatzResearch.WordTrace]
  refine ⟨69005395516259343998117639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184014388043358250661647037 69005395516259343998117639)
  ·
    refine ⟨103508093274389015997176459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69005395516259343998117639 103508093274389015997176459)
    ·
      refine ⟨155262139911583523995764689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103508093274389015997176459 155262139911583523995764689)
      ·
        refine ⟨116446604933687642996823517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155262139911583523995764689 116446604933687642996823517)
        ·
          refine ⟨43667476850132866123808819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116446604933687642996823517 43667476850132866123808819)
          ·
            refine ⟨65501215275199299185713229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43667476850132866123808819 65501215275199299185713229)
            ·
              refine ⟨24562955728199737194642461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65501215275199299185713229 24562955728199737194642461)
              ·
                refine ⟨9211108398074901447990923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24562955728199737194642461 9211108398074901447990923)
                ·
                  refine ⟨13816662597112352171986385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211108398074901447990923 13816662597112352171986385)
                  ·
                    refine ⟨10362496947834264128989789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13816662597112352171986385 10362496947834264128989789)
                    ·
                      refine ⟨3885936355437849048371171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362496947834264128989789 3885936355437849048371171)
                      ·
                        rfl

theorem cell23_7567834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_7567834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567834 prefixEnd_7567834 := by exact prefixLift 7567834
  have htrace : WordTrace (prefixWord ++ tailWord_7567834) baseStart_7567834 baseEnd_7567834 := by
    simpa [prefixWord, tailWord_7567834, baseEnd_7567834] using wordTrace_append hprefix tailTrace_7567834
  have hstable : (prefixWord ++ tailWord_7567834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567834).length < 2 ^ (prefixWord ++ tailWord_7567834).sum := by decide
  have hdescent : baseEnd_7567834 < baseStart_7567834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567848 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_7567848 : Nat := 118140960795 + 7567848 * 2 ^ 59
def prefixEnd_7567848 : Nat := 4983230072969 + 3 ^ 40 * 7567848 * 2
def baseEnd_7567848 : Nat := 3885943544167011993596107

theorem tailTrace_7567848 : CollatzResearch.WordTrace tailWord_7567848 prefixEnd_7567848 3885943544167011993596107 := by
  unfold tailWord_7567848
  simp only [CollatzResearch.WordTrace]
  refine ⟨138011046343493328191740099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184014728457991104255653465 138011046343493328191740099)
  ·
    refine ⟨207016569515239992287610149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138011046343493328191740099 207016569515239992287610149)
    ·
      refine ⟨38815606784107498553926903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207016569515239992287610149 38815606784107498553926903)
      ·
        refine ⟨58223410176161247830890355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38815606784107498553926903 58223410176161247830890355)
        ·
          refine ⟨87335115264241871746335533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58223410176161247830890355 87335115264241871746335533)
          ·
            refine ⟨32750668224090701904875825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87335115264241871746335533 32750668224090701904875825)
            ·
              refine ⟨24563001168068026428656869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32750668224090701904875825 24563001168068026428656869)
              ·
                refine ⟨4605562719012754955373163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24563001168068026428656869 4605562719012754955373163)
                ·
                  refine ⟨6908344078519132433059745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605562719012754955373163 6908344078519132433059745)
                  ·
                    refine ⟨5181258058889349324794809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6908344078519132433059745 5181258058889349324794809)
                    ·
                      refine ⟨3885943544167011993596107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181258058889349324794809 3885943544167011993596107)
                      ·
                        rfl

theorem cell23_7567848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_7567848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567848 prefixEnd_7567848 := by exact prefixLift 7567848
  have htrace : WordTrace (prefixWord ++ tailWord_7567848) baseStart_7567848 baseEnd_7567848 := by
    simpa [prefixWord, tailWord_7567848, baseEnd_7567848] using wordTrace_append hprefix tailTrace_7567848
  have hstable : (prefixWord ++ tailWord_7567848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567848).length < 2 ^ (prefixWord ++ tailWord_7567848).sum := by decide
  have hdescent : baseEnd_7567848 < baseStart_7567848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567858 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_7567858 : Nat := 118140960795 + 7567858 * 2 ^ 59
def prefixEnd_7567858 : Nat := 4983230072969 + 3 ^ 40 * 7567858 * 2
def baseEnd_7567858 : Nat := 1295316226324518984823687

theorem tailTrace_7567858 : CollatzResearch.WordTrace tailWord_7567858 prefixEnd_7567858 1295316226324518984823687 := by
  unfold tailWord_7567858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69005614354237607022836057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184014971611300285394229485 69005614354237607022836057)
  ·
    refine ⟨51754210765678205267127043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69005614354237607022836057 51754210765678205267127043)
    ·
      refine ⟨77631316148517307900690565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51754210765678205267127043 77631316148517307900690565)
      ·
        refine ⟨14555871777846995231379481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77631316148517307900690565 14555871777846995231379481)
        ·
          refine ⟨10916903833385246423534611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14555871777846995231379481 10916903833385246423534611)
          ·
            refine ⟨16375355750077869635301917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916903833385246423534611 16375355750077869635301917)
            ·
              refine ⟨6140758406279201113238219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16375355750077869635301917 6140758406279201113238219)
              ·
                refine ⟨9211137609418801669857329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140758406279201113238219 9211137609418801669857329)
                ·
                  refine ⟨6908353207064101252392997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9211137609418801669857329 6908353207064101252392997)
                  ·
                    refine ⟨1295316226324518984823687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6908353207064101252392997 1295316226324518984823687)
                    ·
                      rfl

theorem cell23_7567858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_7567858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567858 prefixEnd_7567858 := by exact prefixLift 7567858
  have htrace : WordTrace (prefixWord ++ tailWord_7567858) baseStart_7567858 baseEnd_7567858 := by
    simpa [prefixWord, tailWord_7567858, baseEnd_7567858] using wordTrace_append hprefix tailTrace_7567858
  have hstable : (prefixWord ++ tailWord_7567858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567858).length < 2 ^ (prefixWord ++ tailWord_7567858).sum := by decide
  have hdescent : baseEnd_7567858 < baseStart_7567858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567942 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7567942 : Nat := 118140960795 + 7567942 * 2 ^ 59
def prefixEnd_7567942 : Nat := 4983230072969 + 3 ^ 40 * 7567942 * 2
def baseEnd_7567942 : Nat := 3885991811348534625820675

theorem tailTrace_7567942 : CollatzResearch.WordTrace tailWord_7567942 prefixEnd_7567942 3885991811348534625820675 := by
  unfold tailWord_7567942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625797535895190951168815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184017014099097406958268053 8625797535895190951168815)
  ·
    refine ⟨12938696303842786426753223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8625797535895190951168815 12938696303842786426753223)
    ·
      refine ⟨19408044455764179640129835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12938696303842786426753223 19408044455764179640129835)
      ·
        refine ⟨29112066683646269460194753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19408044455764179640129835 29112066683646269460194753)
        ·
          refine ⟨21834050012734702095146065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29112066683646269460194753 21834050012734702095146065)
          ·
            refine ⟨16375537509551026571359549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21834050012734702095146065 16375537509551026571359549)
            ·
              refine ⟨6140826566081634964259831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16375537509551026571359549 6140826566081634964259831)
              ·
                refine ⟨9211239849122452446389747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140826566081634964259831 9211239849122452446389747)
                ·
                  refine ⟨13816859773683678669584621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211239849122452446389747 13816859773683678669584621)
                  ·
                    refine ⟨5181322415131379501094233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13816859773683678669584621 5181322415131379501094233)
                    ·
                      refine ⟨3885991811348534625820675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181322415131379501094233 3885991811348534625820675)
                      ·
                        rfl

theorem cell23_7567942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7567942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567942 prefixEnd_7567942 := by exact prefixLift 7567942
  have htrace : WordTrace (prefixWord ++ tailWord_7567942) baseStart_7567942 baseEnd_7567942 := by
    simpa [prefixWord, tailWord_7567942, baseEnd_7567942] using wordTrace_append hprefix tailTrace_7567942
  have hstable : (prefixWord ++ tailWord_7567942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567942).length < 2 ^ (prefixWord ++ tailWord_7567942).sum := by decide
  have hdescent : baseEnd_7567942 < baseStart_7567942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567954 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_7567954 : Nat := 118140960795 + 7567954 * 2 ^ 59
def prefixEnd_7567954 : Nat := 4983230072969 + 3 ^ 40 * 7567954 * 2
def baseEnd_7567954 : Nat := 3885997973116388578870619

theorem tailTrace_7567954 : CollatzResearch.WordTrace tailWord_7567954 prefixEnd_7567954 3885997973116388578870619 := by
  unfold tailWord_7567954
  simp only [CollatzResearch.WordTrace]
  refine ⟨69006489706150659121709729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184017305883068424324559277 69006489706150659121709729)
  ·
    refine ⟨51754867279612994341282297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69006489706150659121709729 51754867279612994341282297)
    ·
      refine ⟨38816150459709745755961723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51754867279612994341282297 38816150459709745755961723)
      ·
        refine ⟨58224225689564618633942585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38816150459709745755961723 58224225689564618633942585)
        ·
          refine ⟨43668169267173463975456939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58224225689564618633942585 43668169267173463975456939)
          ·
            refine ⟨65502253900760195963185409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43668169267173463975456939 65502253900760195963185409)
            ·
              refine ⟨49126690425570146972389057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65502253900760195963185409 49126690425570146972389057)
              ·
                refine ⟨36845017819177610229291793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49126690425570146972389057 36845017819177610229291793)
                ·
                  refine ⟨27633763364383207671968845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36845017819177610229291793 27633763364383207671968845)
                  ·
                    refine ⟨10362661261643702876988317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27633763364383207671968845 10362661261643702876988317)
                    ·
                      refine ⟨3885997973116388578870619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362661261643702876988317 3885997973116388578870619)
                      ·
                        rfl

theorem cell23_7567954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_7567954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567954 prefixEnd_7567954 := by exact prefixLift 7567954
  have htrace : WordTrace (prefixWord ++ tailWord_7567954) baseStart_7567954 baseEnd_7567954 := by
    simpa [prefixWord, tailWord_7567954, baseEnd_7567954] using wordTrace_append hprefix tailTrace_7567954
  have hstable : (prefixWord ++ tailWord_7567954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567954).length < 2 ^ (prefixWord ++ tailWord_7567954).sum := by decide
  have hdescent : baseEnd_7567954 < baseStart_7567954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7567977 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_7567977 : Nat := 118140960795 + 7567977 * 2 ^ 59
def prefixEnd_7567977 : Nat := 4983230072969 + 3 ^ 40 * 7567977 * 2
def baseEnd_7567977 : Nat := 3886009783171441988883013

theorem tailTrace_7567977 : CollatzResearch.WordTrace tailWord_7567977 prefixEnd_7567977 3886009783171441988883013 := by
  unfold tailWord_7567977
  simp only [CollatzResearch.WordTrace]
  refine ⟨276026797703519311414926185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184017865135679540943284123 276026797703519311414926185)
  ·
    refine ⟨207020098277639483561194639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276026797703519311414926185 207020098277639483561194639)
    ·
      refine ⟨310530147416459225341791959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207020098277639483561194639 310530147416459225341791959)
      ·
        refine ⟨465795221124688838012687939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310530147416459225341791959 465795221124688838012687939)
        ·
          refine ⟨698692831687033257019031909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465795221124688838012687939 698692831687033257019031909)
          ·
            refine ⟨131004905941318735691068483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 698692831687033257019031909 131004905941318735691068483)
            ·
              refine ⟨196507358911978103536602725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131004905941318735691068483 196507358911978103536602725)
              ·
                refine ⟨36845129795995894413113011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196507358911978103536602725 36845129795995894413113011)
                ·
                  refine ⟨55267694693993841619669517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36845129795995894413113011 55267694693993841619669517)
                  ·
                    refine ⟨20725385510247690607376069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55267694693993841619669517 20725385510247690607376069)
                    ·
                      refine ⟨3886009783171441988883013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20725385510247690607376069 3886009783171441988883013)
                      ·
                        rfl

theorem cell23_7567977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_7567977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7567977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7567977 prefixEnd_7567977 := by exact prefixLift 7567977
  have htrace : WordTrace (prefixWord ++ tailWord_7567977) baseStart_7567977 baseEnd_7567977 := by
    simpa [prefixWord, tailWord_7567977, baseEnd_7567977] using wordTrace_append hprefix tailTrace_7567977
  have hstable : (prefixWord ++ tailWord_7567977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7567977).length < 2 ^ (prefixWord ++ tailWord_7567977).sum := by decide
  have hdescent : baseEnd_7567977 < baseStart_7567977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7567977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568007 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_7568007 : Nat := 118140960795 + 7568007 * 2 ^ 59
def prefixEnd_7568007 : Nat := 4983230072969 + 3 ^ 40 * 7568007 * 2
def baseEnd_7568007 : Nat := 3886025187591076871507875

theorem tailTrace_7568007 : CollatzResearch.WordTrace tailWord_7568007 prefixEnd_7568007 3886025187591076871507875 := by
  unfold tailWord_7568007
  simp only [CollatzResearch.WordTrace]
  refine ⟨276027891893410626538518275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184018594595607084359012183 276027891893410626538518275)
  ·
    refine ⟨414041837840115939807777413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276027891893410626538518275 414041837840115939807777413)
    ·
      refine ⟨77632844595021738713958265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414041837840115939807777413 77632844595021738713958265)
      ·
        refine ⟨58224633446266304035468699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77632844595021738713958265 58224633446266304035468699)
        ·
          refine ⟨87336950169399456053203049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58224633446266304035468699 87336950169399456053203049)
          ·
            refine ⟨65502712627049592039902287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87336950169399456053203049 65502712627049592039902287)
            ·
              refine ⟨98254068940574388059853431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65502712627049592039902287 98254068940574388059853431)
              ·
                refine ⟨147381103410861582089780147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98254068940574388059853431 147381103410861582089780147)
                ·
                  refine ⟨221071655116292373134670221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147381103410861582089780147 221071655116292373134670221)
                  ·
                    refine ⟨82901870668609639925501333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221071655116292373134670221 82901870668609639925501333)
                    ·
                      refine ⟨3886025187591076871507875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82901870668609639925501333 3886025187591076871507875)
                      ·
                        rfl

theorem cell23_7568007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_7568007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568007 prefixEnd_7568007 := by exact prefixLift 7568007
  have htrace : WordTrace (prefixWord ++ tailWord_7568007) baseStart_7568007 baseEnd_7568007 := by
    simpa [prefixWord, tailWord_7568007, baseEnd_7568007] using wordTrace_append hprefix tailTrace_7568007
  have hstable : (prefixWord ++ tailWord_7568007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568007).length < 2 ^ (prefixWord ++ tailWord_7568007).sum := by decide
  have hdescent : baseEnd_7568007 < baseStart_7568007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568037 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7568037 : Nat := 118140960795 + 7568037 * 2 ^ 59
def prefixEnd_7568037 : Nat := 4983230072969 + 3 ^ 40 * 7568037 * 2
def baseEnd_7568037 : Nat := 3886040592010711754132737

theorem tailTrace_7568037 : CollatzResearch.WordTrace tailWord_7568037 prefixEnd_7568037 3886040592010711754132737 := by
  unfold tailWord_7568037
  simp only [CollatzResearch.WordTrace]
  refine ⟨276028986083301941662110365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184019324055534627774740243 276028986083301941662110365)
  ·
    refine ⟨103510869781238228123291387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276028986083301941662110365 103510869781238228123291387)
    ·
      refine ⟨155266304671857342184937081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103510869781238228123291387 155266304671857342184937081)
      ·
        refine ⟨116449728503893006638702811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155266304671857342184937081 116449728503893006638702811)
        ·
          refine ⟨174674592755839509958054217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116449728503893006638702811 174674592755839509958054217)
          ·
            refine ⟨131005944566879632468540663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174674592755839509958054217 131005944566879632468540663)
            ·
              refine ⟨196508916850319448702810995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131005944566879632468540663 196508916850319448702810995)
              ·
                refine ⟨294763375275479173054216493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196508916850319448702810995 294763375275479173054216493)
                ·
                  refine ⟨110536265728304689895331185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294763375275479173054216493 110536265728304689895331185)
                  ·
                    refine ⟨82902199296228517421498389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110536265728304689895331185 82902199296228517421498389)
                    ·
                      refine ⟨3886040592010711754132737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82902199296228517421498389 3886040592010711754132737)
                      ·
                        rfl

theorem cell23_7568037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7568037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568037 prefixEnd_7568037 := by exact prefixLift 7568037
  have htrace : WordTrace (prefixWord ++ tailWord_7568037) baseStart_7568037 baseEnd_7568037 := by
    simpa [prefixWord, tailWord_7568037, baseEnd_7568037] using wordTrace_append hprefix tailTrace_7568037
  have hstable : (prefixWord ++ tailWord_7568037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568037).length < 2 ^ (prefixWord ++ tailWord_7568037).sum := by decide
  have hdescent : baseEnd_7568037 < baseStart_7568037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568055 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 1, 4]
def baseStart_7568055 : Nat := 118140960795 + 7568055 * 2 ^ 59
def prefixEnd_7568055 : Nat := 4983230072969 + 3 ^ 40 * 7568055 * 2
def baseEnd_7568055 : Nat := 1295349944887497561235885

theorem tailTrace_7568055 : CollatzResearch.WordTrace tailWord_7568055 prefixEnd_7568055 1295349944887497561235885 := by
  unfold tailWord_7568055
  simp only [CollatzResearch.WordTrace]
  refine ⟨276029642597236730736265619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184019761731491153824177079 276029642597236730736265619)
  ·
    refine ⟨414044463895855096104398429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276029642597236730736265619 414044463895855096104398429)
    ·
      refine ⟨155266673960945661039149411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414044463895855096104398429 155266673960945661039149411)
      ·
        refine ⟨232900010941418491558724117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155266673960945661039149411 232900010941418491558724117)
        ·
          refine ⟨10917188012878991791815193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232900010941418491558724117 10917188012878991791815193)
          ·
            refine ⟨8187891009659243843861395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10917188012878991791815193 8187891009659243843861395)
            ·
              refine ⟨12281836514488865765792093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187891009659243843861395 12281836514488865765792093)
              ·
                refine ⟨4605688692933324662172035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12281836514488865765792093 4605688692933324662172035)
                ·
                  refine ⟨6908533039399986993258053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605688692933324662172035 6908533039399986993258053)
                  ·
                    refine ⟨1295349944887497561235885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6908533039399986993258053 1295349944887497561235885)
                    ·
                      rfl

theorem cell23_7568055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_7568055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568055 prefixEnd_7568055 := by exact prefixLift 7568055
  have htrace : WordTrace (prefixWord ++ tailWord_7568055) baseStart_7568055 baseEnd_7568055 := by
    simpa [prefixWord, tailWord_7568055, baseEnd_7568055] using wordTrace_append hprefix tailTrace_7568055
  have hstable : (prefixWord ++ tailWord_7568055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568055).length < 2 ^ (prefixWord ++ tailWord_7568055).sum := by decide
  have hdescent : baseEnd_7568055 < baseStart_7568055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568065 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7568065 : Nat := 118140960795 + 7568065 * 2 ^ 59
def prefixEnd_7568065 : Nat := 4983230072969 + 3 ^ 40 * 7568065 * 2
def baseEnd_7568065 : Nat := 3886054969469037644582609

theorem tailTrace_7568065 : CollatzResearch.WordTrace tailWord_7568065 prefixEnd_7568065 3886054969469037644582609 := by
  unfold tailWord_7568065
  simp only [CollatzResearch.WordTrace]
  refine ⟨276030007327200502444129649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184020004884800334962753099 276030007327200502444129649)
  ·
    refine ⟨207022505495400376833097237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276030007327200502444129649 207022505495400376833097237)
    ·
      refine ⟨9704179945096892664051433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207022505495400376833097237 9704179945096892664051433)
      ·
        refine ⟨7278134958822669498038575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9704179945096892664051433 7278134958822669498038575)
        ·
          refine ⟨10917202438234004247057863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278134958822669498038575 10917202438234004247057863)
          ·
            refine ⟨16375803657351006370586795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917202438234004247057863 16375803657351006370586795)
            ·
              refine ⟨24563705486026509555880193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16375803657351006370586795 24563705486026509555880193)
              ·
                refine ⟨18422779114519882166910145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24563705486026509555880193 18422779114519882166910145)
                ·
                  refine ⟨13817084335889911625182609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18422779114519882166910145 13817084335889911625182609)
                  ·
                    refine ⟨10362813251917433718886957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13817084335889911625182609 10362813251917433718886957)
                    ·
                      refine ⟨3886054969469037644582609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362813251917433718886957 3886054969469037644582609)
                      ·
                        rfl

theorem cell23_7568065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7568065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568065 prefixEnd_7568065 := by exact prefixLift 7568065
  have htrace : WordTrace (prefixWord ++ tailWord_7568065) baseStart_7568065 baseEnd_7568065 := by
    simpa [prefixWord, tailWord_7568065, baseEnd_7568065] using wordTrace_append hprefix tailTrace_7568065
  have hstable : (prefixWord ++ tailWord_7568065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568065).length < 2 ^ (prefixWord ++ tailWord_7568065).sum := by decide
  have hdescent : baseEnd_7568065 < baseStart_7568065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568078 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_7568078 : Nat := 118140960795 + 7568078 * 2 ^ 59
def prefixEnd_7568078 : Nat := 4983230072969 + 3 ^ 40 * 7568078 * 2
def baseEnd_7568078 : Nat := 3886061644717546093720049

theorem tailTrace_7568078 : CollatzResearch.WordTrace tailWord_7568078 prefixEnd_7568078 3886061644717546093720049 := by
  unfold tailWord_7568078
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503810184519175708044111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184020320984102270442901925 34503810184519175708044111)
  ·
    refine ⟨51755715276778763562066167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34503810184519175708044111 51755715276778763562066167)
    ·
      refine ⟨77633572915168145343099251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51755715276778763562066167 77633572915168145343099251)
      ·
        refine ⟨116450359372752218014648877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77633572915168145343099251 116450359372752218014648877)
        ·
          refine ⟨43668884764782081755493329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116450359372752218014648877 43668884764782081755493329)
          ·
            refine ⟨32751663573586561316619997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43668884764782081755493329 32751663573586561316619997)
            ·
              refine ⟨12281873840094960493732499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32751663573586561316619997 12281873840094960493732499)
              ·
                refine ⟨18422810760142440740598749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12281873840094960493732499 18422810760142440740598749)
                ·
                  refine ⟨6908554035053415277724531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18422810760142440740598749 6908554035053415277724531)
                  ·
                    refine ⟨10362831052580122916586797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6908554035053415277724531 10362831052580122916586797)
                    ·
                      refine ⟨3886061644717546093720049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362831052580122916586797 3886061644717546093720049)
                      ·
                        rfl

theorem cell23_7568078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_7568078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568078 prefixEnd_7568078 := by exact prefixLift 7568078
  have htrace : WordTrace (prefixWord ++ tailWord_7568078) baseStart_7568078 baseEnd_7568078 := by
    simpa [prefixWord, tailWord_7568078, baseEnd_7568078] using wordTrace_append hprefix tailTrace_7568078
  have hstable : (prefixWord ++ tailWord_7568078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568078).length < 2 ^ (prefixWord ++ tailWord_7568078).sum := by decide
  have hdescent : baseEnd_7568078 < baseStart_7568078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568085 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 6]
def baseStart_7568085 : Nat := 118140960795 + 7568085 * 2 ^ 59
def prefixEnd_7568085 : Nat := 4983230072969 + 3 ^ 40 * 7568085 * 2
def baseEnd_7568085 : Nat := 431785026564680840703613

theorem tailTrace_7568085 : CollatzResearch.WordTrace tailWord_7568085 prefixEnd_7568085 431785026564680840703613 := by
  unfold tailWord_7568085
  simp only [CollatzResearch.WordTrace]
  refine ⟨276030736787128045859857709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184020491191418697239905139 276030736787128045859857709)
  ·
    refine ⟨103511526295173017197446641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276030736787128045859857709 103511526295173017197446641)
    ·
      refine ⟨77633644721379762898084981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103511526295173017197446641 77633644721379762898084981)
      ·
        refine ⟨7278154192629352771695467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77633644721379762898084981 7278154192629352771695467)
        ·
          refine ⟨10917231288944029157543201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278154192629352771695467 10917231288944029157543201)
          ·
            refine ⟨8187923466708021868157401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10917231288944029157543201 8187923466708021868157401)
            ·
              refine ⟨6140942600031016401118051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8187923466708021868157401 6140942600031016401118051)
              ·
                refine ⟨9211413900046524601677077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140942600031016401118051 9211413900046524601677077)
                ·
                  refine ⟨431785026564680840703613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9211413900046524601677077 431785026564680840703613)
                  ·
                    rfl

theorem cell23_7568085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_7568085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568085 prefixEnd_7568085 := by exact prefixLift 7568085
  have htrace : WordTrace (prefixWord ++ tailWord_7568085) baseStart_7568085 baseEnd_7568085 := by
    simpa [prefixWord, tailWord_7568085, baseEnd_7568085] using wordTrace_append hprefix tailTrace_7568085
  have hstable : (prefixWord ++ tailWord_7568085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568085).length < 2 ^ (prefixWord ++ tailWord_7568085).sum := by decide
  have hdescent : baseEnd_7568085 < baseStart_7568085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568101 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7568101 : Nat := 118140960795 + 7568101 * 2 ^ 59
def prefixEnd_7568101 : Nat := 4983230072969 + 3 ^ 40 * 7568101 * 2
def baseEnd_7568101 : Nat := 3886073454772599503732443

theorem tailTrace_7568101 : CollatzResearch.WordTrace tailWord_7568101 prefixEnd_7568101 3886073454772599503732443 := by
  unfold tailWord_7568101
  simp only [CollatzResearch.WordTrace]
  refine ⟨276031320355070080592440157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184020880236713387061626771 276031320355070080592440157)
  ·
    refine ⟨103511745133151280222165059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276031320355070080592440157 103511745133151280222165059)
    ·
      refine ⟨155267617699726920333247589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103511745133151280222165059 155267617699726920333247589)
      ·
        refine ⟨29112678318698797562483923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155267617699726920333247589 29112678318698797562483923)
        ·
          refine ⟨43669017478048196343725885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29112678318698797562483923 43669017478048196343725885)
          ·
            refine ⟨16375881554268073628897207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43669017478048196343725885 16375881554268073628897207)
            ·
              refine ⟨24563822331402110443345811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16375881554268073628897207 24563822331402110443345811)
              ·
                refine ⟨36845733497103165665018717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24563822331402110443345811 36845733497103165665018717)
                ·
                  refine ⟨13817150061413687124382019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36845733497103165665018717 13817150061413687124382019)
                  ·
                    refine ⟨20725725092120530686573029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13817150061413687124382019 20725725092120530686573029)
                    ·
                      refine ⟨3886073454772599503732443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20725725092120530686573029 3886073454772599503732443)
                      ·
                        rfl

theorem cell23_7568101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7568101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568101 prefixEnd_7568101 := by exact prefixLift 7568101
  have htrace : WordTrace (prefixWord ++ tailWord_7568101) baseStart_7568101 baseEnd_7568101 := by
    simpa [prefixWord, tailWord_7568101, baseEnd_7568101] using wordTrace_append hprefix tailTrace_7568101
  have hstable : (prefixWord ++ tailWord_7568101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568101).length < 2 ^ (prefixWord ++ tailWord_7568101).sum := by decide
  have hdescent : baseEnd_7568101 < baseStart_7568101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568121 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 3]
def baseStart_7568121 : Nat := 118140960795 + 7568121 * 2 ^ 59
def prefixEnd_7568121 : Nat := 4983230072969 + 3 ^ 40 * 7568121 * 2
def baseEnd_7568121 : Nat := 3886083724385689425482351

theorem tailTrace_7568121 : CollatzResearch.WordTrace tailWord_7568121 prefixEnd_7568121 3886083724385689425482351 := by
  unfold tailWord_7568121
  simp only [CollatzResearch.WordTrace]
  refine ⟨276032049814997624008168217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184021366543331749338778811 276032049814997624008168217)
  ·
    refine ⟨207024037361248218006126163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276032049814997624008168217 207024037361248218006126163)
    ·
      refine ⟨310536056041872327009189245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207024037361248218006126163 310536056041872327009189245)
      ·
        refine ⟨116451021015702122628445967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310536056041872327009189245 116451021015702122628445967)
        ·
          refine ⟨174676531523553183942668951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116451021015702122628445967 174676531523553183942668951)
          ·
            refine ⟨262014797285329775914003427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174676531523553183942668951 262014797285329775914003427)
            ·
              refine ⟨393022195927994663871005141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262014797285329775914003427 393022195927994663871005141)
              ·
                refine ⟨9211457717062374934476683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 393022195927994663871005141 9211457717062374934476683)
                ·
                  refine ⟨13817186575593562401715025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211457717062374934476683 13817186575593562401715025)
                  ·
                    refine ⟨10362889931695171801286269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13817186575593562401715025 10362889931695171801286269)
                    ·
                      refine ⟨3886083724385689425482351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362889931695171801286269 3886083724385689425482351)
                      ·
                        rfl

theorem cell23_7568121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_7568121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568121 prefixEnd_7568121 := by exact prefixLift 7568121
  have htrace : WordTrace (prefixWord ++ tailWord_7568121) baseStart_7568121 baseEnd_7568121 := by
    simpa [prefixWord, tailWord_7568121, baseEnd_7568121] using wordTrace_append hprefix tailTrace_7568121
  have hstable : (prefixWord ++ tailWord_7568121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568121).length < 2 ^ (prefixWord ++ tailWord_7568121).sum := by decide
  have hdescent : baseEnd_7568121 < baseStart_7568121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568154 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_7568154 : Nat := 118140960795 + 7568154 * 2 ^ 59
def prefixEnd_7568154 : Nat := 4983230072969 + 3 ^ 40 * 7568154 * 2
def baseEnd_7568154 : Nat := 1295366889749095932123233

theorem tailTrace_7568154 : CollatzResearch.WordTrace tailWord_7568154 prefixEnd_7568154 1295366889749095932123233 := by
  unfold tailWord_7568154
  simp only [CollatzResearch.WordTrace]
  refine ⟨69008313355969517661029879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184022168949252047096079677 69008313355969517661029879)
  ·
    refine ⟨103512470033954276491544819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69008313355969517661029879 103512470033954276491544819)
    ·
      refine ⟨155268705050931414737317229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103512470033954276491544819 155268705050931414737317229)
      ·
        refine ⟨58225764394099280526493961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155268705050931414737317229 58225764394099280526493961)
        ·
          refine ⟨43669323295574460394870471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58225764394099280526493961 43669323295574460394870471)
          ·
            refine ⟨65503984943361690592305707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43669323295574460394870471 65503984943361690592305707)
            ·
              refine ⟨98255977415042535888458561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65503984943361690592305707 98255977415042535888458561)
              ·
                refine ⟨73691983061281901916343921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98255977415042535888458561 73691983061281901916343921)
                ·
                  refine ⟨55268987295961426437257941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73691983061281901916343921 55268987295961426437257941)
                  ·
                    refine ⟨1295366889749095932123233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55268987295961426437257941 1295366889749095932123233)
                    ·
                      rfl

theorem cell23_7568154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_7568154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568154 prefixEnd_7568154 := by exact prefixLift 7568154
  have htrace : WordTrace (prefixWord ++ tailWord_7568154) baseStart_7568154 baseEnd_7568154 := by
    simpa [prefixWord, tailWord_7568154, baseEnd_7568154] using wordTrace_append hprefix tailTrace_7568154
  have hstable : (prefixWord ++ tailWord_7568154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568154).length < 2 ^ (prefixWord ++ tailWord_7568154).sum := by decide
  have hdescent : baseEnd_7568154 < baseStart_7568154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568168 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_7568168 : Nat := 118140960795 + 7568168 * 2 ^ 59
def prefixEnd_7568168 : Nat := 4983230072969 + 3 ^ 40 * 7568168 * 2
def baseEnd_7568168 : Nat := 3886107857976450741594635

theorem tailTrace_7568168 : CollatzResearch.WordTrace tailWord_7568168 prefixEnd_7568168 3886107857976450741594635 := by
  unfold tailWord_7568168
  simp only [CollatzResearch.WordTrace]
  refine ⟨138016882022913675517564579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184022509363884900690086105 138016882022913675517564579)
  ·
    refine ⟨207025323034370513276346869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138016882022913675517564579 207025323034370513276346869)
    ·
      refine ⟨19408624034472235619657519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207025323034370513276346869 19408624034472235619657519)
      ·
        refine ⟨29112936051708353429486279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19408624034472235619657519 29112936051708353429486279)
        ·
          refine ⟨43669404077562530144229419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29112936051708353429486279 43669404077562530144229419)
          ·
            refine ⟨65504106116343795216344129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43669404077562530144229419 65504106116343795216344129)
            ·
              refine ⟨49128079587257846412258097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65504106116343795216344129 49128079587257846412258097)
              ·
                refine ⟨36846059690443384809193573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49128079587257846412258097 36846059690443384809193573)
                ·
                  refine ⟨6908636191958134651723795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36846059690443384809193573 6908636191958134651723795)
                  ·
                    refine ⟨10362954287937201977585693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6908636191958134651723795 10362954287937201977585693)
                    ·
                      refine ⟨3886107857976450741594635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10362954287937201977585693 3886107857976450741594635)
                      ·
                        rfl

theorem cell23_7568168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_7568168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568168 prefixEnd_7568168 := by exact prefixLift 7568168
  have htrace : WordTrace (prefixWord ++ tailWord_7568168) baseStart_7568168 baseEnd_7568168 := by
    simpa [prefixWord, tailWord_7568168, baseEnd_7568168] using wordTrace_append hprefix tailTrace_7568168
  have hstable : (prefixWord ++ tailWord_7568168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568168).length < 2 ^ (prefixWord ++ tailWord_7568168).sum := by decide
  have hdescent : baseEnd_7568168 < baseStart_7568168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568184 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_7568184 : Nat := 118140960795 + 7568184 * 2 ^ 59
def prefixEnd_7568184 : Nat := 4983230072969 + 3 ^ 40 * 7568184 * 2
def baseEnd_7568184 : Nat := 1295372024555640892998187

theorem tailTrace_7568184 : CollatzResearch.WordTrace tailWord_7568184 prefixEnd_7568184 1295372024555640892998187 := by
  unfold tailWord_7568184
  simp only [CollatzResearch.WordTrace]
  refine ⟨138017173806884692883855803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184022898409179590511807737 138017173806884692883855803)
  ·
    refine ⟨207025760710327039325783705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138017173806884692883855803 207025760710327039325783705)
    ·
      refine ⟨155269320532745279494337779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207025760710327039325783705 155269320532745279494337779)
      ·
        refine ⟨232903980799117919241506669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155269320532745279494337779 232903980799117919241506669)
        ·
          refine ⟨87338992799669219715565001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232903980799117919241506669 87338992799669219715565001)
          ·
            refine ⟨65504244599751914786673751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87338992799669219715565001 65504244599751914786673751)
            ·
              refine ⟨98256366899627872180010627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65504244599751914786673751 98256366899627872180010627)
              ·
                refine ⟨147384550349441808270015941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98256366899627872180010627 147384550349441808270015941)
                ·
                  refine ⟨27634603190520339050627989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147384550349441808270015941 27634603190520339050627989)
                  ·
                    refine ⟨1295372024555640892998187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27634603190520339050627989 1295372024555640892998187)
                    ·
                      rfl

theorem cell23_7568184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_7568184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568184 prefixEnd_7568184 := by exact prefixLift 7568184
  have htrace : WordTrace (prefixWord ++ tailWord_7568184) baseStart_7568184 baseEnd_7568184 := by
    simpa [prefixWord, tailWord_7568184, baseEnd_7568184] using wordTrace_append hprefix tailTrace_7568184
  have hstable : (prefixWord ++ tailWord_7568184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568184).length < 2 ^ (prefixWord ++ tailWord_7568184).sum := by decide
  have hdescent : baseEnd_7568184 < baseStart_7568184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568208 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 1, 4, 2]
def baseStart_7568208 : Nat := 118140960795 + 7568208 * 2 ^ 59
def prefixEnd_7568208 : Nat := 4983230072969 + 3 ^ 40 * 7568208 * 2
def baseEnd_7568208 : Nat := 3886128397202630585094451

theorem tailTrace_7568208 : CollatzResearch.WordTrace tailWord_7568208 prefixEnd_7568208 3886128397202630585094451 := by
  unfold tailWord_7568208
  simp only [CollatzResearch.WordTrace]
  refine ⟨138017611482841218933292639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184023481977121625244390185 138017611482841218933292639)
  ·
    refine ⟨207026417224261828399938959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138017611482841218933292639 207026417224261828399938959)
    ·
      refine ⟨310539625836392742599908439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207026417224261828399938959 310539625836392742599908439)
      ·
        refine ⟨465809438754589113899862659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310539625836392742599908439 465809438754589113899862659)
        ·
          refine ⟨698714158131883670849793989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465809438754589113899862659 698714158131883670849793989)
          ·
            refine ⟨131008904649728188284336373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 698714158131883670849793989 131008904649728188284336373)
            ·
              refine ⟨12282084810912017651656535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131008904649728188284336373 12282084810912017651656535)
              ·
                refine ⟨18423127216368026477484803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12282084810912017651656535 18423127216368026477484803)
                ·
                  refine ⟨27634690824552039716227205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18423127216368026477484803 27634690824552039716227205)
                  ·
                    refine ⟨5181504529603507446792601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27634690824552039716227205 5181504529603507446792601)
                    ·
                      refine ⟨3886128397202630585094451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181504529603507446792601 3886128397202630585094451)
                      ·
                        rfl

theorem cell23_7568208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 4, 2].length) (baseStart_7568208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568208 prefixEnd_7568208 := by exact prefixLift 7568208
  have htrace : WordTrace (prefixWord ++ tailWord_7568208) baseStart_7568208 baseEnd_7568208 := by
    simpa [prefixWord, tailWord_7568208, baseEnd_7568208] using wordTrace_append hprefix tailTrace_7568208
  have hstable : (prefixWord ++ tailWord_7568208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568208).length < 2 ^ (prefixWord ++ tailWord_7568208).sum := by decide
  have hdescent : baseEnd_7568208 < baseStart_7568208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568212 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_7568212 : Nat := 118140960795 + 7568212 * 2 ^ 59
def prefixEnd_7568212 : Nat := 4983230072969 + 3 ^ 40 * 7568212 * 2
def baseEnd_7568212 : Nat := 3886130451125248569444433

theorem tailTrace_7568212 : CollatzResearch.WordTrace tailWord_7568212 prefixEnd_7568212 3886130451125248569444433 := by
  unfold tailWord_7568212
  simp only [CollatzResearch.WordTrace]
  refine ⟨138017684428833973274865445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184023579238445297699820593 138017684428833973274865445)
  ·
    refine ⟨25878315830406369989037271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138017684428833973274865445 25878315830406369989037271)
    ·
      refine ⟨38817473745609554983555907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25878315830406369989037271 38817473745609554983555907)
      ·
        refine ⟨58226210618414332475333861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38817473745609554983555907 58226210618414332475333861)
        ·
          refine ⟨10917414490952687339125099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58226210618414332475333861 10917414490952687339125099)
          ·
            refine ⟨16376121736429031008687649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917414490952687339125099 16376121736429031008687649)
            ·
              refine ⟨12282091302321773256515737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16376121736429031008687649 12282091302321773256515737)
              ·
                refine ⟨9211568476741329942386803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12282091302321773256515737 9211568476741329942386803)
                ·
                  refine ⟨13817352715111994913580205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211568476741329942386803 13817352715111994913580205)
                  ·
                    refine ⟨5181507268166998092592577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13817352715111994913580205 5181507268166998092592577)
                    ·
                      refine ⟨3886130451125248569444433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181507268166998092592577 3886130451125248569444433)
                      ·
                        rfl

theorem cell23_7568212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_7568212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568212 prefixEnd_7568212 := by exact prefixLift 7568212
  have htrace : WordTrace (prefixWord ++ tailWord_7568212) baseStart_7568212 baseEnd_7568212 := by
    simpa [prefixWord, tailWord_7568212, baseEnd_7568212] using wordTrace_append hprefix tailTrace_7568212
  have hstable : (prefixWord ++ tailWord_7568212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568212).length < 2 ^ (prefixWord ++ tailWord_7568212).sum := by decide
  have hdescent : baseEnd_7568212 < baseStart_7568212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568318 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_7568318 : Nat := 118140960795 + 7568318 * 2 ^ 59
def prefixEnd_7568318 : Nat := 4983230072969 + 3 ^ 40 * 7568318 * 2
def baseEnd_7568318 : Nat := 3886184880074625154718945

theorem tailTrace_7568318 : CollatzResearch.WordTrace tailWord_7568318 prefixEnd_7568318 3886184880074625154718945 := by
  unfold tailWord_7568318
  simp only [CollatzResearch.WordTrace]
  refine ⟨34504904374410490831636201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184026156663522617768726405 34504904374410490831636201)
  ·
    refine ⟨25878678280807868123727151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34504904374410490831636201 25878678280807868123727151)
    ·
      refine ⟨38818017421211802185590727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25878678280807868123727151 38818017421211802185590727)
      ·
        refine ⟨58227026131817703278386091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38818017421211802185590727 58227026131817703278386091)
        ·
          refine ⟨87340539197726554917579137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58227026131817703278386091 87340539197726554917579137)
          ·
            refine ⟨65505404398294916188184353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87340539197726554917579137 65505404398294916188184353)
            ·
              refine ⟨49129053298721187141138265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65505404398294916188184353 49129053298721187141138265)
              ·
                refine ⟨36846789974040890355853699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49129053298721187141138265 36846789974040890355853699)
                ·
                  refine ⟨55270184961061335533780549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36846789974040890355853699 55270184961061335533780549)
                  ·
                    refine ⟨10363159680199000412583853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55270184961061335533780549 10363159680199000412583853)
                    ·
                      refine ⟨3886184880074625154718945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363159680199000412583853 3886184880074625154718945)
                      ·
                        rfl

theorem cell23_7568318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_7568318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568318 prefixEnd_7568318 := by exact prefixLift 7568318
  have htrace : WordTrace (prefixWord ++ tailWord_7568318) baseStart_7568318 baseEnd_7568318 := by
    simpa [prefixWord, tailWord_7568318, baseEnd_7568318] using wordTrace_append hprefix tailTrace_7568318
  have hstable : (prefixWord ++ tailWord_7568318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568318).length < 2 ^ (prefixWord ++ tailWord_7568318).sum := by decide
  have hdescent : baseEnd_7568318 < baseStart_7568318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568335 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 3]
def baseStart_7568335 : Nat := 118140960795 + 7568335 * 2 ^ 59
def prefixEnd_7568335 : Nat := 4983230072969 + 3 ^ 40 * 7568335 * 2
def baseEnd_7568335 : Nat := 3886193609245751588206367

theorem tailTrace_7568335 : CollatzResearch.WordTrace tailWord_7568335 prefixEnd_7568335 3886193609245751588206367 := by
  unfold tailWord_7568335
  simp only [CollatzResearch.WordTrace]
  refine ⟨276039855036222338556458459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184026570024148225704305639 276039855036222338556458459)
  ·
    refine ⟨414059782554333507834687689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276039855036222338556458459 414059782554333507834687689)
    ·
      refine ⟨310544836915750130876015767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414059782554333507834687689 310544836915750130876015767)
      ·
        refine ⟨465817255373625196314023651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310544836915750130876015767 465817255373625196314023651)
        ·
          refine ⟨698725883060437794471035477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465817255373625196314023651 698725883060437794471035477)
          ·
            refine ⟨8188193942114505403957447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 698725883060437794471035477 8188193942114505403957447)
            ·
              refine ⟨12282290913171758105936171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8188193942114505403957447 12282290913171758105936171)
              ·
                refine ⟨18423436369757637158904257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12282290913171758105936171 18423436369757637158904257)
                ·
                  refine ⟨13817577277318227869178193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18423436369757637158904257 13817577277318227869178193)
                  ·
                    refine ⟨10363182957988670901883645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13817577277318227869178193 10363182957988670901883645)
                    ·
                      refine ⟨3886193609245751588206367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363182957988670901883645 3886193609245751588206367)
                      ·
                        rfl

theorem cell23_7568335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_7568335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568335 prefixEnd_7568335 := by exact prefixLift 7568335
  have htrace : WordTrace (prefixWord ++ tailWord_7568335) baseStart_7568335 baseEnd_7568335 := by
    simpa [prefixWord, tailWord_7568335, baseEnd_7568335] using wordTrace_append hprefix tailTrace_7568335
  have hstable : (prefixWord ++ tailWord_7568335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568335).length < 2 ^ (prefixWord ++ tailWord_7568335).sum := by decide
  have hdescent : baseEnd_7568335 < baseStart_7568335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568385 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7568385 : Nat := 118140960795 + 7568385 * 2 ^ 59
def prefixEnd_7568385 : Nat := 4983230072969 + 3 ^ 40 * 7568385 * 2
def baseEnd_7568385 : Nat := 1295406427759492130860379

theorem tailTrace_7568385 : CollatzResearch.WordTrace tailWord_7568385 prefixEnd_7568385 1295406427759492130860379 := by
  unfold tailWord_7568385
  simp only [CollatzResearch.WordTrace]
  refine ⟨276041678686041197095778609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184027785790694131397185739 276041678686041197095778609)
  ·
    refine ⟨207031259014530897821833957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276041678686041197095778609 207031259014530897821833957)
    ·
      refine ⟨38818361065224543341593867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207031259014530897821833957 38818361065224543341593867)
      ·
        refine ⟨58227541597836815012390801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38818361065224543341593867 58227541597836815012390801)
        ·
          refine ⟨43670656198377611259293101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58227541597836815012390801 43670656198377611259293101)
          ·
            refine ⟨16376496074391604222234913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43670656198377611259293101 16376496074391604222234913)
            ·
              refine ⟨12282372055793703166676185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16376496074391604222234913 12282372055793703166676185)
              ·
                refine ⟨9211779041845277375007139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12282372055793703166676185 9211779041845277375007139)
                ·
                  refine ⟨13817668562767916062510709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211779041845277375007139 13817668562767916062510709)
                  ·
                    refine ⟨1295406427759492130860379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13817668562767916062510709 1295406427759492130860379)
                    ·
                      rfl

theorem cell23_7568385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7568385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568385 prefixEnd_7568385 := by exact prefixLift 7568385
  have htrace : WordTrace (prefixWord ++ tailWord_7568385) baseStart_7568385 baseEnd_7568385 := by
    simpa [prefixWord, tailWord_7568385, baseEnd_7568385] using wordTrace_append hprefix tailTrace_7568385
  have hstable : (prefixWord ++ tailWord_7568385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568385).length < 2 ^ (prefixWord ++ tailWord_7568385).sum := by decide
  have hdescent : baseEnd_7568385 < baseStart_7568385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568405 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_7568405 : Nat := 118140960795 + 7568405 * 2 ^ 59
def prefixEnd_7568405 : Nat := 4983230072969 + 3 ^ 40 * 7568405 * 2
def baseEnd_7568405 : Nat := 3886229552891566314331045

theorem tailTrace_7568405 : CollatzResearch.WordTrace tailWord_7568405 prefixEnd_7568405 3886229552891566314331045 := by
  unfold tailWord_7568405
  simp only [CollatzResearch.WordTrace]
  refine ⟨276042408145968740511506669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184028272097312493674337779 276042408145968740511506669)
  ·
    refine ⟨103515903054738277691815001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276042408145968740511506669 103515903054738277691815001)
    ·
      refine ⟨77636927291053708268861251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103515903054738277691815001 77636927291053708268861251)
      ·
        refine ⟨116455390936580562403291877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77636927291053708268861251 116455390936580562403291877)
        ·
          refine ⟨21835385800608855450617227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116455390936580562403291877 21835385800608855450617227)
          ·
            refine ⟨32753078700913283175925841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21835385800608855450617227 32753078700913283175925841)
            ·
              refine ⟨24564809025684962381944381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32753078700913283175925841 24564809025684962381944381)
              ·
                refine ⟨9211803384631860893229143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24564809025684962381944381 9211803384631860893229143)
                ·
                  refine ⟨13817705076947791339843715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211803384631860893229143 13817705076947791339843715)
                  ·
                    refine ⟨20726557615421687009765573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13817705076947791339843715 20726557615421687009765573)
                    ·
                      refine ⟨3886229552891566314331045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20726557615421687009765573 3886229552891566314331045)
                      ·
                        rfl

theorem cell23_7568405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_7568405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568405 prefixEnd_7568405 := by exact prefixLift 7568405
  have htrace : WordTrace (prefixWord ++ tailWord_7568405) baseStart_7568405 baseEnd_7568405 := by
    simpa [prefixWord, tailWord_7568405, baseEnd_7568405] using wordTrace_append hprefix tailTrace_7568405
  have hstable : (prefixWord ++ tailWord_7568405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568405).length < 2 ^ (prefixWord ++ tailWord_7568405).sum := by decide
  have hdescent : baseEnd_7568405 < baseStart_7568405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568408 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7568408 : Nat := 118140960795 + 7568408 * 2 ^ 59
def prefixEnd_7568408 : Nat := 4983230072969 + 3 ^ 40 * 7568408 * 2
def baseEnd_7568408 : Nat := 3886231093333529802593531

theorem tailTrace_7568408 : CollatzResearch.WordTrace tailWord_7568408 prefixEnd_7568408 3886231093333529802593531 := by
  unfold tailWord_7568408
  simp only [CollatzResearch.WordTrace]
  refine ⟨138021258782478936011932939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184028345043305248015910585 138021258782478936011932939)
  ·
    refine ⟨207031888173718404017899409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138021258782478936011932939 207031888173718404017899409)
    ·
      refine ⟨155273916130288803013424557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207031888173718404017899409 155273916130288803013424557)
      ·
        refine ⟨58227718548858301130034209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155273916130288803013424557 58227718548858301130034209)
        ·
          refine ⟨43670788911643725847525657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58227718548858301130034209 43670788911643725847525657)
          ·
            refine ⟨32753091683732794385644243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43670788911643725847525657 32753091683732794385644243)
            ·
              refine ⟨49129637525599191578466365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32753091683732794385644243 49129637525599191578466365)
              ·
                refine ⟨18423614072099696841924887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49129637525599191578466365 18423614072099696841924887)
                ·
                  refine ⟨27635421108149545262887331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18423614072099696841924887 27635421108149545262887331)
                  ·
                    refine ⟨41453131662224317894330997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27635421108149545262887331 41453131662224317894330997)
                    ·
                      refine ⟨3886231093333529802593531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41453131662224317894330997 3886231093333529802593531)
                      ·
                        rfl

theorem cell23_7568408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7568408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568408 prefixEnd_7568408 := by exact prefixLift 7568408
  have htrace : WordTrace (prefixWord ++ tailWord_7568408) baseStart_7568408 baseEnd_7568408 := by
    simpa [prefixWord, tailWord_7568408, baseEnd_7568408] using wordTrace_append hprefix tailTrace_7568408
  have hstable : (prefixWord ++ tailWord_7568408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568408).length < 2 ^ (prefixWord ++ tailWord_7568408).sum := by decide
  have hdescent : baseEnd_7568408 < baseStart_7568408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568416 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7568416 : Nat := 118140960795 + 7568416 * 2 ^ 59
def prefixEnd_7568416 : Nat := 4983230072969 + 3 ^ 40 * 7568416 * 2
def baseEnd_7568416 : Nat := 3886235201178765771293495

theorem tailTrace_7568416 : CollatzResearch.WordTrace tailWord_7568416 prefixEnd_7568416 3886235201178765771293495 := by
  unfold tailWord_7568416
  simp only [CollatzResearch.WordTrace]
  refine ⟨138021404674464444695078551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184028539565952592926771401 138021404674464444695078551)
  ·
    refine ⟨207032107011696667042617827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138021404674464444695078551 207032107011696667042617827)
    ·
      refine ⟨310548160517545000563926741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207032107011696667042617827 310548160517545000563926741)
      ·
        refine ⟨7278472512129960950717033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 310548160517545000563926741 7278472512129960950717033)
        ·
          refine ⟨5458854384097470713037775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7278472512129960950717033 5458854384097470713037775)
          ·
            refine ⟨8188281576146206069556663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458854384097470713037775 8188281576146206069556663)
            ·
              refine ⟨12282422364219309104334995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8188281576146206069556663 12282422364219309104334995)
              ·
                refine ⟨18423633546328963656502493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12282422364219309104334995 18423633546328963656502493)
                ·
                  refine ⟨6908862579873361371188435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18423633546328963656502493 6908862579873361371188435)
                  ·
                    refine ⟨10363293869810042056782653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6908862579873361371188435 10363293869810042056782653)
                    ·
                      refine ⟨3886235201178765771293495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363293869810042056782653 3886235201178765771293495)
                      ·
                        rfl

theorem cell23_7568416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7568416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568416 prefixEnd_7568416 := by exact prefixLift 7568416
  have htrace : WordTrace (prefixWord ++ tailWord_7568416) baseStart_7568416 baseEnd_7568416 := by
    simpa [prefixWord, tailWord_7568416, baseEnd_7568416] using wordTrace_append hprefix tailTrace_7568416
  have hstable : (prefixWord ++ tailWord_7568416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568416).length < 2 ^ (prefixWord ++ tailWord_7568416).sum := by decide
  have hdescent : baseEnd_7568416 < baseStart_7568416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568418 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7568418 : Nat := 118140960795 + 7568418 * 2 ^ 59
def prefixEnd_7568418 : Nat := 4983230072969 + 3 ^ 40 * 7568418 * 2
def baseEnd_7568418 : Nat := 3886236228140074763468485

theorem tailTrace_7568418 : CollatzResearch.WordTrace tailWord_7568418 prefixEnd_7568418 3886236228140074763468485 := by
  unfold tailWord_7568418
  simp only [CollatzResearch.WordTrace]
  refine ⟨69010720573730410932932477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184028588196614429154486605 69010720573730410932932477)
  ·
    refine ⟨25879020215148904099849679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69010720573730410932932477 25879020215148904099849679)
    ·
      refine ⟨38818530322723356149774519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25879020215148904099849679 38818530322723356149774519)
      ·
        refine ⟨58227795484085034224661779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38818530322723356149774519 58227795484085034224661779)
        ·
          refine ⟨87341693226127551336992669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58227795484085034224661779 87341693226127551336992669)
          ·
            refine ⟨32753134959797831751372251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87341693226127551336992669 32753134959797831751372251)
            ·
              refine ⟨49129702439696747627058377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32753134959797831751372251 49129702439696747627058377)
              ·
                refine ⟨36847276829772560720293783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49129702439696747627058377 36847276829772560720293783)
                ·
                  refine ⟨55270915244658841080440675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36847276829772560720293783 55270915244658841080440675)
                  ·
                    refine ⟨82906372866988261620661013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55270915244658841080440675 82906372866988261620661013)
                    ·
                      refine ⟨3886236228140074763468485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82906372866988261620661013 3886236228140074763468485)
                      ·
                        rfl

theorem cell23_7568418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7568418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568418 prefixEnd_7568418 := by exact prefixLift 7568418
  have htrace : WordTrace (prefixWord ++ tailWord_7568418) baseStart_7568418 baseEnd_7568418 := by
    simpa [prefixWord, tailWord_7568418, baseEnd_7568418] using wordTrace_append hprefix tailTrace_7568418
  have hstable : (prefixWord ++ tailWord_7568418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568418).length < 2 ^ (prefixWord ++ tailWord_7568418).sum := by decide
  have hdescent : baseEnd_7568418 < baseStart_7568418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568455 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_7568455 : Nat := 118140960795 + 7568455 * 2 ^ 59
def prefixEnd_7568455 : Nat := 4983230072969 + 3 ^ 40 * 7568455 * 2
def baseEnd_7568455 : Nat := 3886255226924291118705815

theorem tailTrace_7568455 : CollatzResearch.WordTrace tailWord_7568455 prefixEnd_7568455 3886255226924291118705815 := by
  unfold tailWord_7568455
  simp only [CollatzResearch.WordTrace]
  refine ⟨276044231795787599050826819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184029487863858399367217879 276044231795787599050826819)
  ·
    refine ⟨414066347693681398576240229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276044231795787599050826819 414066347693681398576240229)
    ·
      refine ⟨77637440192565262233045043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414066347693681398576240229 77637440192565262233045043)
      ·
        refine ⟨116456160288847893349567565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77637440192565262233045043 116456160288847893349567565)
        ·
          refine ⟨43671060108317960006087837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116456160288847893349567565 43671060108317960006087837)
          ·
            refine ⟨16376647540619235002282939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43671060108317960006087837 16376647540619235002282939)
            ·
              refine ⟨24564971310928852503424409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16376647540619235002282939 24564971310928852503424409)
              ·
                refine ⟨18423728483196639377568307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24564971310928852503424409 18423728483196639377568307)
                ·
                  refine ⟨27635592724794959066352461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18423728483196639377568307 27635592724794959066352461)
                  ·
                    refine ⟨10363347271798109649882173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27635592724794959066352461 10363347271798109649882173)
                    ·
                      refine ⟨3886255226924291118705815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363347271798109649882173 3886255226924291118705815)
                      ·
                        rfl

theorem cell23_7568455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_7568455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568455 prefixEnd_7568455 := by exact prefixLift 7568455
  have htrace : WordTrace (prefixWord ++ tailWord_7568455) baseStart_7568455 baseEnd_7568455 := by
    simpa [prefixWord, tailWord_7568455, baseEnd_7568455] using wordTrace_append hprefix tailTrace_7568455
  have hstable : (prefixWord ++ tailWord_7568455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568455).length < 2 ^ (prefixWord ++ tailWord_7568455).sum := by decide
  have hdescent : baseEnd_7568455 < baseStart_7568455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568468 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_7568468 : Nat := 118140960795 + 7568468 * 2 ^ 59
def prefixEnd_7568468 : Nat := 4983230072969 + 3 ^ 40 * 7568468 * 2
def baseEnd_7568468 : Nat := 3886261902172799567843255

theorem tailTrace_7568468 : CollatzResearch.WordTrace tailWord_7568468 prefixEnd_7568468 3886261902172799567843255 := by
  unfold tailWord_7568468
  simp only [CollatzResearch.WordTrace]
  refine ⟨138022352972370251135525029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184029803963160334847366705 138022352972370251135525029)
  ·
    refine ⟨25879191182319422087910943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138022352972370251135525029 25879191182319422087910943)
    ·
      refine ⟨38818786773479133131866415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25879191182319422087910943 38818786773479133131866415)
      ·
        refine ⟨58228180160218699697799623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38818786773479133131866415 58228180160218699697799623)
        ·
          refine ⟨87342270240328049546699435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58228180160218699697799623 87342270240328049546699435)
          ·
            refine ⟨131013405360492074320049153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87342270240328049546699435 131013405360492074320049153)
            ·
              refine ⟨98260054020369055740036865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131013405360492074320049153 98260054020369055740036865)
              ·
                refine ⟨73695040515276791805027649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98260054020369055740036865 73695040515276791805027649)
                ·
                  refine ⟨55271280386457593853770737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73695040515276791805027649 55271280386457593853770737)
                  ·
                    refine ⟨41453460289843195390328053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55271280386457593853770737 41453460289843195390328053)
                    ·
                      refine ⟨3886261902172799567843255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41453460289843195390328053 3886261902172799567843255)
                      ·
                        rfl

theorem cell23_7568468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_7568468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568468 prefixEnd_7568468 := by exact prefixLift 7568468
  have htrace : WordTrace (prefixWord ++ tailWord_7568468) baseStart_7568468 baseEnd_7568468 := by
    simpa [prefixWord, tailWord_7568468, baseEnd_7568468] using wordTrace_append hprefix tailTrace_7568468
  have hstable : (prefixWord ++ tailWord_7568468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568468).length < 2 ^ (prefixWord ++ tailWord_7568468).sum := by decide
  have hdescent : baseEnd_7568468 < baseStart_7568468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568472 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_7568472 : Nat := 118140960795 + 7568472 * 2 ^ 59
def prefixEnd_7568472 : Nat := 4983230072969 + 3 ^ 40 * 7568472 * 2
def baseEnd_7568472 : Nat := 3886263956095417552193237

theorem tailTrace_7568472 : CollatzResearch.WordTrace tailWord_7568472 prefixEnd_7568472 3886263956095417552193237 := by
  unfold tailWord_7568472
  simp only [CollatzResearch.WordTrace]
  refine ⟨138022425918363005477097835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184029901224484007302797113 138022425918363005477097835)
  ·
    refine ⟨207033638877544508215646753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138022425918363005477097835 207033638877544508215646753)
    ·
      refine ⟨155275229158158381161735065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207033638877544508215646753 155275229158158381161735065)
      ·
        refine ⟨116456421868618785871301299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155275229158158381161735065 116456421868618785871301299)
        ·
          refine ⟨174684632802928178806951949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116456421868618785871301299 174684632802928178806951949)
          ·
            refine ⟨65506737301098067052606981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174684632802928178806951949 65506737301098067052606981)
            ·
              refine ⟨12282513243955887572363809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65506737301098067052606981 12282513243955887572363809)
              ·
                refine ⟨9211884932966915679272857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12282513243955887572363809 9211884932966915679272857)
                ·
                  refine ⟨6908913699725186759454643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9211884932966915679272857 6908913699725186759454643)
                  ·
                    refine ⟨10363370549587780139181965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6908913699725186759454643 10363370549587780139181965)
                    ·
                      refine ⟨3886263956095417552193237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363370549587780139181965 3886263956095417552193237)
                      ·
                        rfl

theorem cell23_7568472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_7568472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568472 prefixEnd_7568472 := by exact prefixLift 7568472
  have htrace : WordTrace (prefixWord ++ tailWord_7568472) baseStart_7568472 baseEnd_7568472 := by
    simpa [prefixWord, tailWord_7568472, baseEnd_7568472] using wordTrace_append hprefix tailTrace_7568472
  have hstable : (prefixWord ++ tailWord_7568472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568472).length < 2 ^ (prefixWord ++ tailWord_7568472).sum := by decide
  have hdescent : baseEnd_7568472 < baseStart_7568472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568508 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_7568508 : Nat := 118140960795 + 7568508 * 2 ^ 59
def prefixEnd_7568508 : Nat := 4983230072969 + 3 ^ 40 * 7568508 * 2
def baseEnd_7568508 : Nat := 3886282441398979411343071

theorem tailTrace_7568508 : CollatzResearch.WordTrace tailWord_7568508 prefixEnd_7568508 3886282441398979411343071 := by
  unfold tailWord_7568508
  simp only [CollatzResearch.WordTrace]
  refine ⟨138023082432297794551253089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184030776576397059401670785 138023082432297794551253089)
  ·
    refine ⟨103517311824223345913439817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138023082432297794551253089 103517311824223345913439817)
    ·
      refine ⟨77637983868167509435079863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103517311824223345913439817 77637983868167509435079863)
      ·
        refine ⟨116456975802251264152619795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77637983868167509435079863 116456975802251264152619795)
        ·
          refine ⟨174685463703376896228929693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116456975802251264152619795 174685463703376896228929693)
          ·
            refine ⟨65507048888766336085848635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174685463703376896228929693 65507048888766336085848635)
            ·
              refine ⟨98260573333149504128772953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65507048888766336085848635 98260573333149504128772953)
              ·
                refine ⟨73695429999862128096579715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98260573333149504128772953 73695429999862128096579715)
                ·
                  refine ⟨110543144999793192144869573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73695429999862128096579715 110543144999793192144869573)
                  ·
                    refine ⟨20726839687461223527163045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110543144999793192144869573 20726839687461223527163045)
                    ·
                      refine ⟨3886282441398979411343071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20726839687461223527163045 3886282441398979411343071)
                      ·
                        rfl

theorem cell23_7568508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_7568508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568508 prefixEnd_7568508 := by exact prefixLift 7568508
  have htrace : WordTrace (prefixWord ++ tailWord_7568508) baseStart_7568508 baseEnd_7568508 := by
    simpa [prefixWord, tailWord_7568508, baseEnd_7568508] using wordTrace_append hprefix tailTrace_7568508
  have hstable : (prefixWord ++ tailWord_7568508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568508).length < 2 ^ (prefixWord ++ tailWord_7568508).sum := by decide
  have hdescent : baseEnd_7568508 < baseStart_7568508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568510 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7568510 : Nat := 118140960795 + 7568510 * 2 ^ 59
def prefixEnd_7568510 : Nat := 4983230072969 + 3 ^ 40 * 7568510 * 2
def baseEnd_7568510 : Nat := 3886283468360288403518063

theorem tailTrace_7568510 : CollatzResearch.WordTrace tailWord_7568510 prefixEnd_7568510 3886283468360288403518063 := by
  unfold tailWord_7568510
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505779726323542930509873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184030825207058895629385989 34505779726323542930509873)
  ·
    refine ⟨25879334794742657197882405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34505779726323542930509873 25879334794742657197882405)
    ·
      refine ⟨4852375274014248224602951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25879334794742657197882405 4852375274014248224602951)
      ·
        refine ⟨7278562911021372336904427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4852375274014248224602951 7278562911021372336904427)
        ·
          refine ⟨10917844366532058505356641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278562911021372336904427 10917844366532058505356641)
          ·
            refine ⟨8188383274899043879017481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10917844366532058505356641 8188383274899043879017481)
            ·
              refine ⟨6141287456174282909263111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8188383274899043879017481 6141287456174282909263111)
              ·
                refine ⟨9211931184261424363894667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141287456174282909263111 9211931184261424363894667)
                ·
                  refine ⟨13817896776392136545842001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211931184261424363894667 13817896776392136545842001)
                  ·
                    refine ⟨10363422582294102409381501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13817896776392136545842001 10363422582294102409381501)
                    ·
                      refine ⟨3886283468360288403518063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363422582294102409381501 3886283468360288403518063)
                      ·
                        rfl

theorem cell23_7568510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7568510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568510 prefixEnd_7568510 := by exact prefixLift 7568510
  have htrace : WordTrace (prefixWord ++ tailWord_7568510) baseStart_7568510 baseEnd_7568510 := by
    simpa [prefixWord, tailWord_7568510, baseEnd_7568510] using wordTrace_append hprefix tailTrace_7568510
  have hstable : (prefixWord ++ tailWord_7568510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568510).length < 2 ^ (prefixWord ++ tailWord_7568510).sum := by decide
  have hdescent : baseEnd_7568510 < baseStart_7568510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568516 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_7568516 : Nat := 118140960795 + 7568516 * 2 ^ 59
def prefixEnd_7568516 : Nat := 4983230072969 + 3 ^ 40 * 7568516 * 2
def baseEnd_7568516 : Nat := 3886286549244215380043035

theorem tailTrace_7568516 : CollatzResearch.WordTrace tailWord_7568516 prefixEnd_7568516 3886286549244215380043035 := by
  unfold tailWord_7568516
  simp only [CollatzResearch.WordTrace]
  refine ⟨138023228324283303234398701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184030971099044404312531601 138023228324283303234398701)
  ·
    refine ⟨51758710621606238712899513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138023228324283303234398701 51758710621606238712899513)
    ·
      refine ⟨38819032966204679034674635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51758710621606238712899513 38819032966204679034674635)
      ·
        refine ⟨58228549449307018552011953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38819032966204679034674635 58228549449307018552011953)
        ·
          refine ⟨43671412086980263914008965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58228549449307018552011953 43671412086980263914008965)
          ·
            refine ⟨8188389766308799483876681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43671412086980263914008965 8188389766308799483876681)
            ·
              refine ⟨6141292324731599612907511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8188389766308799483876681 6141292324731599612907511)
              ·
                refine ⟨9211938487097399419361267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141292324731599612907511 9211938487097399419361267)
                ·
                  refine ⟨13817907730646099129041901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211938487097399419361267 13817907730646099129041901)
                  ·
                    refine ⟨5181715398992287173390713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13817907730646099129041901 5181715398992287173390713)
                    ·
                      refine ⟨3886286549244215380043035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181715398992287173390713 3886286549244215380043035)
                      ·
                        rfl

theorem cell23_7568516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_7568516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568516 prefixEnd_7568516 := by exact prefixLift 7568516
  have htrace : WordTrace (prefixWord ++ tailWord_7568516) baseStart_7568516 baseEnd_7568516 := by
    simpa [prefixWord, tailWord_7568516, baseEnd_7568516] using wordTrace_append hprefix tailTrace_7568516
  have hstable : (prefixWord ++ tailWord_7568516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568516).length < 2 ^ (prefixWord ++ tailWord_7568516).sum := by decide
  have hdescent : baseEnd_7568516 < baseStart_7568516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568535 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 7]
def baseStart_7568535 : Nat := 118140960795 + 7568535 * 2 ^ 59
def prefixEnd_7568535 : Nat := 4983230072969 + 3 ^ 40 * 7568535 * 2
def baseEnd_7568535 : Nat := 431810700597405645078383

theorem tailTrace_7568535 : CollatzResearch.WordTrace tailWord_7568535 prefixEnd_7568535 431810700597405645078383 := by
  unfold tailWord_7568535
  simp only [CollatzResearch.WordTrace]
  refine ⟨276047149635497772713739059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184031433090331848475826039 276047149635497772713739059)
  ·
    refine ⟨414070724453246659070608589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276047149635497772713739059 414070724453246659070608589)
    ·
      refine ⟨155276521669967497151478221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414070724453246659070608589 155276521669967497151478221)
      ·
        refine ⟨58228695626237811431804333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155276521669967497151478221 58228695626237811431804333)
        ·
          refine ⟨21835760859839179286926625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58228695626237811431804333 21835760859839179286926625)
          ·
            refine ⟨16376820644879384465194969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21835760859839179286926625 16376820644879384465194969)
            ·
              refine ⟨12282615483659538348896227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16376820644879384465194969 12282615483659538348896227)
              ·
                refine ⟨18423923225489307523344341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12282615483659538348896227 18423923225489307523344341)
                ·
                  refine ⟨431810700597405645078383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18423923225489307523344341 431810700597405645078383)
                  ·
                    rfl

theorem cell23_7568535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 7].length) (baseStart_7568535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568535 prefixEnd_7568535 := by exact prefixLift 7568535
  have htrace : WordTrace (prefixWord ++ tailWord_7568535) baseStart_7568535 baseEnd_7568535 := by
    simpa [prefixWord, tailWord_7568535, baseEnd_7568535] using wordTrace_append hprefix tailTrace_7568535
  have hstable : (prefixWord ++ tailWord_7568535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568535).length < 2 ^ (prefixWord ++ tailWord_7568535).sum := by decide
  have hdescent : baseEnd_7568535 < baseStart_7568535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568542 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7568542 : Nat := 118140960795 + 7568542 * 2 ^ 59
def prefixEnd_7568542 : Nat := 4983230072969 + 3 ^ 40 * 7568542 * 2
def baseEnd_7568542 : Nat := 3886299899741232278317915

theorem tailTrace_7568542 : CollatzResearch.WordTrace tailWord_7568542 prefixEnd_7568542 3886299899741232278317915 := by
  unfold tailWord_7568542
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505925618309051613655485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184031603297648275272829253 34505925618309051613655485)
  ·
    refine ⟨12939722106865894355120807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34505925618309051613655485 12939722106865894355120807)
    ·
      refine ⟨19409583160298841532681211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12939722106865894355120807 19409583160298841532681211)
      ·
        refine ⟨29114374740448262299021817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19409583160298841532681211 29114374740448262299021817)
        ·
          refine ⟨21835781055336196724266363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29114374740448262299021817 21835781055336196724266363)
          ·
            refine ⟨32753671583004295086399545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21835781055336196724266363 32753671583004295086399545)
            ·
              refine ⟨24565253687253221314799659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32753671583004295086399545 24565253687253221314799659)
              ·
                refine ⟨36847880530879831972199489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24565253687253221314799659 36847880530879831972199489)
                ·
                  refine ⟨27635910398159873979149617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36847880530879831972199489 27635910398159873979149617)
                  ·
                    refine ⟨20726932798619905484362213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27635910398159873979149617 20726932798619905484362213)
                    ·
                      refine ⟨3886299899741232278317915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20726932798619905484362213 3886299899741232278317915)
                      ·
                        rfl

theorem cell23_7568542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7568542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568542 prefixEnd_7568542 := by exact prefixLift 7568542
  have htrace : WordTrace (prefixWord ++ tailWord_7568542) baseStart_7568542 baseEnd_7568542 := by
    simpa [prefixWord, tailWord_7568542, baseEnd_7568542] using wordTrace_append hprefix tailTrace_7568542
  have hstable : (prefixWord ++ tailWord_7568542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568542).length < 2 ^ (prefixWord ++ tailWord_7568542).sum := by decide
  have hdescent : baseEnd_7568542 < baseStart_7568542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568545 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7568545 : Nat := 118140960795 + 7568545 * 2 ^ 59
def prefixEnd_7568545 : Nat := 4983230072969 + 3 ^ 40 * 7568545 * 2
def baseEnd_7568545 : Nat := 3886301440183195766580401

theorem tailTrace_7568545 : CollatzResearch.WordTrace tailWord_7568545 prefixEnd_7568545 3886301440183195766580401 := by
  unfold tailWord_7568545
  simp only [CollatzResearch.WordTrace]
  refine ⟨276047514365461544421603089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184031676243641029614402059 276047514365461544421603089)
  ·
    refine ⟨207035635774096158316202317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276047514365461544421603089 207035635774096158316202317)
    ·
      refine ⟨77638363415286059368575869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207035635774096158316202317 77638363415286059368575869)
      ·
        refine ⟨29114386280732272263215951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77638363415286059368575869 29114386280732272263215951)
        ·
          refine ⟨43671579421098408394823927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29114386280732272263215951 43671579421098408394823927)
          ·
            refine ⟨65507369131647612592235891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43671579421098408394823927 65507369131647612592235891)
            ·
              refine ⟨98261053697471418888353837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65507369131647612592235891 98261053697471418888353837)
              ·
                refine ⟨36847895136551782083132689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98261053697471418888353837 36847895136551782083132689)
                ·
                  refine ⟨27635921352413836562349517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36847895136551782083132689 27635921352413836562349517)
                  ·
                    refine ⟨10363470507155188710881069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27635921352413836562349517 10363470507155188710881069)
                    ·
                      refine ⟨3886301440183195766580401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363470507155188710881069 3886301440183195766580401)
                      ·
                        rfl

theorem cell23_7568545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7568545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568545 prefixEnd_7568545 := by exact prefixLift 7568545
  have htrace : WordTrace (prefixWord ++ tailWord_7568545) baseStart_7568545 baseEnd_7568545 := by
    simpa [prefixWord, tailWord_7568545, baseEnd_7568545] using wordTrace_append hprefix tailTrace_7568545
  have hstable : (prefixWord ++ tailWord_7568545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568545).length < 2 ^ (prefixWord ++ tailWord_7568545).sum := by decide
  have hdescent : baseEnd_7568545 < baseStart_7568545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568546 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7568546 : Nat := 118140960795 + 7568546 * 2 ^ 59
def prefixEnd_7568546 : Nat := 4983230072969 + 3 ^ 40 * 7568546 * 2
def baseEnd_7568546 : Nat := 3886301953663850262667897

theorem tailTrace_7568546 : CollatzResearch.WordTrace tailWord_7568546 prefixEnd_7568546 3886301953663850262667897 := by
  unfold tailWord_7568546
  simp only [CollatzResearch.WordTrace]
  refine ⟨69011887709614480398097373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184031700558971947728259661 69011887709614480398097373)
  ·
    refine ⟨25879457891105430149286515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69011887709614480398097373 25879457891105430149286515)
    ·
      refine ⟨38819186836658145223929773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25879457891105430149286515 38819186836658145223929773)
      ·
        refine ⟨14557195063746804458973665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38819186836658145223929773 14557195063746804458973665)
        ·
          refine ⟨10917896297810103344230249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14557195063746804458973665 10917896297810103344230249)
          ·
            refine ⟨8188422223357577508172687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10917896297810103344230249 8188422223357577508172687)
            ·
              refine ⟨12282633335036366262259031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8188422223357577508172687 12282633335036366262259031)
              ·
                refine ⟨18423950002554549393388547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12282633335036366262259031 18423950002554549393388547)
                ·
                  refine ⟨27635925003831824090082821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18423950002554549393388547 27635925003831824090082821)
                  ·
                    refine ⟨5181735938218467016890529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27635925003831824090082821 5181735938218467016890529)
                    ·
                      refine ⟨3886301953663850262667897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181735938218467016890529 3886301953663850262667897)
                      ·
                        rfl

theorem cell23_7568546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7568546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568546 prefixEnd_7568546 := by exact prefixLift 7568546
  have htrace : WordTrace (prefixWord ++ tailWord_7568546) baseStart_7568546 baseEnd_7568546 := by
    simpa [prefixWord, tailWord_7568546, baseEnd_7568546] using wordTrace_append hprefix tailTrace_7568546
  have hstable : (prefixWord ++ tailWord_7568546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568546).length < 2 ^ (prefixWord ++ tailWord_7568546).sum := by decide
  have hdescent : baseEnd_7568546 < baseStart_7568546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568622 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_7568622 : Nat := 118140960795 + 7568622 * 2 ^ 59
def prefixEnd_7568622 : Nat := 4983230072969 + 3 ^ 40 * 7568622 * 2
def baseEnd_7568622 : Nat := 3886340978193591965317547

theorem tailTrace_7568622 : CollatzResearch.WordTrace tailWord_7568622 prefixEnd_7568622 3886340978193591965317547 := by
  unfold tailWord_7568622
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506290348272823321519515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184033548524121724381437413 34506290348272823321519515)
  ·
    refine ⟨51759435522409234982279273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34506290348272823321519515 51759435522409234982279273)
    ·
      refine ⟨38819576641806926236709455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51759435522409234982279273 38819576641806926236709455)
      ·
        refine ⟨58229364962710389355064183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38819576641806926236709455 58229364962710389355064183)
        ·
          refine ⟨87344047444065584032596275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58229364962710389355064183 87344047444065584032596275)
          ·
            refine ⟨131016071166098376048894413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87344047444065584032596275 131016071166098376048894413)
            ·
              refine ⟨49131026687286891018335405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131016071166098376048894413 49131026687286891018335405)
              ·
                refine ⟨18424135007732584131875777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49131026687286891018335405 18424135007732584131875777)
                ·
                  refine ⟨13818101255799438098906833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18424135007732584131875777 13818101255799438098906833)
                  ·
                    refine ⟨10363575941849578574180125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13818101255799438098906833 10363575941849578574180125)
                    ·
                      refine ⟨3886340978193591965317547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363575941849578574180125 3886340978193591965317547)
                      ·
                        rfl

theorem cell23_7568622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_7568622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568622 prefixEnd_7568622 := by exact prefixLift 7568622
  have htrace : WordTrace (prefixWord ++ tailWord_7568622) baseStart_7568622 baseEnd_7568622 := by
    simpa [prefixWord, tailWord_7568622, baseEnd_7568622] using wordTrace_append hprefix tailTrace_7568622
  have hstable : (prefixWord ++ tailWord_7568622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568622).length < 2 ^ (prefixWord ++ tailWord_7568622).sum := by decide
  have hdescent : baseEnd_7568622 < baseStart_7568622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568669 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_7568669 : Nat := 118140960795 + 7568669 * 2 ^ 59
def prefixEnd_7568669 : Nat := 4983230072969 + 3 ^ 40 * 7568669 * 2
def baseEnd_7568669 : Nat := 3886365111784353281429831

theorem tailTrace_7568669 : CollatzResearch.WordTrace tailWord_7568669 prefixEnd_7568669 3886365111784353281429831 := by
  unfold tailWord_7568669
  simp only [CollatzResearch.WordTrace]
  refine ⟨276052037017012313599117061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184034691344674875732744707 276052037017012313599117061)
  ·
    refine ⟨51759756940689808799834449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276052037017012313599117061 51759756940689808799834449)
    ·
      refine ⟨38819817705517356599875837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51759756940689808799834449 38819817705517356599875837)
      ·
        refine ⟨14557431639569008724953439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38819817705517356599875837 14557431639569008724953439)
        ·
          refine ⟨21836147459353513087430159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14557431639569008724953439 21836147459353513087430159)
          ·
            refine ⟨32754221189030269631145239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21836147459353513087430159 32754221189030269631145239)
            ·
              refine ⟨49131331783545404446717859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32754221189030269631145239 49131331783545404446717859)
              ·
                refine ⟨73696997675318106670076789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49131331783545404446717859 73696997675318106670076789)
                ·
                  refine ⟨6909093532061072500319699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73696997675318106670076789 6909093532061072500319699)
                  ·
                    refine ⟨10363640298091608750479549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909093532061072500319699 10363640298091608750479549)
                    ·
                      refine ⟨3886365111784353281429831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363640298091608750479549 3886365111784353281429831)
                      ·
                        rfl

theorem cell23_7568669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_7568669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568669 prefixEnd_7568669 := by exact prefixLift 7568669
  have htrace : WordTrace (prefixWord ++ tailWord_7568669) baseStart_7568669 baseEnd_7568669 := by
    simpa [prefixWord, tailWord_7568669, baseEnd_7568669] using wordTrace_append hprefix tailTrace_7568669
  have hstable : (prefixWord ++ tailWord_7568669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568669).length < 2 ^ (prefixWord ++ tailWord_7568669).sum := by decide
  have hdescent : baseEnd_7568669 < baseStart_7568669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568689 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 1, 5]
def baseStart_7568689 : Nat := 118140960795 + 7568689 * 2 ^ 59
def prefixEnd_7568689 : Nat := 4983230072969 + 3 ^ 40 * 7568689 * 2
def baseEnd_7568689 : Nat := 1295458460465814401059913

theorem tailTrace_7568689 : CollatzResearch.WordTrace tailWord_7568689 prefixEnd_7568689 1295458460465814401059913 := by
  unfold tailWord_7568689
  simp only [CollatzResearch.WordTrace]
  refine ⟨276052766476939857014845121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184035177651293238009896747 276052766476939857014845121)
  ·
    refine ⟨207039574857704892761133841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276052766476939857014845121 207039574857704892761133841)
    ·
      refine ⟨155279681143278669570850381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207039574857704892761133841 155279681143278669570850381)
      ·
        refine ⟨58229880428729501089068893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155279681143278669570850381 58229880428729501089068893)
        ·
          refine ⟨21836205160773562908400835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58229880428729501089068893 21836205160773562908400835)
          ·
            refine ⟨32754307741160344362601253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21836205160773562908400835 32754307741160344362601253)
            ·
              refine ⟨6141432701467564567987735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32754307741160344362601253 6141432701467564567987735)
              ·
                refine ⟨9212149052201346851981603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141432701467564567987735 9212149052201346851981603)
                ·
                  refine ⟨13818223578302020277972405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9212149052201346851981603 13818223578302020277972405)
                  ·
                    refine ⟨1295458460465814401059913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13818223578302020277972405 1295458460465814401059913)
                    ·
                      rfl

theorem cell23_7568689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_7568689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568689 prefixEnd_7568689 := by exact prefixLift 7568689
  have htrace : WordTrace (prefixWord ++ tailWord_7568689) baseStart_7568689 baseEnd_7568689 := by
    simpa [prefixWord, tailWord_7568689, baseEnd_7568689] using wordTrace_append hprefix tailTrace_7568689
  have hstable : (prefixWord ++ tailWord_7568689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568689).length < 2 ^ (prefixWord ++ tailWord_7568689).sum := by decide
  have hdescent : baseEnd_7568689 < baseStart_7568689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568759 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_7568759 : Nat := 118140960795 + 7568759 * 2 ^ 59
def prefixEnd_7568759 : Nat := 4983230072969 + 3 ^ 40 * 7568759 * 2
def baseEnd_7568759 : Nat := 3886411325043257929304417

theorem tailTrace_7568759 : CollatzResearch.WordTrace tailWord_7568759 prefixEnd_7568759 3886411325043257929304417 := by
  unfold tailWord_7568759
  simp only [CollatzResearch.WordTrace]
  refine ⟨276055319586686258969893331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184036879724457505979928887 276055319586686258969893331)
  ·
    refine ⟨414082979380029388454839997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276055319586686258969893331 414082979380029388454839997)
    ·
      refine ⟨155281117267511020670564999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414082979380029388454839997 155281117267511020670564999)
      ·
        refine ⟨232921675901266531005847499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155281117267511020670564999 232921675901266531005847499)
        ·
          refine ⟨349382513851899796508771249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232921675901266531005847499 349382513851899796508771249)
          ·
            refine ⟨262036885388924847381578437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349382513851899796508771249 262036885388924847381578437)
            ·
              refine ⟨49131916010423408884045957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262036885388924847381578437 49131916010423408884045957)
              ·
                refine ⟨9212234251954389165758617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49131916010423408884045957 9212234251954389165758617)
                ·
                  refine ⟨6909175688965791874318963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212234251954389165758617 6909175688965791874318963)
                  ·
                    refine ⟨10363763533448687811478445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909175688965791874318963 10363763533448687811478445)
                    ·
                      refine ⟨3886411325043257929304417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363763533448687811478445 3886411325043257929304417)
                      ·
                        rfl

theorem cell23_7568759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_7568759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568759 prefixEnd_7568759 := by exact prefixLift 7568759
  have htrace : WordTrace (prefixWord ++ tailWord_7568759) baseStart_7568759 baseEnd_7568759 := by
    simpa [prefixWord, tailWord_7568759, baseEnd_7568759] using wordTrace_append hprefix tailTrace_7568759
  have hstable : (prefixWord ++ tailWord_7568759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568759).length < 2 ^ (prefixWord ++ tailWord_7568759).sum := by decide
  have hdescent : baseEnd_7568759 < baseStart_7568759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568766 : List Nat := [4, 2, 3, 2, 1, 1, 2, 8]
def baseStart_7568766 : Nat := 118140960795 + 7568766 * 2 ^ 59
def prefixEnd_7568766 : Nat := 4983230072969 + 3 ^ 40 * 7568766 * 2
def baseEnd_7568766 : Nat := 143941293311401459330255

theorem tailTrace_7568766 : CollatzResearch.WordTrace tailWord_7568766 prefixEnd_7568766 143941293311401459330255 := by
  unfold tailWord_7568766
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506946862207612395674769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184037049931773932776932101 34506946862207612395674769)
  ·
    refine ⟨25880210146655709296756077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34506946862207612395674769 25880210146655709296756077)
    ·
      refine ⟨9705078804995890986283529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25880210146655709296756077 9705078804995890986283529)
      ·
        refine ⟨7278809103746918239712647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9705078804995890986283529 7278809103746918239712647)
        ·
          refine ⟨10918213655620377359568971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278809103746918239712647 10918213655620377359568971)
          ·
            refine ⟨16377320483430566039353457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10918213655620377359568971 16377320483430566039353457)
            ·
              refine ⟨12282990362572924529515093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16377320483430566039353457 12282990362572924529515093)
              ·
                refine ⟨143941293311401459330255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12282990362572924529515093 143941293311401459330255)
                ·
                  rfl

theorem cell23_7568766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_7568766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568766 prefixEnd_7568766 := by exact prefixLift 7568766
  have htrace : WordTrace (prefixWord ++ tailWord_7568766) baseStart_7568766 baseEnd_7568766 := by
    simpa [prefixWord, tailWord_7568766, baseEnd_7568766] using wordTrace_append hprefix tailTrace_7568766
  have hstable : (prefixWord ++ tailWord_7568766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568766).length < 2 ^ (prefixWord ++ tailWord_7568766).sum := by decide
  have hdescent : baseEnd_7568766 < baseStart_7568766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568770 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7568770 : Nat := 118140960795 + 7568770 * 2 ^ 59
def prefixEnd_7568770 : Nat := 4983230072969 + 3 ^ 40 * 7568770 * 2
def baseEnd_7568770 : Nat := 1295472324443485795422289

theorem tailTrace_7568770 : CollatzResearch.WordTrace tailWord_7568770 prefixEnd_7568770 1295472324443485795422289 := by
  unfold tailWord_7568770
  simp only [CollatzResearch.WordTrace]
  refine ⟨69013930197411601962135941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184037147193097605232362509 69013930197411601962135941)
  ·
    refine ⟨12940111912014675367900489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69013930197411601962135941 12940111912014675367900489)
    ·
      refine ⟨9705083934011006525925367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12940111912014675367900489 9705083934011006525925367)
      ·
        refine ⟨14557625901016509788888051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705083934011006525925367 14557625901016509788888051)
        ·
          refine ⟨21836438851524764683332077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14557625901016509788888051 21836438851524764683332077)
          ·
            refine ⟨8188664569321786756249529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21836438851524764683332077 8188664569321786756249529)
            ·
              refine ⟨6141498426991340067187147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8188664569321786756249529 6141498426991340067187147)
              ·
                refine ⟨9212247640487010100780721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141498426991340067187147 9212247640487010100780721)
                ·
                  refine ⟨6909185730365257575585541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212247640487010100780721 6909185730365257575585541)
                  ·
                    refine ⟨1295472324443485795422289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6909185730365257575585541 1295472324443485795422289)
                    ·
                      rfl

theorem cell23_7568770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7568770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568770 prefixEnd_7568770 := by exact prefixLift 7568770
  have htrace : WordTrace (prefixWord ++ tailWord_7568770) baseStart_7568770 baseEnd_7568770 := by
    simpa [prefixWord, tailWord_7568770, baseEnd_7568770] using wordTrace_append hprefix tailTrace_7568770
  have hstable : (prefixWord ++ tailWord_7568770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568770).length < 2 ^ (prefixWord ++ tailWord_7568770).sum := by decide
  have hdescent : baseEnd_7568770 < baseStart_7568770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568776 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7568776 : Nat := 118140960795 + 7568776 * 2 ^ 59
def prefixEnd_7568776 : Nat := 4983230072969 + 3 ^ 40 * 7568776 * 2
def baseEnd_7568776 : Nat := 3886420054214384362791839

theorem tailTrace_7568776 : CollatzResearch.WordTrace tailWord_7568776 prefixEnd_7568776 3886420054214384362791839 := by
  unfold tailWord_7568776
  simp only [CollatzResearch.WordTrace]
  refine ⟨138027969813812335436631091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184037293085083113915508121 138027969813812335436631091)
  ·
    refine ⟨207041954720718503154946637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138027969813812335436631091 207041954720718503154946637)
    ·
      refine ⟨77640733020269438683104989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207041954720718503154946637 77640733020269438683104989)
      ·
        refine ⟨29115274882601039506164371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77640733020269438683104989 29115274882601039506164371)
        ·
          refine ⟨43672912323901559259246557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29115274882601039506164371 43672912323901559259246557)
          ·
            refine ⟨16377342121463084722217459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43672912323901559259246557 16377342121463084722217459)
            ·
              refine ⟨24566013182194627083326189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16377342121463084722217459 24566013182194627083326189)
              ·
                refine ⟨9212254943322985156247321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24566013182194627083326189 9212254943322985156247321)
                ·
                  refine ⟨6909191207492238867185491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212254943322985156247321 6909191207492238867185491)
                  ·
                    refine ⟨10363786811238358300778237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909191207492238867185491 10363786811238358300778237)
                    ·
                      refine ⟨3886420054214384362791839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363786811238358300778237 3886420054214384362791839)
                      ·
                        rfl

theorem cell23_7568776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7568776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568776 prefixEnd_7568776 := by exact prefixLift 7568776
  have htrace : WordTrace (prefixWord ++ tailWord_7568776) baseStart_7568776 baseEnd_7568776 := by
    simpa [prefixWord, tailWord_7568776, baseEnd_7568776] using wordTrace_append hprefix tailTrace_7568776
  have hstable : (prefixWord ++ tailWord_7568776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568776).length < 2 ^ (prefixWord ++ tailWord_7568776).sum := by decide
  have hdescent : baseEnd_7568776 < baseStart_7568776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568785 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_7568785 : Nat := 118140960795 + 7568785 * 2 ^ 59
def prefixEnd_7568785 : Nat := 4983230072969 + 3 ^ 40 * 7568785 * 2
def baseEnd_7568785 : Nat := 3886424675540274827579297

theorem tailTrace_7568785 : CollatzResearch.WordTrace tailWord_7568785 prefixEnd_7568785 3886424675540274827579297 := by
  unfold tailWord_7568785
  simp only [CollatzResearch.WordTrace]
  refine ⟨276056267884592065410339809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184037511923061376940226539 276056267884592065410339809)
  ·
    refine ⟨207042200913444049057754857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276056267884592065410339809 207042200913444049057754857)
    ·
      refine ⟨155281650685083036793316143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207042200913444049057754857 155281650685083036793316143)
      ·
        refine ⟨232922476027624555189974215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155281650685083036793316143 232922476027624555189974215)
        ·
          refine ⟨349383714041436832784961323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232922476027624555189974215 349383714041436832784961323)
          ·
            refine ⟨524075571062155249177441985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349383714041436832784961323 524075571062155249177441985)
            ·
              refine ⟨393056678296616436883081489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524075571062155249177441985 393056678296616436883081489)
              ·
                refine ⟨294792508722462327662311117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393056678296616436883081489 294792508722462327662311117)
                ·
                  refine ⟨110547190770923372873366669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294792508722462327662311117 110547190770923372873366669)
                  ·
                    refine ⟨41455196539096264827512501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110547190770923372873366669 41455196539096264827512501)
                    ·
                      refine ⟨3886424675540274827579297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41455196539096264827512501 3886424675540274827579297)
                      ·
                        rfl

theorem cell23_7568785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_7568785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568785 prefixEnd_7568785 := by exact prefixLift 7568785
  have htrace : WordTrace (prefixWord ++ tailWord_7568785) baseStart_7568785 baseEnd_7568785 := by
    simpa [prefixWord, tailWord_7568785, baseEnd_7568785] using wordTrace_append hprefix tailTrace_7568785
  have hstable : (prefixWord ++ tailWord_7568785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568785).length < 2 ^ (prefixWord ++ tailWord_7568785).sum := by decide
  have hdescent : baseEnd_7568785 < baseStart_7568785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568799 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 3, 4, 2]
def baseStart_7568799 : Nat := 118140960795 + 7568799 * 2 ^ 59
def prefixEnd_7568799 : Nat := 4983230072969 + 3 ^ 40 * 7568799 * 2
def baseEnd_7568799 : Nat := 3886431864269437772804233

theorem tailTrace_7568799 : CollatzResearch.WordTrace tailWord_7568799 prefixEnd_7568799 3886431864269437772804233 := by
  unfold tailWord_7568799
  simp only [CollatzResearch.WordTrace]
  refine ⟨276056778506541345801349451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184037852337694230534232967 276056778506541345801349451)
  ·
    refine ⟨414085167759812018702024177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276056778506541345801349451 414085167759812018702024177)
    ·
      refine ⟨310563875819859014026518133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414085167759812018702024177 310563875819859014026518133)
      ·
        refine ⟨29115363358111782564986075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310563875819859014026518133 29115363358111782564986075)
        ·
          refine ⟨43673045037167673847479113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29115363358111782564986075 43673045037167673847479113)
          ·
            refine ⟨32754783777875755385609335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43673045037167673847479113 32754783777875755385609335)
            ·
              refine ⟨49132175666813633078414003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32754783777875755385609335 49132175666813633078414003)
              ·
                refine ⟨73698263500220449617621005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49132175666813633078414003 73698263500220449617621005)
                ·
                  refine ⟨27636848812582668606607877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73698263500220449617621005 27636848812582668606607877)
                  ·
                    refine ⟨5181909152359250363738977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27636848812582668606607877 5181909152359250363738977)
                    ·
                      refine ⟨3886431864269437772804233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5181909152359250363738977 3886431864269437772804233)
                      ·
                        rfl

theorem cell23_7568799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_7568799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568799 prefixEnd_7568799 := by exact prefixLift 7568799
  have htrace : WordTrace (prefixWord ++ tailWord_7568799) baseStart_7568799 baseEnd_7568799 := by
    simpa [prefixWord, tailWord_7568799, baseEnd_7568799] using wordTrace_append hprefix tailTrace_7568799
  have hstable : (prefixWord ++ tailWord_7568799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568799).length < 2 ^ (prefixWord ++ tailWord_7568799).sum := by decide
  have hdescent : baseEnd_7568799 < baseStart_7568799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568805 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 11]
def baseStart_7568805 : Nat := 118140960795 + 7568805 * 2 ^ 59
def prefixEnd_7568805 : Nat := 4983230072969 + 3 ^ 40 * 7568805 * 2
def baseEnd_7568805 : Nat := 431826105017040527703245

theorem tailTrace_7568805 : CollatzResearch.WordTrace tailWord_7568805 prefixEnd_7568805 431826105017040527703245 := by
  unfold tailWord_7568805
  simp only [CollatzResearch.WordTrace]
  refine ⟨276056997344519608826067869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184037998229679739217378579 276056997344519608826067869)
  ·
    refine ⟨103521374004194853309775451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276056997344519608826067869 103521374004194853309775451)
    ·
      refine ⟨155282061006292279964663177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103521374004194853309775451 155282061006292279964663177)
      ·
        refine ⟨116461545754719209973497383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155282061006292279964663177 116461545754719209973497383)
        ·
          refine ⟨174692318632078814960246075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116461545754719209973497383 174692318632078814960246075)
          ·
            refine ⟨262038477948118222440369113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174692318632078814960246075 262038477948118222440369113)
            ·
              refine ⟨196528858461088666830276835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262038477948118222440369113 196528858461088666830276835)
              ·
                refine ⟨294793287691633000245415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196528858461088666830276835 294793287691633000245415253)
                ·
                  refine ⟨431826105017040527703245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 294793287691633000245415253 431826105017040527703245)
                  ·
                    rfl

theorem cell23_7568805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_7568805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568805 prefixEnd_7568805 := by exact prefixLift 7568805
  have htrace : WordTrace (prefixWord ++ tailWord_7568805) baseStart_7568805 baseEnd_7568805 := by
    simpa [prefixWord, tailWord_7568805, baseEnd_7568805] using wordTrace_append hprefix tailTrace_7568805
  have hstable : (prefixWord ++ tailWord_7568805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568805).length < 2 ^ (prefixWord ++ tailWord_7568805).sum := by decide
  have hdescent : baseEnd_7568805 < baseStart_7568805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568815 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_7568815 : Nat := 118140960795 + 7568815 * 2 ^ 59
def prefixEnd_7568815 : Nat := 4983230072969 + 3 ^ 40 * 7568815 * 2
def baseEnd_7568815 : Nat := 3886440079959909710204159

theorem tailTrace_7568815 : CollatzResearch.WordTrace tailWord_7568815 prefixEnd_7568815 3886440079959909710204159 := by
  unfold tailWord_7568815
  simp only [CollatzResearch.WordTrace]
  refine ⟨276057362074483380533931899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184038241382988920355954599 276057362074483380533931899)
  ·
    refine ⟨414086043111725070800897849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276057362074483380533931899 414086043111725070800897849)
    ·
      refine ⟨310564532333793803100673387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414086043111725070800897849 310564532333793803100673387)
      ·
        refine ⟨465846798500690704651010081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310564532333793803100673387 465846798500690704651010081)
        ·
          refine ⟨349385098875518028488257561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465846798500690704651010081 349385098875518028488257561)
          ·
            refine ⟨262038824156638521366193171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349385098875518028488257561 262038824156638521366193171)
            ·
              refine ⟨393058236234957782049289757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262038824156638521366193171 393058236234957782049289757)
              ·
                refine ⟨147396838588109168268483659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393058236234957782049289757 147396838588109168268483659)
                ·
                  refine ⟨221095257882163752402725489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147396838588109168268483659 221095257882163752402725489)
                  ·
                    refine ⟨165821443411622814302044117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221095257882163752402725489 165821443411622814302044117)
                    ·
                      refine ⟨3886440079959909710204159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165821443411622814302044117 3886440079959909710204159)
                      ·
                        rfl

theorem cell23_7568815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_7568815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568815 prefixEnd_7568815 := by exact prefixLift 7568815
  have htrace : WordTrace (prefixWord ++ tailWord_7568815) baseStart_7568815 baseEnd_7568815 := by
    simpa [prefixWord, tailWord_7568815, baseEnd_7568815] using wordTrace_append hprefix tailTrace_7568815
  have hstable : (prefixWord ++ tailWord_7568815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568815).length < 2 ^ (prefixWord ++ tailWord_7568815).sum := by decide
  have hdescent : baseEnd_7568815 < baseStart_7568815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568832 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_7568832 : Nat := 118140960795 + 7568832 * 2 ^ 59
def prefixEnd_7568832 : Nat := 4983230072969 + 3 ^ 40 * 7568832 * 2
def baseEnd_7568832 : Nat := 3886448809131036143691581

theorem tailTrace_7568832 : CollatzResearch.WordTrace tailWord_7568832 prefixEnd_7568832 3886448809131036143691581 := by
  unfold tailWord_7568832
  simp only [CollatzResearch.WordTrace]
  refine ⟨138028991057710896218650375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184038654743614528291533833 138028991057710896218650375)
  ·
    refine ⟨207043486586566344327975563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138028991057710896218650375 207043486586566344327975563)
    ·
      refine ⟨310565229879849516491963345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207043486586566344327975563 310565229879849516491963345)
      ·
        refine ⟨232923922409887137368972509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310565229879849516491963345 232923922409887137368972509)
        ·
          refine ⟨87346470903707676513364691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232923922409887137368972509 87346470903707676513364691)
          ·
            refine ⟨131019706355561514770047037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87346470903707676513364691 131019706355561514770047037)
            ·
              refine ⟨49132389883335568038767639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131019706355561514770047037 49132389883335568038767639)
              ·
                refine ⟨73698584825003352058151459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49132389883335568038767639 73698584825003352058151459)
                ·
                  refine ⟨110547877237505028087227189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73698584825003352058151459 110547877237505028087227189)
                  ·
                    refine ⟨10363863491016096383177549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110547877237505028087227189 10363863491016096383177549)
                    ·
                      refine ⟨3886448809131036143691581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10363863491016096383177549 3886448809131036143691581)
                      ·
                        rfl

theorem cell23_7568832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_7568832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568832 prefixEnd_7568832 := by exact prefixLift 7568832
  have htrace : WordTrace (prefixWord ++ tailWord_7568832) baseStart_7568832 baseEnd_7568832 := by
    simpa [prefixWord, tailWord_7568832, baseEnd_7568832] using wordTrace_append hprefix tailTrace_7568832
  have hstable : (prefixWord ++ tailWord_7568832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568832).length < 2 ^ (prefixWord ++ tailWord_7568832).sum := by decide
  have hdescent : baseEnd_7568832 < baseStart_7568832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568959 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 3, 5]
def baseStart_7568959 : Nat := 118140960795 + 7568959 * 2 ^ 59
def prefixEnd_7568959 : Nat := 4983230072969 + 3 ^ 40 * 7568959 * 2
def baseEnd_7568959 : Nat := 1295504673724719048934499

theorem tailTrace_7568959 : CollatzResearch.WordTrace tailWord_7568959 prefixEnd_7568959 1295504673724719048934499 := by
  unfold tailWord_7568959
  simp only [CollatzResearch.WordTrace]
  refine ⟨276062614185961693127173931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184041742790641128751449287 276062614185961693127173931)
  ·
    refine ⟨414093921278942539690760897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276062614185961693127173931 414093921278942539690760897)
    ·
      refine ⟨310570440959206904768070673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414093921278942539690760897 310570440959206904768070673)
      ·
        refine ⟨232927830719405178576053005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310570440959206904768070673 232927830719405178576053005)
        ·
          refine ⟨87347936519776941966019877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232927830719405178576053005 87347936519776941966019877)
          ·
            refine ⟨16377738097458176618628727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87347936519776941966019877 16377738097458176618628727)
            ·
              refine ⟨24566607146187264927943091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16377738097458176618628727 24566607146187264927943091)
              ·
                refine ⟨36849910719280897391914637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24566607146187264927943091 36849910719280897391914637)
                ·
                  refine ⟨13818716519730336521967989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36849910719280897391914637 13818716519730336521967989)
                  ·
                    refine ⟨1295504673724719048934499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13818716519730336521967989 1295504673724719048934499)
                    ·
                      rfl

theorem cell23_7568959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_7568959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568959 prefixEnd_7568959 := by exact prefixLift 7568959
  have htrace : WordTrace (prefixWord ++ tailWord_7568959) baseStart_7568959 baseEnd_7568959 := by
    simpa [prefixWord, tailWord_7568959, baseEnd_7568959] using wordTrace_append hprefix tailTrace_7568959
  have hstable : (prefixWord ++ tailWord_7568959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568959).length < 2 ^ (prefixWord ++ tailWord_7568959).sum := by decide
  have hdescent : baseEnd_7568959 < baseStart_7568959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568976 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 1, 5]
def baseStart_7568976 : Nat := 118140960795 + 7568976 * 2 ^ 59
def prefixEnd_7568976 : Nat := 4983230072969 + 3 ^ 40 * 7568976 * 2
def baseEnd_7568976 : Nat := 1295507583448427860096973

theorem tailTrace_7568976 : CollatzResearch.WordTrace tailWord_7568976 prefixEnd_7568976 1295507583448427860096973 := by
  unfold tailWord_7568976
  simp only [CollatzResearch.WordTrace]
  refine ⟨138031617113450052515271391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184042156151266736687028521 138031617113450052515271391)
  ·
    refine ⟨207047425670175078772907087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138031617113450052515271391 207047425670175078772907087)
    ·
      refine ⟨310571138505262618159360631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207047425670175078772907087 310571138505262618159360631)
      ·
        refine ⟨465856707757893927239040947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310571138505262618159360631 465856707757893927239040947)
        ·
          refine ⟨698785061636840890858561421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465856707757893927239040947 698785061636840890858561421)
          ·
            refine ⟨262044398113815334071960533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 698785061636840890858561421 262044398113815334071960533)
            ·
              refine ⟨6141665580792546892311575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 262044398113815334071960533 6141665580792546892311575)
              ·
                refine ⟨9212498371188820338467363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141665580792546892311575 9212498371188820338467363)
                ·
                  refine ⟨13818747556783230507701045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9212498371188820338467363 13818747556783230507701045)
                  ·
                    refine ⟨1295507583448427860096973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13818747556783230507701045 1295507583448427860096973)
                    ·
                      rfl

theorem cell23_7568976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 5].length) (baseStart_7568976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568976 prefixEnd_7568976 := by exact prefixLift 7568976
  have htrace : WordTrace (prefixWord ++ tailWord_7568976) baseStart_7568976 baseEnd_7568976 := by
    simpa [prefixWord, tailWord_7568976, baseEnd_7568976] using wordTrace_append hprefix tailTrace_7568976
  have hstable : (prefixWord ++ tailWord_7568976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568976).length < 2 ^ (prefixWord ++ tailWord_7568976).sum := by decide
  have hdescent : baseEnd_7568976 < baseStart_7568976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568979 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 8, 2]
def baseStart_7568979 : Nat := 118140960795 + 7568979 * 2 ^ 59
def prefixEnd_7568979 : Nat := 4983230072969 + 3 ^ 40 * 7568979 * 2
def baseEnd_7568979 : Nat := 3886524290787247068553405

theorem tailTrace_7568979 : CollatzResearch.WordTrace tailWord_7568979 prefixEnd_7568979 3886524290787247068553405 := by
  unfold tailWord_7568979
  simp only [CollatzResearch.WordTrace]
  refine ⟨276063343645889236542901991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184042229097259491028601327 276063343645889236542901991)
  ·
    refine ⟨414095015468833854814352987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276063343645889236542901991 414095015468833854814352987)
    ·
      refine ⟨621142523203250782221529481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414095015468833854814352987 621142523203250782221529481)
      ·
        refine ⟨465856892402438086666147111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621142523203250782221529481 465856892402438086666147111)
        ·
          refine ⟨698785338603657129999220667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465856892402438086666147111 698785338603657129999220667)
          ·
            refine ⟨1048178007905485694998831001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698785338603657129999220667 1048178007905485694998831001)
            ·
              refine ⟨786133505929114271249123251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048178007905485694998831001 786133505929114271249123251)
              ·
                refine ⟨1179200258893671406873684877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786133505929114271249123251 1179200258893671406873684877)
                ·
                  refine ⟨442200097085126777577631829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179200258893671406873684877 442200097085126777577631829)
                  ·
                    refine ⟨5182032387716329424737873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 442200097085126777577631829 5182032387716329424737873)
                    ·
                      refine ⟨3886524290787247068553405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182032387716329424737873 3886524290787247068553405)
                      ·
                        rfl

theorem cell23_7568979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8, 2].length) (baseStart_7568979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568979 prefixEnd_7568979 := by exact prefixLift 7568979
  have htrace : WordTrace (prefixWord ++ tailWord_7568979) baseStart_7568979 baseEnd_7568979 := by
    simpa [prefixWord, tailWord_7568979, baseEnd_7568979] using wordTrace_append hprefix tailTrace_7568979
  have hstable : (prefixWord ++ tailWord_7568979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568979).length < 2 ^ (prefixWord ++ tailWord_7568979).sum := by decide
  have hdescent : baseEnd_7568979 < baseStart_7568979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7568999 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_7568999 : Nat := 118140960795 + 7568999 * 2 ^ 59
def prefixEnd_7568999 : Nat := 4983230072969 + 3 ^ 40 * 7568999 * 2
def baseEnd_7568999 : Nat := 3886534560400336990303313

theorem tailTrace_7568999 : CollatzResearch.WordTrace tailWord_7568999 prefixEnd_7568999 3886534560400336990303313 := by
  unfold tailWord_7568999
  simp only [CollatzResearch.WordTrace]
  refine ⟨276064073105816779958630051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184042715403877853305753367 276064073105816779958630051)
  ·
    refine ⟨414096109658725169937945077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276064073105816779958630051 414096109658725169937945077)
    ·
      refine ⟨38821510280505484681682351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 414096109658725169937945077 38821510280505484681682351)
      ·
        refine ⟨58232265420758227022523527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38821510280505484681682351 58232265420758227022523527)
        ·
          refine ⟨87348398131137340533785291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58232265420758227022523527 87348398131137340533785291)
          ·
            refine ⟨131022597196706010800677937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87348398131137340533785291 131022597196706010800677937)
            ·
              refine ⟨98266947897529508100508453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131022597196706010800677937 98266947897529508100508453)
              ·
                refine ⟨18425052730786782768845335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98266947897529508100508453 18425052730786782768845335)
                ·
                  refine ⟨27637579096180174153268003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18425052730786782768845335 27637579096180174153268003)
                  ·
                    refine ⟨41456368644270261229902005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27637579096180174153268003 41456368644270261229902005)
                    ·
                      refine ⟨3886534560400336990303313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41456368644270261229902005 3886534560400336990303313)
                      ·
                        rfl

theorem cell23_7568999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_7568999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7568999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7568999 prefixEnd_7568999 := by exact prefixLift 7568999
  have htrace : WordTrace (prefixWord ++ tailWord_7568999) baseStart_7568999 baseEnd_7568999 := by
    simpa [prefixWord, tailWord_7568999, baseEnd_7568999] using wordTrace_append hprefix tailTrace_7568999
  have hstable : (prefixWord ++ tailWord_7568999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7568999).length < 2 ^ (prefixWord ++ tailWord_7568999).sum := by decide
  have hdescent : baseEnd_7568999 < baseStart_7568999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7568999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569019 : List Nat := [1, 1, 1, 1, 1, 4, 7, 7]
def baseStart_7569019 : Nat := 118140960795 + 7569019 * 2 ^ 59
def prefixEnd_7569019 : Nat := 4983230072969 + 3 ^ 40 * 7569019 * 2
def baseEnd_7569019 : Nat := 143946104815312107853823

theorem tailTrace_7569019 : CollatzResearch.WordTrace tailWord_7569019 prefixEnd_7569019 143946104815312107853823 := by
  unfold tailWord_7569019
  simp only [CollatzResearch.WordTrace]
  refine ⟨276064802565744323374358111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184043201710496215582905407 276064802565744323374358111)
  ·
    refine ⟨414097203848616485061537167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276064802565744323374358111 414097203848616485061537167)
    ·
      refine ⟨621145805772924727592305751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414097203848616485061537167 621145805772924727592305751)
      ·
        refine ⟨931718708659387091388458627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621145805772924727592305751 931718708659387091388458627)
        ·
          refine ⟨1397578062989080637082687941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931718708659387091388458627 1397578062989080637082687941)
          ·
            refine ⟨262045886810452619453003989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1397578062989080637082687941 262045886810452619453003989)
            ·
              refine ⟨6141700472119983268429781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 262045886810452619453003989 6141700472119983268429781)
              ·
                refine ⟨143946104815312107853823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6141700472119983268429781 143946104815312107853823)
                ·
                  rfl

theorem cell23_7569019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 7].length) (baseStart_7569019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569019 prefixEnd_7569019 := by exact prefixLift 7569019
  have htrace : WordTrace (prefixWord ++ tailWord_7569019) baseStart_7569019 baseEnd_7569019 := by
    simpa [prefixWord, tailWord_7569019, baseEnd_7569019] using wordTrace_append hprefix tailTrace_7569019
  have hstable : (prefixWord ++ tailWord_7569019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569019).length < 2 ^ (prefixWord ++ tailWord_7569019).sum := by decide
  have hdescent : baseEnd_7569019 < baseStart_7569019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569033 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 1, 2, 3]
def baseStart_7569033 : Nat := 118140960795 + 7569033 * 2 ^ 59
def prefixEnd_7569033 : Nat := 4983230072969 + 3 ^ 40 * 7569033 * 2
def baseEnd_7569033 : Nat := 3886552018742589857278157

theorem tailTrace_7569033 : CollatzResearch.WordTrace tailWord_7569033 prefixEnd_7569033 3886552018742589857278157 := by
  unfold tailWord_7569033
  simp only [CollatzResearch.WordTrace]
  refine ⟨276065313187693603765367753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184043542125129069176911835 276065313187693603765367753)
  ·
    refine ⟨207048984890770202824025815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276065313187693603765367753 207048984890770202824025815)
    ·
      refine ⟨310573477336155304236038723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207048984890770202824025815 310573477336155304236038723)
      ·
        refine ⟨465860216004232956354058085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310573477336155304236038723 465860216004232956354058085)
        ·
          refine ⟨87348790500793679316385891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465860216004232956354058085 87348790500793679316385891)
          ·
            refine ⟨131023185751190518974578837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87348790500793679316385891 131023185751190518974578837)
            ·
              refine ⟨6141711832087055576933383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131023185751190518974578837 6141711832087055576933383)
              ·
                refine ⟨9212567748130583365400075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141711832087055576933383 9212567748130583365400075)
                ·
                  refine ⟨13818851622195875048100113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9212567748130583365400075 13818851622195875048100113)
                  ·
                    refine ⟨10364138716646906286075085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13818851622195875048100113 10364138716646906286075085)
                    ·
                      refine ⟨3886552018742589857278157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10364138716646906286075085 3886552018742589857278157)
                      ·
                        rfl

theorem cell23_7569033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 2, 3].length) (baseStart_7569033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569033 prefixEnd_7569033 := by exact prefixLift 7569033
  have htrace : WordTrace (prefixWord ++ tailWord_7569033) baseStart_7569033 baseEnd_7569033 := by
    simpa [prefixWord, tailWord_7569033, baseEnd_7569033] using wordTrace_append hprefix tailTrace_7569033
  have hstable : (prefixWord ++ tailWord_7569033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569033).length < 2 ^ (prefixWord ++ tailWord_7569033).sum := by decide
  have hdescent : baseEnd_7569033 < baseStart_7569033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569070 : List Nat := [4, 1, 4, 1, 2, 2, 2, 7]
def baseStart_7569070 : Nat := 118140960795 + 7569070 * 2 ^ 59
def prefixEnd_7569070 : Nat := 4983230072969 + 3 ^ 40 * 7569070 * 2
def baseEnd_7569070 : Nat := 143947074723215044907981

theorem tailTrace_7569070 : CollatzResearch.WordTrace tailWord_7569070 prefixEnd_7569070 143947074723215044907981 := by
  unfold tailWord_7569070
  simp only [CollatzResearch.WordTrace]
  refine ⟨34508332836069944885558083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184044441792373039389643109 34508332836069944885558083)
  ·
    refine ⟨51762499254104917328337125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34508332836069944885558083 51762499254104917328337125)
    ·
      refine ⟨9705468610144671999063211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51762499254104917328337125 9705468610144671999063211)
      ·
        refine ⟨14558202915217007998594817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705468610144671999063211 14558202915217007998594817)
        ·
          refine ⟨10918652186412755998946113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14558202915217007998594817 10918652186412755998946113)
          ·
            refine ⟨8188989139809566999209585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10918652186412755998946113 8188989139809566999209585)
            ·
              refine ⟨6141741854857175249407189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8188989139809566999209585 6141741854857175249407189)
              ·
                refine ⟨143947074723215044907981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6141741854857175249407189 143947074723215044907981)
                ·
                  rfl

theorem cell23_7569070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_7569070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569070 prefixEnd_7569070 := by exact prefixLift 7569070
  have htrace : WordTrace (prefixWord ++ tailWord_7569070) baseStart_7569070 baseEnd_7569070 := by
    simpa [prefixWord, tailWord_7569070, baseEnd_7569070] using wordTrace_append hprefix tailTrace_7569070
  have hstable : (prefixWord ++ tailWord_7569070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569070).length < 2 ^ (prefixWord ++ tailWord_7569070).sum := by decide
  have hdescent : baseEnd_7569070 < baseStart_7569070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569099 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4]
def baseStart_7569099 : Nat := 118140960795 + 7569099 * 2 ^ 59
def prefixEnd_7569099 : Nat := 4983230072969 + 3 ^ 40 * 7569099 * 2
def baseEnd_7569099 : Nat := 3886585908465786599052853

theorem tailTrace_7569099 : CollatzResearch.WordTrace tailWord_7569099 prefixEnd_7569099 3886585908465786599052853 := by
  unfold tailWord_7569099
  simp only [CollatzResearch.WordTrace]
  refine ⟨276067720405454497037270351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184045146936969664691513567 276067720405454497037270351)
  ·
    refine ⟨414101580608181745555905527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276067720405454497037270351 414101580608181745555905527)
    ·
      refine ⟨621152370912272618333858291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414101580608181745555905527 621152370912272618333858291)
      ·
        refine ⟨931728556368408927500787437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621152370912272618333858291 931728556368408927500787437)
        ·
          refine ⟨349398208638153347812795289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 931728556368408927500787437 349398208638153347812795289)
          ·
            refine ⟨262048656478615010859596467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349398208638153347812795289 262048656478615010859596467)
            ·
              refine ⟨393072984717922516289394701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262048656478615010859596467 393072984717922516289394701)
              ·
                refine ⟨147402369269220943608523013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393072984717922516289394701 147402369269220943608523013)
                ·
                  refine ⟨27637944237978926926598065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147402369269220943608523013 27637944237978926926598065)
                  ·
                    refine ⟨20728458178484195194948549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27637944237978926926598065 20728458178484195194948549)
                    ·
                      refine ⟨3886585908465786599052853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20728458178484195194948549 3886585908465786599052853)
                      ·
                        rfl

theorem cell23_7569099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_7569099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569099 prefixEnd_7569099 := by exact prefixLift 7569099
  have htrace : WordTrace (prefixWord ++ tailWord_7569099) baseStart_7569099 baseEnd_7569099 := by
    simpa [prefixWord, tailWord_7569099, baseEnd_7569099] using wordTrace_append hprefix tailTrace_7569099
  have hstable : (prefixWord ++ tailWord_7569099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569099).length < 2 ^ (prefixWord ++ tailWord_7569099).sum := by decide
  have hdescent : baseEnd_7569099 < baseStart_7569099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569139 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 1, 7]
def baseStart_7569139 : Nat := 118140960795 + 7569139 * 2 ^ 59
def prefixEnd_7569139 : Nat := 4983230072969 + 3 ^ 40 * 7569139 * 2
def baseEnd_7569139 : Nat := 1295535482563988814184223

theorem tailTrace_7569139 : CollatzResearch.WordTrace tailWord_7569139 prefixEnd_7569139 1295535482563988814184223 := by
  unfold tailWord_7569139
  simp only [CollatzResearch.WordTrace]
  refine ⟨276069179325309583868726471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184046119550206389245817647 276069179325309583868726471)
  ·
    refine ⟨414103768987964375803089707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276069179325309583868726471 414103768987964375803089707)
    ·
      refine ⟨621155653481946563704634561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414103768987964375803089707 621155653481946563704634561)
      ·
        refine ⟨465866740111459922778475921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621155653481946563704634561 465866740111459922778475921)
        ·
          refine ⟨349400055083594942083856941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465866740111459922778475921 349400055083594942083856941)
          ·
            refine ⟨131025020656348103281446353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349400055083594942083856941 131025020656348103281446353)
            ·
              refine ⟨98268765492261077461084765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131025020656348103281446353 98268765492261077461084765)
              ·
                refine ⟨36850787059597904047906787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98268765492261077461084765 36850787059597904047906787)
                ·
                  refine ⟨55276180589396856071860181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36850787059597904047906787 55276180589396856071860181)
                  ·
                    refine ⟨1295535482563988814184223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55276180589396856071860181 1295535482563988814184223)
                    ·
                      rfl

theorem cell23_7569139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 7].length) (baseStart_7569139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569139 prefixEnd_7569139 := by exact prefixLift 7569139
  have htrace : WordTrace (prefixWord ++ tailWord_7569139) baseStart_7569139 baseEnd_7569139 := by
    simpa [prefixWord, tailWord_7569139, baseEnd_7569139] using wordTrace_append hprefix tailTrace_7569139
  have hstable : (prefixWord ++ tailWord_7569139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569139).length < 2 ^ (prefixWord ++ tailWord_7569139).sum := by decide
  have hdescent : baseEnd_7569139 < baseStart_7569139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569140 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7569140 : Nat := 118140960795 + 7569140 * 2 ^ 59
def prefixEnd_7569140 : Nat := 4983230072969 + 3 ^ 40 * 7569140 * 2
def baseEnd_7569140 : Nat := 3886606961172620938640165

theorem tailTrace_7569140 : CollatzResearch.WordTrace tailWord_7569140 prefixEnd_7569140 3886606961172620938640165 := by
  unfold tailWord_7569140
  simp only [CollatzResearch.WordTrace]
  refine ⟨138034607899152980519756437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184046143865537307359675249 138034607899152980519756437)
  ·
    refine ⟨6470372245272795961863583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138034607899152980519756437 6470372245272795961863583)
    ·
      refine ⟨9705558367909193942795375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6470372245272795961863583 9705558367909193942795375)
      ·
        refine ⟨14558337551863790914193063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705558367909193942795375 14558337551863790914193063)
        ·
          refine ⟨21837506327795686371289595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14558337551863790914193063 21837506327795686371289595)
          ·
            refine ⟨32756259491693529556934393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21837506327795686371289595 32756259491693529556934393)
            ·
              refine ⟨24567194618770147167700795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32756259491693529556934393 24567194618770147167700795)
              ·
                refine ⟨36850791928155220751551193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24567194618770147167700795 36850791928155220751551193)
                ·
                  refine ⟨27638093946116415563663395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36850791928155220751551193 27638093946116415563663395)
                  ·
                    refine ⟨41457140919174623345495093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27638093946116415563663395 41457140919174623345495093)
                    ·
                      refine ⟨3886606961172620938640165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41457140919174623345495093 3886606961172620938640165)
                      ·
                        rfl

theorem cell23_7569140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7569140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569140 prefixEnd_7569140 := by exact prefixLift 7569140
  have htrace : WordTrace (prefixWord ++ tailWord_7569140) baseStart_7569140 baseEnd_7569140 := by
    simpa [prefixWord, tailWord_7569140, baseEnd_7569140] using wordTrace_append hprefix tailTrace_7569140
  have hstable : (prefixWord ++ tailWord_7569140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569140).length < 2 ^ (prefixWord ++ tailWord_7569140).sum := by decide
  have hdescent : baseEnd_7569140 < baseStart_7569140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569166 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7569166 : Nat := 118140960795 + 7569166 * 2 ^ 59
def prefixEnd_7569166 : Nat := 4983230072969 + 3 ^ 40 * 7569166 * 2
def baseEnd_7569166 : Nat := 3886620311669637836915045

theorem tailTrace_7569166 : CollatzResearch.WordTrace tailWord_7569166 prefixEnd_7569166 3886620311669637836915045 := by
  unfold tailWord_7569166
  simp only [CollatzResearch.WordTrace]
  refine ⟨34508770512026470934994919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184046776064141178319972901 34508770512026470934994919)
  ·
    refine ⟨51763155768039706402492379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34508770512026470934994919 51763155768039706402492379)
    ·
      refine ⟨77644733652059559603738569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51763155768039706402492379 77644733652059559603738569)
      ·
        refine ⟨58233550239044669702803927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77644733652059559603738569 58233550239044669702803927)
        ·
          refine ⟨87350325358567004554205891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58233550239044669702803927 87350325358567004554205891)
          ·
            refine ⟨131025488037850506831308837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87350325358567004554205891 131025488037850506831308837)
            ·
              refine ⟨24567279007096970030870407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131025488037850506831308837 24567279007096970030870407)
              ·
                refine ⟨36850918510645455046305611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24567279007096970030870407 36850918510645455046305611)
                ·
                  refine ⟨55276377765968182569458417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36850918510645455046305611 55276377765968182569458417)
                  ·
                    refine ⟨41457283324476136927093813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55276377765968182569458417 41457283324476136927093813)
                    ·
                      refine ⟨3886620311669637836915045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41457283324476136927093813 3886620311669637836915045)
                      ·
                        rfl

theorem cell23_7569166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7569166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569166 prefixEnd_7569166 := by exact prefixLift 7569166
  have htrace : WordTrace (prefixWord ++ tailWord_7569166) baseStart_7569166 baseEnd_7569166 := by
    simpa [prefixWord, tailWord_7569166, baseEnd_7569166] using wordTrace_append hprefix tailTrace_7569166
  have hstable : (prefixWord ++ tailWord_7569166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569166).length < 2 ^ (prefixWord ++ tailWord_7569166).sum := by decide
  have hdescent : baseEnd_7569166 < baseStart_7569166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569169 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_7569169 : Nat := 118140960795 + 7569169 * 2 ^ 59
def prefixEnd_7569169 : Nat := 4983230072969 + 3 ^ 40 * 7569169 * 2
def baseEnd_7569169 : Nat := 1295540617370533775059177

theorem tailTrace_7569169 : CollatzResearch.WordTrace tailWord_7569169 prefixEnd_7569169 1295540617370533775059177 := by
  unfold tailWord_7569169
  simp only [CollatzResearch.WordTrace]
  refine ⟨276070273515200898992318561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184046849010133932661545707 276070273515200898992318561)
  ·
    refine ⟨207052705136400674244238921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276070273515200898992318561 207052705136400674244238921)
    ·
      refine ⟨155289528852300505683179191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207052705136400674244238921 155289528852300505683179191)
      ·
        refine ⟨232934293278450758524768787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155289528852300505683179191 232934293278450758524768787)
        ·
          refine ⟨349401439917676137787153181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232934293278450758524768787 349401439917676137787153181)
          ·
            refine ⟨131025539969128551670182443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349401439917676137787153181 131025539969128551670182443)
            ·
              refine ⟨196538309953692827505273665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131025539969128551670182443 196538309953692827505273665)
              ·
                refine ⟨147403732465269620628955249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196538309953692827505273665 147403732465269620628955249)
                ·
                  refine ⟨110552799348952215471716437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147403732465269620628955249 110552799348952215471716437)
                  ·
                    refine ⟨1295540617370533775059177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110552799348952215471716437 1295540617370533775059177)
                    ·
                      rfl

theorem cell23_7569169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_7569169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569169 prefixEnd_7569169 := by exact prefixLift 7569169
  have htrace : WordTrace (prefixWord ++ tailWord_7569169) baseStart_7569169 baseEnd_7569169 := by
    simpa [prefixWord, tailWord_7569169, baseEnd_7569169] using wordTrace_append hprefix tailTrace_7569169
  have hstable : (prefixWord ++ tailWord_7569169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569169).length < 2 ^ (prefixWord ++ tailWord_7569169).sum := by decide
  have hdescent : baseEnd_7569169 < baseStart_7569169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569170 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7569170 : Nat := 118140960795 + 7569170 * 2 ^ 59
def prefixEnd_7569170 : Nat := 4983230072969 + 3 ^ 40 * 7569170 * 2
def baseEnd_7569170 : Nat := 3886622365592255821265027

theorem tailTrace_7569170 : CollatzResearch.WordTrace tailWord_7569170 prefixEnd_7569170 3886622365592255821265027 := by
  unfold tailWord_7569170
  simp only [CollatzResearch.WordTrace]
  refine ⟨69017577497049319040776241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184046873325464850775403309 69017577497049319040776241)
  ·
    refine ⟨51763183122786989280582181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69017577497049319040776241 51763183122786989280582181)
    ·
      refine ⟨9705596835522560490109159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51763183122786989280582181 9705596835522560490109159)
      ·
        refine ⟨14558395253283840735163739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705596835522560490109159 14558395253283840735163739)
        ·
          refine ⟨21837592879925761102745609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14558395253283840735163739 21837592879925761102745609)
          ·
            refine ⟨16378194659944320827059207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21837592879925761102745609 16378194659944320827059207)
            ·
              refine ⟨24567291989916481240588811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16378194659944320827059207 24567291989916481240588811)
              ·
                refine ⟨36850937984874721860883217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24567291989916481240588811 36850937984874721860883217)
                ·
                  refine ⟨27638203488656041395662413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36850937984874721860883217 27638203488656041395662413)
                  ·
                    refine ⟨10364326308246015523373405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27638203488656041395662413 10364326308246015523373405)
                    ·
                      refine ⟨3886622365592255821265027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10364326308246015523373405 3886622365592255821265027)
                      ·
                        rfl

theorem cell23_7569170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7569170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569170 prefixEnd_7569170 := by exact prefixLift 7569170
  have htrace : WordTrace (prefixWord ++ tailWord_7569170) baseStart_7569170 baseEnd_7569170 := by
    simpa [prefixWord, tailWord_7569170, baseEnd_7569170] using wordTrace_append hprefix tailTrace_7569170
  have hstable : (prefixWord ++ tailWord_7569170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569170).length < 2 ^ (prefixWord ++ tailWord_7569170).sum := by decide
  have hdescent : baseEnd_7569170 < baseStart_7569170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569176 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7569176 : Nat := 118140960795 + 7569176 * 2 ^ 59
def prefixEnd_7569176 : Nat := 4983230072969 + 3 ^ 40 * 7569176 * 2
def baseEnd_7569176 : Nat := 3886625446476182797789999

theorem tailTrace_7569176 : CollatzResearch.WordTrace tailWord_7569176 prefixEnd_7569176 3886625446476182797789999 := by
  unfold tailWord_7569176
  simp only [CollatzResearch.WordTrace]
  refine ⟨138035264413087769593911691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184047019217450359458548921 138035264413087769593911691)
  ·
    refine ⟨207052896619631654390867537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138035264413087769593911691 207052896619631654390867537)
    ·
      refine ⟨155289672464723740793150653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207052896619631654390867537 155289672464723740793150653)
      ·
        refine ⟨58233627174271402797431495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155289672464723740793150653 58233627174271402797431495)
        ·
          refine ⟨87350440761407104196147243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58233627174271402797431495 87350440761407104196147243)
          ·
            refine ⟨131025661142110656294220865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87350440761407104196147243 131025661142110656294220865)
            ·
              refine ⟨98269245856582992220665649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131025661142110656294220865 98269245856582992220665649)
              ·
                refine ⟨73701934392437244165499237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98269245856582992220665649 73701934392437244165499237)
                ·
                  refine ⟨13819112698581983281031107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73701934392437244165499237 13819112698581983281031107)
                  ·
                    refine ⟨20728669047872974921546661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13819112698581983281031107 20728669047872974921546661)
                    ·
                      refine ⟨3886625446476182797789999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20728669047872974921546661 3886625446476182797789999)
                      ·
                        rfl

theorem cell23_7569176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7569176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569176 prefixEnd_7569176 := by exact prefixLift 7569176
  have htrace : WordTrace (prefixWord ++ tailWord_7569176) baseStart_7569176 baseEnd_7569176 := by
    simpa [prefixWord, tailWord_7569176, baseEnd_7569176] using wordTrace_append hprefix tailTrace_7569176
  have hstable : (prefixWord ++ tailWord_7569176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569176).length < 2 ^ (prefixWord ++ tailWord_7569176).sum := by decide
  have hdescent : baseEnd_7569176 < baseStart_7569176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569179 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_7569179 : Nat := 118140960795 + 7569179 * 2 ^ 59
def prefixEnd_7569179 : Nat := 4983230072969 + 3 ^ 40 * 7569179 * 2
def baseEnd_7569179 : Nat := 3886626986918146286052485

theorem tailTrace_7569179 : CollatzResearch.WordTrace tailWord_7569179 prefixEnd_7569179 3886626986918146286052485 := by
  unfold tailWord_7569179
  simp only [CollatzResearch.WordTrace]
  refine ⟨276070638245164670700182591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184047092163443113800121727 276070638245164670700182591)
  ·
    refine ⟨414105957367747006050273887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276070638245164670700182591 414105957367747006050273887)
    ·
      refine ⟨621158936051620509075410831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414105957367747006050273887 621158936051620509075410831)
      ·
        refine ⟨931738404077430763613116247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621158936051620509075410831 931738404077430763613116247)
        ·
          refine ⟨1397607606116146145419674371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931738404077430763613116247 1397607606116146145419674371)
          ·
            refine ⟨2096411409174219218129511557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397607606116146145419674371 2096411409174219218129511557)
            ·
              refine ⟨393077139220166103399283417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2096411409174219218129511557 393077139220166103399283417)
              ·
                refine ⟨294807854415124577549462563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393077139220166103399283417 294807854415124577549462563)
                ·
                  refine ⟨442211781622686866324193845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294807854415124577549462563 442211781622686866324193845)
                  ·
                    refine ⟨41457354527126893717893173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 442211781622686866324193845 41457354527126893717893173)
                    ·
                      refine ⟨3886626986918146286052485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41457354527126893717893173 3886626986918146286052485)
                      ·
                        rfl

theorem cell23_7569179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_7569179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569179 prefixEnd_7569179 := by exact prefixLift 7569179
  have htrace : WordTrace (prefixWord ++ tailWord_7569179) baseStart_7569179 baseEnd_7569179 := by
    simpa [prefixWord, tailWord_7569179, baseEnd_7569179] using wordTrace_append hprefix tailTrace_7569179
  have hstable : (prefixWord ++ tailWord_7569179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569179).length < 2 ^ (prefixWord ++ tailWord_7569179).sum := by decide
  have hdescent : baseEnd_7569179 < baseStart_7569179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569199 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 10]
def baseStart_7569199 : Nat := 118140960795 + 7569199 * 2 ^ 59
def prefixEnd_7569199 : Nat := 4983230072969 + 3 ^ 40 * 7569199 * 2
def baseEnd_7569199 : Nat := 431848584059026245311377

theorem tailTrace_7569199 : CollatzResearch.WordTrace tailWord_7569199 prefixEnd_7569199 431848584059026245311377 := by
  unfold tailWord_7569199
  simp only [CollatzResearch.WordTrace]
  refine ⟨276071367705092214115910651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184047578470061476077273767 276071367705092214115910651)
  ·
    refine ⟨414107051557638321173865977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276071367705092214115910651 414107051557638321173865977)
    ·
      refine ⟨310580288668228740880399483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414107051557638321173865977 310580288668228740880399483)
      ·
        refine ⟨465870433002343111320599225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310580288668228740880399483 465870433002343111320599225)
        ·
          refine ⟨349402824751757333490449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465870433002343111320599225 349402824751757333490449419)
          ·
            refine ⟨524104237127636000235674129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349402824751757333490449419 524104237127636000235674129)
            ·
              refine ⟨393078177845727000176755597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524104237127636000235674129 393078177845727000176755597)
              ·
                refine ⟨147404316692147625066283349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393078177845727000176755597 147404316692147625066283349)
                ·
                  refine ⟨431848584059026245311377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 147404316692147625066283349 431848584059026245311377)
                  ·
                    rfl

theorem cell23_7569199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 10].length) (baseStart_7569199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569199 prefixEnd_7569199 := by exact prefixLift 7569199
  have htrace : WordTrace (prefixWord ++ tailWord_7569199) baseStart_7569199 baseEnd_7569199 := by
    simpa [prefixWord, tailWord_7569199, baseEnd_7569199] using wordTrace_append hprefix tailTrace_7569199
  have hstable : (prefixWord ++ tailWord_7569199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569199).length < 2 ^ (prefixWord ++ tailWord_7569199).sum := by decide
  have hdescent : baseEnd_7569199 < baseStart_7569199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569300 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7569300 : Nat := 118140960795 + 7569300 * 2 ^ 59
def prefixEnd_7569300 : Nat := 4983230072969 + 3 ^ 40 * 7569300 * 2
def baseEnd_7569300 : Nat := 3886689118077340312639429

theorem tailTrace_7569300 : CollatzResearch.WordTrace tailWord_7569300 prefixEnd_7569300 3886689118077340312639429 := by
  unfold tailWord_7569300
  simp only [CollatzResearch.WordTrace]
  refine ⟨138037525738863154182668677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184050034318484205576891569 138037525738863154182668677)
  ·
    refine ⟨25882036076036841409250377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138037525738863154182668677 25882036076036841409250377)
    ·
      refine ⟨19411527057027631056937783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25882036076036841409250377 19411527057027631056937783)
      ·
        refine ⟨29117290585541446585406675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19411527057027631056937783 29117290585541446585406675)
        ·
          refine ⟨43675935878312169878110013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29117290585541446585406675 43675935878312169878110013)
          ·
            refine ⟨16378475954367063704291255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43675935878312169878110013 16378475954367063704291255)
            ·
              refine ⟨24567713931550595556436883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16378475954367063704291255 24567713931550595556436883)
              ·
                refine ⟨36851570897325893334655325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24567713931550595556436883 36851570897325893334655325)
                ·
                  refine ⟨13819339086497210000495747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36851570897325893334655325 13819339086497210000495747)
                  ·
                    refine ⟨20729008629745815000743621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13819339086497210000495747 20729008629745815000743621)
                    ·
                      refine ⟨3886689118077340312639429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20729008629745815000743621 3886689118077340312639429)
                      ·
                        rfl

theorem cell23_7569300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7569300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569300 prefixEnd_7569300 := by exact prefixLift 7569300
  have htrace : WordTrace (prefixWord ++ tailWord_7569300) baseStart_7569300 baseEnd_7569300 := by
    simpa [prefixWord, tailWord_7569300, baseEnd_7569300] using wordTrace_append hprefix tailTrace_7569300
  have hstable : (prefixWord ++ tailWord_7569300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569300).length < 2 ^ (prefixWord ++ tailWord_7569300).sum := by decide
  have hdescent : baseEnd_7569300 < baseStart_7569300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569304 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7569304 : Nat := 118140960795 + 7569304 * 2 ^ 59
def prefixEnd_7569304 : Nat := 4983230072969 + 3 ^ 40 * 7569304 * 2
def baseEnd_7569304 : Nat := 3886691171999958296989411

theorem tailTrace_7569304 : CollatzResearch.WordTrace tailWord_7569304 prefixEnd_7569304 3886691171999958296989411 := by
  unfold tailWord_7569304
  simp only [CollatzResearch.WordTrace]
  refine ⟨138037598684855908524241483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184050131579807878032321977 138037598684855908524241483)
  ·
    refine ⟨207056398027283862786362225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138037598684855908524241483 207056398027283862786362225)
    ·
      refine ⟨155292298520462897089771669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207056398027283862786362225 155292298520462897089771669)
      ·
        refine ⟨7279326493146698301083047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155292298520462897089771669 7279326493146698301083047)
        ·
          refine ⟨10918989739720047451624571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7279326493146698301083047 10918989739720047451624571)
          ·
            refine ⟨16378484609580071177436857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10918989739720047451624571 16378484609580071177436857)
            ·
              refine ⟨12283863457185053383077643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16378484609580071177436857 12283863457185053383077643)
              ·
                refine ⟨18425795185777580074616465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12283863457185053383077643 18425795185777580074616465)
                ·
                  refine ⟨13819346389333185055962349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18425795185777580074616465 13819346389333185055962349)
                  ·
                    refine ⟨5182254895999944395985881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13819346389333185055962349 5182254895999944395985881)
                    ·
                      refine ⟨3886691171999958296989411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182254895999944395985881 3886691171999958296989411)
                      ·
                        rfl

theorem cell23_7569304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7569304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569304 prefixEnd_7569304 := by exact prefixLift 7569304
  have htrace : WordTrace (prefixWord ++ tailWord_7569304) baseStart_7569304 baseEnd_7569304 := by
    simpa [prefixWord, tailWord_7569304, baseEnd_7569304] using wordTrace_append hprefix tailTrace_7569304
  have hstable : (prefixWord ++ tailWord_7569304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569304).length < 2 ^ (prefixWord ++ tailWord_7569304).sum := by decide
  have hdescent : baseEnd_7569304 < baseStart_7569304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569336 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_7569336 : Nat := 118140960795 + 7569336 * 2 ^ 59
def prefixEnd_7569336 : Nat := 4983230072969 + 3 ^ 40 * 7569336 * 2
def baseEnd_7569336 : Nat := 1295569201126967390596421

theorem tailTrace_7569336 : CollatzResearch.WordTrace tailWord_7569336 prefixEnd_7569336 1295569201126967390596421 := by
  unfold tailWord_7569336
  simp only [CollatzResearch.WordTrace]
  refine ⟨138038182252797943256823931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184050909670397257675765241 138038182252797943256823931)
  ·
    refine ⟨207057273379196914885235897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138038182252797943256823931 207057273379196914885235897)
    ·
      refine ⟨155292955034397686163926923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207057273379196914885235897 155292955034397686163926923)
      ·
        refine ⟨232939432551596529245890385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155292955034397686163926923 232939432551596529245890385)
        ·
          refine ⟨174704574413697396934417789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232939432551596529245890385 174704574413697396934417789)
          ·
            refine ⟨65514215405136523850406671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174704574413697396934417789 65514215405136523850406671)
            ·
              refine ⟨98271323107704785775610007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65514215405136523850406671 98271323107704785775610007)
              ·
                refine ⟨147406984661557178663415011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98271323107704785775610007 147406984661557178663415011)
                ·
                  refine ⟨221110476992335767995122517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147406984661557178663415011 221110476992335767995122517)
                  ·
                    refine ⟨1295569201126967390596421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221110476992335767995122517 1295569201126967390596421)
                    ·
                      rfl

theorem cell23_7569336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_7569336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569336 prefixEnd_7569336 := by exact prefixLift 7569336
  have htrace : WordTrace (prefixWord ++ tailWord_7569336) baseStart_7569336 baseEnd_7569336 := by
    simpa [prefixWord, tailWord_7569336, baseEnd_7569336] using wordTrace_append hprefix tailTrace_7569336
  have hstable : (prefixWord ++ tailWord_7569336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569336).length < 2 ^ (prefixWord ++ tailWord_7569336).sum := by decide
  have hdescent : baseEnd_7569336 < baseStart_7569336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569360 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 3, 3, 2]
def baseStart_7569360 : Nat := 118140960795 + 7569360 * 2 ^ 59
def prefixEnd_7569360 : Nat := 4983230072969 + 3 ^ 40 * 7569360 * 2
def baseEnd_7569360 : Nat := 3886719926916610077889153

theorem tailTrace_7569360 : CollatzResearch.WordTrace tailWord_7569360 prefixEnd_7569360 3886719926916610077889153 := by
  unfold tailWord_7569360
  simp only [CollatzResearch.WordTrace]
  refine ⟨138038619928754469306260767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184051493238339292408347689 138038619928754469306260767)
  ·
    refine ⟨207057929893131703959391151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138038619928754469306260767 207057929893131703959391151)
    ·
      refine ⟨310586894839697555939086727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207057929893131703959391151 310586894839697555939086727)
      ·
        refine ⟨465880342259546333908630091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310586894839697555939086727 465880342259546333908630091)
        ·
          refine ⟨698820513389319500862945137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465880342259546333908630091 698820513389319500862945137)
          ·
            refine ⟨524115385041989625647208853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698820513389319500862945137 524115385041989625647208853)
            ·
              refine ⟨24567908673843263702212915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 524115385041989625647208853 24567908673843263702212915)
              ·
                refine ⟨36851863010764895553319373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24567908673843263702212915 36851863010764895553319373)
                ·
                  refine ⟨13819448629036835832494765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36851863010764895553319373 13819448629036835832494765)
                  ·
                    refine ⟨5182293235888813437185537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13819448629036835832494765 5182293235888813437185537)
                    ·
                      refine ⟨3886719926916610077889153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182293235888813437185537 3886719926916610077889153)
                      ·
                        rfl

theorem cell23_7569360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 3, 2].length) (baseStart_7569360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569360 prefixEnd_7569360 := by exact prefixLift 7569360
  have htrace : WordTrace (prefixWord ++ tailWord_7569360) baseStart_7569360 baseEnd_7569360 := by
    simpa [prefixWord, tailWord_7569360, baseEnd_7569360] using wordTrace_append hprefix tailTrace_7569360
  have hstable : (prefixWord ++ tailWord_7569360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569360).length < 2 ^ (prefixWord ++ tailWord_7569360).sum := by decide
  have hdescent : baseEnd_7569360 < baseStart_7569360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569403 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4]
def baseStart_7569403 : Nat := 118140960795 + 7569403 * 2 ^ 59
def prefixEnd_7569403 : Nat := 4983230072969 + 3 ^ 40 * 7569403 * 2
def baseEnd_7569403 : Nat := 3886742006584753409651455

theorem tailTrace_7569403 : CollatzResearch.WordTrace tailWord_7569403 prefixEnd_7569403 3886742006584753409651455 := by
  unfold tailWord_7569403
  simp only [CollatzResearch.WordTrace]
  refine ⟨276078808196353156956336863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184052538797568771304224575 276078808196353156956336863)
  ·
    refine ⟨414118212294529735434505295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276078808196353156956336863 414118212294529735434505295)
    ·
      refine ⟨621177318441794603151757943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414118212294529735434505295 621177318441794603151757943)
      ·
        refine ⟨931765977662691904727636915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621177318441794603151757943 931765977662691904727636915)
        ·
          refine ⟨1397648966494037857091455373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931765977662691904727636915 1397648966494037857091455373)
          ·
            refine ⟨524118362435264196409295765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1397648966494037857091455373 524118362435264196409295765)
            ·
              refine ⟨24568048239153009206685739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 524118362435264196409295765 24568048239153009206685739)
              ·
                refine ⟨36852072358729513810028609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24568048239153009206685739 36852072358729513810028609)
                ·
                  refine ⟨27639054269047135357521457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36852072358729513810028609 27639054269047135357521457)
                  ·
                    refine ⟨20729290701785351518141093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27639054269047135357521457 20729290701785351518141093)
                    ·
                      refine ⟨3886742006584753409651455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20729290701785351518141093 3886742006584753409651455)
                      ·
                        rfl

theorem cell23_7569403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_7569403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569403 prefixEnd_7569403 := by exact prefixLift 7569403
  have htrace : WordTrace (prefixWord ++ tailWord_7569403) baseStart_7569403 baseEnd_7569403 := by
    simpa [prefixWord, tailWord_7569403, baseEnd_7569403] using wordTrace_append hprefix tailTrace_7569403
  have hstable : (prefixWord ++ tailWord_7569403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569403).length < 2 ^ (prefixWord ++ tailWord_7569403).sum := by decide
  have hdescent : baseEnd_7569403 < baseStart_7569403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569407 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 2, 2, 2]
def baseStart_7569407 : Nat := 118140960795 + 7569407 * 2 ^ 59
def prefixEnd_7569407 : Nat := 4983230072969 + 3 ^ 40 * 7569407 * 2
def baseEnd_7569407 : Nat := 3886744060507371394001437

theorem tailTrace_7569407 : CollatzResearch.WordTrace tailWord_7569407 prefixEnd_7569407 3886744060507371394001437 := by
  unfold tailWord_7569407
  simp only [CollatzResearch.WordTrace]
  refine ⟨276078954088338665639482475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184052636058892443759654983 276078954088338665639482475)
  ·
    refine ⟨414118431132507998459223713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276078954088338665639482475 414118431132507998459223713)
    ·
      refine ⟨310588823349380998844417785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414118431132507998459223713 310588823349380998844417785)
      ·
        refine ⟨232941617512035749133313339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310588823349380998844417785 232941617512035749133313339)
        ·
          refine ⟨349412426268053623699970009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232941617512035749133313339 349412426268053623699970009)
          ·
            refine ⟨262059319701040217774977507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349412426268053623699970009 262059319701040217774977507)
            ·
              refine ⟨393088979551560326662466261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262059319701040217774977507 393088979551560326662466261)
              ·
                refine ⟨9213022958239695156151553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 393088979551560326662466261 9213022958239695156151553)
                ·
                  refine ⟨6909767218679771367113665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9213022958239695156151553 6909767218679771367113665)
                  ·
                    refine ⟨5182325414009828525335249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6909767218679771367113665 5182325414009828525335249)
                    ·
                      refine ⟨3886744060507371394001437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182325414009828525335249 3886744060507371394001437)
                      ·
                        rfl

theorem cell23_7569407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_7569407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569407 prefixEnd_7569407 := by exact prefixLift 7569407
  have htrace : WordTrace (prefixWord ++ tailWord_7569407) baseStart_7569407 baseEnd_7569407 := by
    simpa [prefixWord, tailWord_7569407, baseEnd_7569407] using wordTrace_append hprefix tailTrace_7569407
  have hstable : (prefixWord ++ tailWord_7569407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569407).length < 2 ^ (prefixWord ++ tailWord_7569407).sum := by decide
  have hdescent : baseEnd_7569407 < baseStart_7569407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569413 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 7]
def baseStart_7569413 : Nat := 118140960795 + 7569413 * 2 ^ 59
def prefixEnd_7569413 : Nat := 4983230072969 + 3 ^ 40 * 7569413 * 2
def baseEnd_7569413 : Nat := 431860793487922041169601

theorem tailTrace_7569413 : CollatzResearch.WordTrace tailWord_7569413 prefixEnd_7569413 431860793487922041169601 := by
  unfold tailWord_7569413
  simp only [CollatzResearch.WordTrace]
  refine ⟨276079172926316928664200893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184052781950877952442800595 276079172926316928664200893)
  ·
    refine ⟨103529689847368848249075335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276079172926316928664200893 103529689847368848249075335)
    ·
      refine ⟨155294534771053272373613003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103529689847368848249075335 155294534771053272373613003)
      ·
        refine ⟨232941802156579908560419505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155294534771053272373613003 232941802156579908560419505)
        ·
          refine ⟨174706351617434931420314629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232941802156579908560419505 174706351617434931420314629)
          ·
            refine ⟨32757440928269049641308993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174706351617434931420314629 32757440928269049641308993)
            ·
              refine ⟨24568080696201787230981745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32757440928269049641308993 24568080696201787230981745)
              ·
                refine ⟨18426060522151340423236309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24568080696201787230981745 18426060522151340423236309)
                ·
                  refine ⟨431860793487922041169601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18426060522151340423236309 431860793487922041169601)
                  ·
                    rfl

theorem cell23_7569413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_7569413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569413 prefixEnd_7569413 := by exact prefixLift 7569413
  have htrace : WordTrace (prefixWord ++ tailWord_7569413) baseStart_7569413 baseEnd_7569413 := by
    simpa [prefixWord, tailWord_7569413, baseEnd_7569413] using wordTrace_append hprefix tailTrace_7569413
  have hstable : (prefixWord ++ tailWord_7569413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569413).length < 2 ^ (prefixWord ++ tailWord_7569413).sum := by decide
  have hdescent : baseEnd_7569413 < baseStart_7569413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569463 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_7569463 : Nat := 118140960795 + 7569463 * 2 ^ 59
def prefixEnd_7569463 : Nat := 4983230072969 + 3 ^ 40 * 7569463 * 2
def baseEnd_7569463 : Nat := 3886772815424023174901179

theorem tailTrace_7569463 : CollatzResearch.WordTrace tailWord_7569463 prefixEnd_7569463 3886772815424023174901179 := by
  unfold tailWord_7569463
  simp only [CollatzResearch.WordTrace]
  refine ⟨276080996576135787203521043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184053997717423858135680695 276080996576135787203521043)
  ·
    refine ⟨414121494864203680805281565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276080996576135787203521043 414121494864203680805281565)
    ·
      refine ⟨155295560574076380301980587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414121494864203680805281565 155295560574076380301980587)
      ·
        refine ⟨232943340861114570452970881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155295560574076380301980587 232943340861114570452970881)
        ·
          refine ⟨174707505645835927839728161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232943340861114570452970881 174707505645835927839728161)
          ·
            refine ⟨131030629234376945879796121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174707505645835927839728161 131030629234376945879796121)
            ·
              refine ⟨98272971925782709409847091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131030629234376945879796121 98272971925782709409847091)
              ·
                refine ⟨147409457888674064114770637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98272971925782709409847091 147409457888674064114770637)
                ·
                  refine ⟨55278546708252774043038989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147409457888674064114770637 55278546708252774043038989)
                  ·
                    refine ⟨20729455015594790266139621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55278546708252774043038989 20729455015594790266139621)
                    ·
                      refine ⟨3886772815424023174901179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20729455015594790266139621 3886772815424023174901179)
                      ·
                        rfl

theorem cell23_7569463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_7569463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569463 prefixEnd_7569463 := by exact prefixLift 7569463
  have htrace : WordTrace (prefixWord ++ tailWord_7569463) baseStart_7569463 baseEnd_7569463 := by
    simpa [prefixWord, tailWord_7569463, baseEnd_7569463] using wordTrace_append hprefix tailTrace_7569463
  have hstable : (prefixWord ++ tailWord_7569463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569463).length < 2 ^ (prefixWord ++ tailWord_7569463).sum := by decide
  have hdescent : baseEnd_7569463 < baseStart_7569463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569480 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_7569480 : Nat := 118140960795 + 7569480 * 2 ^ 59
def prefixEnd_7569480 : Nat := 4983230072969 + 3 ^ 40 * 7569480 * 2
def baseEnd_7569480 : Nat := 3886781544595149608388601

theorem tailTrace_7569480 : CollatzResearch.WordTrace tailWord_7569480 prefixEnd_7569480 3886781544595149608388601 := by
  unfold tailWord_7569480
  simp only [CollatzResearch.WordTrace]
  refine ⟨138040808308537099553444947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184054411078049466071259929 138040808308537099553444947)
  ·
    refine ⟨207061212462805649330167421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138040808308537099553444947 207061212462805649330167421)
    ·
      refine ⟨77647954673552118498812783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207061212462805649330167421 77647954673552118498812783)
      ·
        refine ⟨116471932010328177748219175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77647954673552118498812783 116471932010328177748219175)
        ·
          refine ⟨174707898015492266622328763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116471932010328177748219175 174707898015492266622328763)
          ·
            refine ⟨262061847023238399933493145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174707898015492266622328763 262061847023238399933493145)
            ·
              refine ⟨196546385267428799950119859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262061847023238399933493145 196546385267428799950119859)
              ·
                refine ⟨294819577901143199925179789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196546385267428799950119859 294819577901143199925179789)
                ·
                  refine ⟨110557341712928699971942421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294819577901143199925179789 110557341712928699971942421)
                  ·
                    refine ⟨5182375392793532811184801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110557341712928699971942421 5182375392793532811184801)
                    ·
                      refine ⟨3886781544595149608388601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182375392793532811184801 3886781544595149608388601)
                      ·
                        rfl

theorem cell23_7569480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_7569480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569480 prefixEnd_7569480 := by exact prefixLift 7569480
  have htrace : WordTrace (prefixWord ++ tailWord_7569480) baseStart_7569480 baseEnd_7569480 := by
    simpa [prefixWord, tailWord_7569480, baseEnd_7569480] using wordTrace_append hprefix tailTrace_7569480
  have hstable : (prefixWord ++ tailWord_7569480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569480).length < 2 ^ (prefixWord ++ tailWord_7569480).sum := by decide
  have hdescent : baseEnd_7569480 < baseStart_7569480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569494 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7569494 : Nat := 118140960795 + 7569494 * 2 ^ 59
def prefixEnd_7569494 : Nat := 4983230072969 + 3 ^ 40 * 7569494 * 2
def baseEnd_7569494 : Nat := 1295596244441437517871179

theorem tailTrace_7569494 : CollatzResearch.WordTrace tailWord_7569494 prefixEnd_7569494 1295596244441437517871179 := by
  unfold tailWord_7569494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255132952438967468618721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184054751492682319665266357 17255132952438967468618721)
  ·
    refine ⟨12941349714329225601464041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17255132952438967468618721 12941349714329225601464041)
    ·
      refine ⟨9706012285746919201098031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12941349714329225601464041 9706012285746919201098031)
      ·
        refine ⟨14559018428620378801647047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9706012285746919201098031 14559018428620378801647047)
        ·
          refine ⟨21838527642930568202470571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14559018428620378801647047 21838527642930568202470571)
          ·
            refine ⟨32757791464395852303705857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21838527642930568202470571 32757791464395852303705857)
            ·
              refine ⟨24568343598296889227779393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32757791464395852303705857 24568343598296889227779393)
              ·
                refine ⟨18426257698722666920834545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24568343598296889227779393 18426257698722666920834545)
                ·
                  refine ⟨13819693274042000190625909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18426257698722666920834545 13819693274042000190625909)
                  ·
                    refine ⟨1295596244441437517871179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13819693274042000190625909 1295596244441437517871179)
                    ·
                      rfl

theorem cell23_7569494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7569494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569494 prefixEnd_7569494 := by exact prefixLift 7569494
  have htrace : WordTrace (prefixWord ++ tailWord_7569494) baseStart_7569494 baseEnd_7569494 := by
    simpa [prefixWord, tailWord_7569494, baseEnd_7569494] using wordTrace_append hprefix tailTrace_7569494
  have hstable : (prefixWord ++ tailWord_7569494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569494).length < 2 ^ (prefixWord ++ tailWord_7569494).sum := by decide
  have hdescent : baseEnd_7569494 < baseStart_7569494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569514 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_7569514 : Nat := 118140960795 + 7569514 * 2 ^ 59
def prefixEnd_7569514 : Nat := 4983230072969 + 3 ^ 40 * 7569514 * 2
def baseEnd_7569514 : Nat := 3886799002937402475363445

theorem tailTrace_7569514 : CollatzResearch.WordTrace tailWord_7569514 prefixEnd_7569514 3886799002937402475363445 := by
  unfold tailWord_7569514
  simp only [CollatzResearch.WordTrace]
  refine ⟨69020714174737755728406899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184055237799300681942418397 69020714174737755728406899)
  ·
    refine ⟨103531071262106633592610349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69020714174737755728406899 103531071262106633592610349)
    ·
      refine ⟨38824151723289987597228881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103531071262106633592610349 38824151723289987597228881)
      ·
        refine ⟨29118113792467490697921661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38824151723289987597228881 29118113792467490697921661)
        ·
          refine ⟨10919292672175309011720623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29118113792467490697921661 10919292672175309011720623)
          ·
            refine ⟨16378939008262963517580935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919292672175309011720623 16378939008262963517580935)
            ·
              refine ⟨24568408512394445276371403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16378939008262963517580935 24568408512394445276371403)
              ·
                refine ⟨36852612768591667914557105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24568408512394445276371403 36852612768591667914557105)
                ·
                  refine ⟨27639459576443750935917829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36852612768591667914557105 27639459576443750935917829)
                  ·
                    refine ⟨5182398670583203300484593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27639459576443750935917829 5182398670583203300484593)
                    ·
                      refine ⟨3886799002937402475363445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182398670583203300484593 3886799002937402475363445)
                      ·
                        rfl

theorem cell23_7569514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_7569514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569514 prefixEnd_7569514 := by exact prefixLift 7569514
  have htrace : WordTrace (prefixWord ++ tailWord_7569514) baseStart_7569514 baseEnd_7569514 := by
    simpa [prefixWord, tailWord_7569514, baseEnd_7569514] using wordTrace_append hprefix tailTrace_7569514
  have hstable : (prefixWord ++ tailWord_7569514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569514).length < 2 ^ (prefixWord ++ tailWord_7569514).sum := by decide
  have hdescent : baseEnd_7569514 < baseStart_7569514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569520 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 6]
def baseStart_7569520 : Nat := 118140960795 + 7569520 * 2 ^ 59
def prefixEnd_7569520 : Nat := 4983230072969 + 3 ^ 40 * 7569520 * 2
def baseEnd_7569520 : Nat := 431866898202369939098713

theorem tailTrace_7569520 : CollatzResearch.WordTrace tailWord_7569520 prefixEnd_7569520 431866898202369939098713 := by
  unfold tailWord_7569520
  simp only [CollatzResearch.WordTrace]
  refine ⟨138041537768464642969173007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184055383691286190625564009 138041537768464642969173007)
  ·
    refine ⟨207062306652696964453759511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138041537768464642969173007 207062306652696964453759511)
    ·
      refine ⟨310593459979045446680639267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207062306652696964453759511 310593459979045446680639267)
      ·
        refine ⟨465890189968568170020958901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310593459979045446680639267 465890189968568170020958901)
        ·
          refine ⟨43677205309553265939464897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 465890189968568170020958901 43677205309553265939464897)
          ·
            refine ⟨32757903982164949454598673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43677205309553265939464897 32757903982164949454598673)
            ·
              refine ⟨24568427986623712090949005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32757903982164949454598673 24568427986623712090949005)
              ·
                refine ⟨9213160494983892034105877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24568427986623712090949005 9213160494983892034105877)
                ·
                  refine ⟨431866898202369939098713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9213160494983892034105877 431866898202369939098713)
                  ·
                    rfl

theorem cell23_7569520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_7569520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569520 prefixEnd_7569520 := by exact prefixLift 7569520
  have htrace : WordTrace (prefixWord ++ tailWord_7569520) baseStart_7569520 baseEnd_7569520 := by
    simpa [prefixWord, tailWord_7569520, baseEnd_7569520] using wordTrace_append hprefix tailTrace_7569520
  have hstable : (prefixWord ++ tailWord_7569520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569520).length < 2 ^ (prefixWord ++ tailWord_7569520).sum := by decide
  have hdescent : baseEnd_7569520 < baseStart_7569520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569557 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_7569557 : Nat := 118140960795 + 7569557 * 2 ^ 59
def prefixEnd_7569557 : Nat := 4983230072969 + 3 ^ 40 * 7569557 * 2
def baseEnd_7569557 : Nat := 3886821082605545807125747

theorem tailTrace_7569557 : CollatzResearch.WordTrace tailWord_7569557 prefixEnd_7569557 3886821082605545807125747 := by
  unfold tailWord_7569557
  simp only [CollatzResearch.WordTrace]
  refine ⟨276084425037795241257442925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184056283358530160838295283 276084425037795241257442925)
  ·
    refine ⟨103531659389173215471541097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276084425037795241257442925 103531659389173215471541097)
    ·
      refine ⟨77648744541879911603655823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103531659389173215471541097 77648744541879911603655823)
      ·
        refine ⟨116473116812819867405483735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77648744541879911603655823 116473116812819867405483735)
        ·
          refine ⟨174709675219229801108225603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116473116812819867405483735 174709675219229801108225603)
          ·
            refine ⟨262064512828844701662338405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174709675219229801108225603 262064512828844701662338405)
            ·
              refine ⟨49137096155408381561688451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262064512828844701662338405 49137096155408381561688451)
              ·
                refine ⟨73705644233112572342532677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49137096155408381561688451 73705644233112572342532677)
                ·
                  refine ⟨13819808293708607314224877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73705644233112572342532677 13819808293708607314224877)
                  ·
                    refine ⟨5182428110140727742834329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13819808293708607314224877 5182428110140727742834329)
                    ·
                      refine ⟨3886821082605545807125747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182428110140727742834329 3886821082605545807125747)
                      ·
                        rfl

theorem cell23_7569557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_7569557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569557 prefixEnd_7569557 := by exact prefixLift 7569557
  have htrace : WordTrace (prefixWord ++ tailWord_7569557) baseStart_7569557 baseEnd_7569557 := by
    simpa [prefixWord, tailWord_7569557, baseEnd_7569557] using wordTrace_append hprefix tailTrace_7569557
  have hstable : (prefixWord ++ tailWord_7569557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569557).length < 2 ^ (prefixWord ++ tailWord_7569557).sum := by decide
  have hdescent : baseEnd_7569557 < baseStart_7569557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569564 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_7569564 : Nat := 118140960795 + 7569564 * 2 ^ 59
def prefixEnd_7569564 : Nat := 4983230072969 + 3 ^ 40 * 7569564 * 2
def baseEnd_7569564 : Nat := 3886824676970127279738215

theorem tailTrace_7569564 : CollatzResearch.WordTrace tailWord_7569564 prefixEnd_7569564 3886824676970127279738215 := by
  unfold tailWord_7569564
  simp only [CollatzResearch.WordTrace]
  refine ⟨138042340174384940726473873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184056453565846587635298497 138042340174384940726473873)
  ·
    refine ⟨103531755130788705544855405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138042340174384940726473873 103531755130788705544855405)
    ·
      refine ⟨38824408174045764579320777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103531755130788705544855405 38824408174045764579320777)
      ·
        refine ⟨29118306130534323434490583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38824408174045764579320777 29118306130534323434490583)
        ·
          refine ⟨43677459195801485151735875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29118306130534323434490583 43677459195801485151735875)
          ·
            refine ⟨65516188793702227727603813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43677459195801485151735875 65516188793702227727603813)
            ·
              refine ⟨12284285398819167698925715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65516188793702227727603813 12284285398819167698925715)
              ·
                refine ⟨18426428098228751548388573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12284285398819167698925715 18426428098228751548388573)
                ·
                  refine ⟨6909910536835781830645715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18426428098228751548388573 6909910536835781830645715)
                  ·
                    refine ⟨10364865805253672745968573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909910536835781830645715 10364865805253672745968573)
                    ·
                      refine ⟨3886824676970127279738215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10364865805253672745968573 3886824676970127279738215)
                      ·
                        rfl

theorem cell23_7569564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_7569564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569564 prefixEnd_7569564 := by exact prefixLift 7569564
  have htrace : WordTrace (prefixWord ++ tailWord_7569564) baseStart_7569564 baseEnd_7569564 := by
    simpa [prefixWord, tailWord_7569564, baseEnd_7569564] using wordTrace_append hprefix tailTrace_7569564
  have hstable : (prefixWord ++ tailWord_7569564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569564).length < 2 ^ (prefixWord ++ tailWord_7569564).sum := by decide
  have hdescent : baseEnd_7569564 < baseStart_7569564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569604 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_7569604 : Nat := 118140960795 + 7569604 * 2 ^ 59
def prefixEnd_7569604 : Nat := 4983230072969 + 3 ^ 40 * 7569604 * 2
def baseEnd_7569604 : Nat := 3886845216196307123238031

theorem tailTrace_7569604 : CollatzResearch.WordTrace tailWord_7569604 prefixEnd_7569604 3886845216196307123238031 := by
  unfold tailWord_7569604
  simp only [CollatzResearch.WordTrace]
  refine ⟨138043069634312484142201933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184057426179083312189602577 138043069634312484142201933)
  ·
    refine ⟨51766151112867181553325725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138043069634312484142201933 51766151112867181553325725)
    ·
      refine ⟨19412306667325193082497147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51766151112867181553325725 19412306667325193082497147)
      ·
        refine ⟨29118460000987789623745721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19412306667325193082497147 29118460000987789623745721)
        ·
          refine ⟨21838845000740842217809291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29118460000987789623745721 21838845000740842217809291)
          ·
            refine ⟨32758267501111263326713937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21838845000740842217809291 32758267501111263326713937)
            ·
              refine ⟨24568700625833447495035453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32758267501111263326713937 24568700625833447495035453)
              ·
                refine ⟨9213262734687542810638295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24568700625833447495035453 9213262734687542810638295)
                ·
                  refine ⟨13819894102031314215957443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9213262734687542810638295 13819894102031314215957443)
                  ·
                    refine ⟨20729841153046971323936165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13819894102031314215957443 20729841153046971323936165)
                    ·
                      refine ⟨3886845216196307123238031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20729841153046971323936165 3886845216196307123238031)
                      ·
                        rfl

theorem cell23_7569604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_7569604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569604 prefixEnd_7569604 := by exact prefixLift 7569604
  have htrace : WordTrace (prefixWord ++ tailWord_7569604) baseStart_7569604 baseEnd_7569604 := by
    simpa [prefixWord, tailWord_7569604, baseEnd_7569604] using wordTrace_append hprefix tailTrace_7569604
  have hstable : (prefixWord ++ tailWord_7569604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569604).length < 2 ^ (prefixWord ++ tailWord_7569604).sum := by decide
  have hdescent : baseEnd_7569604 < baseStart_7569604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569654 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7569654 : Nat := 118140960795 + 7569654 * 2 ^ 59
def prefixEnd_7569654 : Nat := 4983230072969 + 3 ^ 40 * 7569654 * 2
def baseEnd_7569654 : Nat := 3886870890229031927612801

theorem tailTrace_7569654 : CollatzResearch.WordTrace tailWord_7569654 prefixEnd_7569654 3886870890229031927612801 := by
  unfold tailWord_7569654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255497682402739176482751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184058641945629217882482677 17255497682402739176482751)
  ·
    refine ⟨25883246523604108764724127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17255497682402739176482751 25883246523604108764724127)
    ·
      refine ⟨38824869785406163147086191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25883246523604108764724127 38824869785406163147086191)
      ·
        refine ⟨58237304678109244720629287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38824869785406163147086191 58237304678109244720629287)
        ·
          refine ⟨87355957017163867080943931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58237304678109244720629287 87355957017163867080943931)
          ·
            refine ⟨131033935525745800621415897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87355957017163867080943931 131033935525745800621415897)
            ·
              refine ⟨98275451644309350466061923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131033935525745800621415897 98275451644309350466061923)
              ·
                refine ⟨147413177466464025699092885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98275451644309350466061923 147413177466464025699092885)
                ·
                  refine ⟨6909992693740501204644979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147413177466464025699092885 6909992693740501204644979)
                  ·
                    refine ⟨10364989040610751806967469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909992693740501204644979 10364989040610751806967469)
                    ·
                      refine ⟨3886870890229031927612801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10364989040610751806967469 3886870890229031927612801)
                      ·
                        rfl

theorem cell23_7569654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7569654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569654 prefixEnd_7569654 := by exact prefixLift 7569654
  have htrace : WordTrace (prefixWord ++ tailWord_7569654) baseStart_7569654 baseEnd_7569654 := by
    simpa [prefixWord, tailWord_7569654, baseEnd_7569654] using wordTrace_append hprefix tailTrace_7569654
  have hstable : (prefixWord ++ tailWord_7569654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569654).length < 2 ^ (prefixWord ++ tailWord_7569654).sum := by decide
  have hdescent : baseEnd_7569654 < baseStart_7569654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569664 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 1, 3, 2]
def baseStart_7569664 : Nat := 118140960795 + 7569664 * 2 ^ 59
def prefixEnd_7569664 : Nat := 4983230072969 + 3 ^ 40 * 7569664 * 2
def baseEnd_7569664 : Nat := 3886876025035576888487755

theorem tailTrace_7569664 : CollatzResearch.WordTrace tailWord_7569664 prefixEnd_7569664 3886876025035576888487755 := by
  unfold tailWord_7569664
  simp only [CollatzResearch.WordTrace]
  refine ⟨138044163824203799265794023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184058885098938399021058697 138044163824203799265794023)
  ·
    refine ⟨207066245736305698898691035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138044163824203799265794023 207066245736305698898691035)
    ·
      refine ⟨310599368604458548348036553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207066245736305698898691035 310599368604458548348036553)
      ·
        refine ⟨232949526453343911261027415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310599368604458548348036553 232949526453343911261027415)
        ·
          refine ⟨349424289680015866891541123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232949526453343911261027415 349424289680015866891541123)
          ·
            refine ⟨524136434520023800337311685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349424289680015866891541123 524136434520023800337311685)
            ·
              refine ⟨98275581472504462563245941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 524136434520023800337311685 98275581472504462563245941)
              ·
                refine ⟨9213335763047293365304307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98275581472504462563245941 9213335763047293365304307)
                ·
                  refine ⟨13820003644570940047956461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9213335763047293365304307 13820003644570940047956461)
                  ·
                    refine ⟨5182501366714102517983673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13820003644570940047956461 5182501366714102517983673)
                    ·
                      refine ⟨3886876025035576888487755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182501366714102517983673 3886876025035576888487755)
                      ·
                        rfl

theorem cell23_7569664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_7569664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569664 prefixEnd_7569664 := by exact prefixLift 7569664
  have htrace : WordTrace (prefixWord ++ tailWord_7569664) baseStart_7569664 baseEnd_7569664 := by
    simpa [prefixWord, tailWord_7569664, baseEnd_7569664] using wordTrace_append hprefix tailTrace_7569664
  have hstable : (prefixWord ++ tailWord_7569664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569664).length < 2 ^ (prefixWord ++ tailWord_7569664).sum := by decide
  have hdescent : baseEnd_7569664 < baseStart_7569664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569687 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 2, 6]
def baseStart_7569687 : Nat := 118140960795 + 7569687 * 2 ^ 59
def prefixEnd_7569687 : Nat := 4983230072969 + 3 ^ 40 * 7569687 * 2
def baseEnd_7569687 : Nat := 1295629278363543432833383

theorem tailTrace_7569687 : CollatzResearch.WordTrace tailWord_7569687 prefixEnd_7569687 1295629278363543432833383 := by
  unfold tailWord_7569687
  simp only [CollatzResearch.WordTrace]
  refine ⟨276089166527324273459675315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184059444351549515639783543 276089166527324273459675315)
  ·
    refine ⟨414133749790986410189512973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276089166527324273459675315 414133749790986410189512973)
    ·
      refine ⟨155300156171619903821067365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414133749790986410189512973 155300156171619903821067365)
      ·
        refine ⟨29118779282178731966450131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155300156171619903821067365 29118779282178731966450131)
        ·
          refine ⟨43678168923268097949675197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29118779282178731966450131 43678168923268097949675197)
          ·
            refine ⟨16379313346225536731128199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43678168923268097949675197 16379313346225536731128199)
            ·
              refine ⟨24568970019338305096692299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16379313346225536731128199 24568970019338305096692299)
              ·
                refine ⟨36853455029007457645038449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24568970019338305096692299 36853455029007457645038449)
                ·
                  refine ⟨27640091271755593233778837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36853455029007457645038449 27640091271755593233778837)
                  ·
                    refine ⟨1295629278363543432833383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27640091271755593233778837 1295629278363543432833383)
                    ·
                      rfl

theorem cell23_7569687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_7569687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569687 prefixEnd_7569687 := by exact prefixLift 7569687
  have htrace : WordTrace (prefixWord ++ tailWord_7569687) baseStart_7569687 baseEnd_7569687 := by
    simpa [prefixWord, tailWord_7569687, baseEnd_7569687] using wordTrace_append hprefix tailTrace_7569687
  have hstable : (prefixWord ++ tailWord_7569687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569687).length < 2 ^ (prefixWord ++ tailWord_7569687).sum := by decide
  have hdescent : baseEnd_7569687 < baseStart_7569687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569727 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_7569727 : Nat := 118140960795 + 7569727 * 2 ^ 59
def prefixEnd_7569727 : Nat := 4983230072969 + 3 ^ 40 * 7569727 * 2
def baseEnd_7569727 : Nat := 3886908374316810141999965

theorem tailTrace_7569727 : CollatzResearch.WordTrace tailWord_7569727 prefixEnd_7569727 3886908374316810141999965 := by
  unfold tailWord_7569727
  simp only [CollatzResearch.WordTrace]
  refine ⟨276090625447179360291131435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184060416964786240194087623 276090625447179360291131435)
  ·
    refine ⟨414135938170769040436697153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276090625447179360291131435 414135938170769040436697153)
    ·
      refine ⟨310601953628076780327522865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414135938170769040436697153 310601953628076780327522865)
      ·
        refine ⟨232951465221057585245642149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310601953628076780327522865 232951465221057585245642149)
        ·
          refine ⟨43678399728948297233557903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232951465221057585245642149 43678399728948297233557903)
          ·
            refine ⟨65517599593422445850336855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43678399728948297233557903 65517599593422445850336855)
            ·
              refine ⟨98276399390133668775505283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65517599593422445850336855 98276399390133668775505283)
              ·
                refine ⟨147414599085200503163257925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98276399390133668775505283 147414599085200503163257925)
                ·
                  refine ⟨27640237328475094343110861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147414599085200503163257925 27640237328475094343110861)
                  ·
                    refine ⟨10365088998178160378666573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27640237328475094343110861 10365088998178160378666573)
                    ·
                      refine ⟨3886908374316810141999965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10365088998178160378666573 3886908374316810141999965)
                      ·
                        rfl

theorem cell23_7569727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_7569727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569727 prefixEnd_7569727 := by exact prefixLift 7569727
  have htrace : WordTrace (prefixWord ++ tailWord_7569727) baseStart_7569727 baseEnd_7569727 := by
    simpa [prefixWord, tailWord_7569727, baseEnd_7569727] using wordTrace_append hprefix tailTrace_7569727
  have hstable : (prefixWord ++ tailWord_7569727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569727).length < 2 ^ (prefixWord ++ tailWord_7569727).sum := by decide
  have hdescent : baseEnd_7569727 < baseStart_7569727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569854 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7569854 : Nat := 118140960795 + 7569854 * 2 ^ 59
def prefixEnd_7569854 : Nat := 4983230072969 + 3 ^ 40 * 7569854 * 2
def baseEnd_7569854 : Nat := 1295657862119977048370627

theorem tailTrace_7569854 : CollatzResearch.WordTrace tailWord_7569854 prefixEnd_7569854 1295657862119977048370627 := by
  unfold tailWord_7569854
  simp only [CollatzResearch.WordTrace]
  refine ⟨34511907189714907622625577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184063505011812840654003077 34511907189714907622625577)
  ·
    refine ⟨25883930392286180716969183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34511907189714907622625577 25883930392286180716969183)
    ·
      refine ⟨38825895588429271075453775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25883930392286180716969183 38825895588429271075453775)
      ·
        refine ⟨58238843382643906613180663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38825895588429271075453775 58238843382643906613180663)
        ·
          refine ⟨87358265073965859919770995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58238843382643906613180663 87358265073965859919770995)
          ·
            refine ⟨131037397610948789879656493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87358265073965859919770995 131037397610948789879656493)
            ·
              refine ⟨49139024104105796204871185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131037397610948789879656493 49139024104105796204871185)
              ·
                refine ⟨36854268078079347153653389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49139024104105796204871185 36854268078079347153653389)
                ·
                  refine ⟨13820350529279755182620021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36854268078079347153653389 13820350529279755182620021)
                  ·
                    refine ⟨1295657862119977048370627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13820350529279755182620021 1295657862119977048370627)
                    ·
                      rfl

theorem cell23_7569854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7569854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569854 prefixEnd_7569854 := by exact prefixLift 7569854
  have htrace : WordTrace (prefixWord ++ tailWord_7569854) baseStart_7569854 baseEnd_7569854 := by
    simpa [prefixWord, tailWord_7569854, baseEnd_7569854] using wordTrace_append hprefix tailTrace_7569854
  have hstable : (prefixWord ++ tailWord_7569854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569854).length < 2 ^ (prefixWord ++ tailWord_7569854).sum := by decide
  have hdescent : baseEnd_7569854 < baseStart_7569854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569868 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7569868 : Nat := 118140960795 + 7569868 * 2 ^ 59
def prefixEnd_7569868 : Nat := 4983230072969 + 3 ^ 40 * 7569868 * 2
def baseEnd_7569868 : Nat := 3886980775089094090336817

theorem tailTrace_7569868 : CollatzResearch.WordTrace tailWord_7569868 prefixEnd_7569868 3886980775089094090336817 := by
  unfold tailWord_7569868
  simp only [CollatzResearch.WordTrace]
  refine ⟨138047884069834270686007129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184063845426445694248009505 138047884069834270686007129)
  ·
    refine ⟨103535913052375703014505347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138047884069834270686007129 103535913052375703014505347)
    ·
      refine ⟨155303869578563554521758021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103535913052375703014505347 155303869578563554521758021)
      ·
        refine ⟨29119475545980666472829629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155303869578563554521758021 29119475545980666472829629)
        ·
          refine ⟨10919803329742749927311111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29119475545980666472829629 10919803329742749927311111)
          ·
            refine ⟨16379704994614124890966667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919803329742749927311111 16379704994614124890966667)
            ·
              refine ⟨24569557491921187336450001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16379704994614124890966667 24569557491921187336450001)
              ·
                refine ⟨18427168118940890502337501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24569557491921187336450001 18427168118940890502337501)
                ·
                  refine ⟨6910188044602833938376563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18427168118940890502337501 6910188044602833938376563)
                  ·
                    refine ⟨10365282066904250907564845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910188044602833938376563 10365282066904250907564845)
                    ·
                      refine ⟨3886980775089094090336817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10365282066904250907564845 3886980775089094090336817)
                      ·
                        rfl

theorem cell23_7569868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7569868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569868 prefixEnd_7569868 := by exact prefixLift 7569868
  have htrace : WordTrace (prefixWord ++ tailWord_7569868) baseStart_7569868 baseEnd_7569868 := by
    simpa [prefixWord, tailWord_7569868, baseEnd_7569868] using wordTrace_append hprefix tailTrace_7569868
  have hstable : (prefixWord ++ tailWord_7569868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569868).length < 2 ^ (prefixWord ++ tailWord_7569868).sum := by decide
  have hdescent : baseEnd_7569868 < baseStart_7569868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569878 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_7569878 : Nat := 118140960795 + 7569878 * 2 ^ 59
def prefixEnd_7569878 : Nat := 4983230072969 + 3 ^ 40 * 7569878 * 2
def baseEnd_7569878 : Nat := 3886985909895639051211771

theorem tailTrace_7569878 : CollatzResearch.WordTrace tailWord_7569878 prefixEnd_7569878 3886985909895639051211771 := by
  unfold tailWord_7569878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256008304352019567492393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184064088579754875386585525 17256008304352019567492393)
  ·
    refine ⟨12942006228264014675619295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17256008304352019567492393 12942006228264014675619295)
    ·
      refine ⟨19413009342396022013428943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12942006228264014675619295 19413009342396022013428943)
      ·
        refine ⟨29119514013594033020143415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413009342396022013428943 29119514013594033020143415)
        ·
          refine ⟨43679271020391049530215123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29119514013594033020143415 43679271020391049530215123)
          ·
            refine ⟨65518906530586574295322685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43679271020391049530215123 65518906530586574295322685)
            ·
              refine ⟨24569589948969965360746007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65518906530586574295322685 24569589948969965360746007)
              ·
                refine ⟨36854384923454948041119011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24569589948969965360746007 36854384923454948041119011)
                ·
                  refine ⟨55281577385182422061678517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36854384923454948041119011 55281577385182422061678517)
                  ·
                    refine ⟨5182647879860852068282361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55281577385182422061678517 5182647879860852068282361)
                    ·
                      refine ⟨3886985909895639051211771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182647879860852068282361 3886985909895639051211771)
                      ·
                        rfl

theorem cell23_7569878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_7569878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569878 prefixEnd_7569878 := by exact prefixLift 7569878
  have htrace : WordTrace (prefixWord ++ tailWord_7569878) baseStart_7569878 baseEnd_7569878 := by
    simpa [prefixWord, tailWord_7569878, baseEnd_7569878] using wordTrace_append hprefix tailTrace_7569878
  have hstable : (prefixWord ++ tailWord_7569878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569878).length < 2 ^ (prefixWord ++ tailWord_7569878).sum := by decide
  have hdescent : baseEnd_7569878 < baseStart_7569878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569885 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_7569885 : Nat := 118140960795 + 7569885 * 2 ^ 59
def prefixEnd_7569885 : Nat := 4983230072969 + 3 ^ 40 * 7569885 * 2
def baseEnd_7569885 : Nat := 3886989504260220523824239

theorem tailTrace_7569885 : CollatzResearch.WordTrace tailWord_7569885 prefixEnd_7569885 3886989504260220523824239 := by
  unfold tailWord_7569885
  simp only [CollatzResearch.WordTrace]
  refine ⟨276096388180606953275383109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184064258787071302183588739 276096388180606953275383109)
  ·
    refine ⟨51768072783863803739134333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276096388180606953275383109 51768072783863803739134333)
    ·
      refine ⟨19413027293948926402175375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51768072783863803739134333 19413027293948926402175375)
      ·
        refine ⟨29119540940923389603263063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413027293948926402175375 29119540940923389603263063)
        ·
          refine ⟨43679311411385084404894595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29119540940923389603263063 43679311411385084404894595)
          ·
            refine ⟨65518967117077626607341893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43679311411385084404894595 65518967117077626607341893)
            ·
              refine ⟨12284806334452054988876605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65518967117077626607341893 12284806334452054988876605)
              ·
                refine ⟨4606802375419520620828727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12284806334452054988876605 4606802375419520620828727)
                ·
                  refine ⟨6910203563129280931243091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606802375419520620828727 6910203563129280931243091)
                  ·
                    refine ⟨10365305344693921396864637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910203563129280931243091 10365305344693921396864637)
                    ·
                      refine ⟨3886989504260220523824239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10365305344693921396864637 3886989504260220523824239)
                      ·
                        rfl

theorem cell23_7569885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_7569885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569885 prefixEnd_7569885 := by exact prefixLift 7569885
  have htrace : WordTrace (prefixWord ++ tailWord_7569885) baseStart_7569885 baseEnd_7569885 := by
    simpa [prefixWord, tailWord_7569885, baseEnd_7569885] using wordTrace_append hprefix tailTrace_7569885
  have hstable : (prefixWord ++ tailWord_7569885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569885).length < 2 ^ (prefixWord ++ tailWord_7569885).sum := by decide
  have hdescent : baseEnd_7569885 < baseStart_7569885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569921 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_7569921 : Nat := 118140960795 + 7569921 * 2 ^ 59
def prefixEnd_7569921 : Nat := 4983230072969 + 3 ^ 40 * 7569921 * 2
def baseEnd_7569921 : Nat := 3887007989563782382974073

theorem tailTrace_7569921 : CollatzResearch.WordTrace tailWord_7569921 prefixEnd_7569921 3887007989563782382974073 := by
  unfold tailWord_7569921
  simp only [CollatzResearch.WordTrace]
  refine ⟨276097701208476531423693617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184065134138984354282462411 276097701208476531423693617)
  ·
    refine ⟨207073275906357398567770213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276097701208476531423693617 207073275906357398567770213)
    ·
      refine ⟨38826239232442012231456915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207073275906357398567770213 38826239232442012231456915)
      ·
        refine ⟨58239358848663018347185373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38826239232442012231456915 58239358848663018347185373)
        ·
          refine ⟨21839759568248631880194515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58239358848663018347185373 21839759568248631880194515)
          ·
            refine ⟨32759639352372947820291773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21839759568248631880194515 32759639352372947820291773)
            ·
              refine ⟨12284864757139855432609415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32759639352372947820291773 12284864757139855432609415)
              ·
                refine ⟨18427297135709783148914123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12284864757139855432609415 18427297135709783148914123)
                ·
                  refine ⟨27640945703564674723371185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18427297135709783148914123 27640945703564674723371185)
                  ·
                    refine ⟨20730709277673506042528389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27640945703564674723371185 20730709277673506042528389)
                    ·
                      refine ⟨3887007989563782382974073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20730709277673506042528389 3887007989563782382974073)
                      ·
                        rfl

theorem cell23_7569921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_7569921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569921 prefixEnd_7569921 := by exact prefixLift 7569921
  have htrace : WordTrace (prefixWord ++ tailWord_7569921) baseStart_7569921 baseEnd_7569921 := by
    simpa [prefixWord, tailWord_7569921, baseEnd_7569921] using wordTrace_append hprefix tailTrace_7569921
  have hstable : (prefixWord ++ tailWord_7569921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569921).length < 2 ^ (prefixWord ++ tailWord_7569921).sum := by decide
  have hdescent : baseEnd_7569921 < baseStart_7569921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569931 : List Nat := [1, 1, 1, 1, 7, 3, 2, 7]
def baseStart_7569931 : Nat := 118140960795 + 7569931 * 2 ^ 59
def prefixEnd_7569931 : Nat := 4983230072969 + 3 ^ 40 * 7569931 * 2
def baseEnd_7569931 : Nat := 143963449050752864587001

theorem tailTrace_7569931 : CollatzResearch.WordTrace tailWord_7569931 prefixEnd_7569931 143963449050752864587001 := by
  unfold tailWord_7569931
  simp only [CollatzResearch.WordTrace]
  refine ⟨276098065938440303131557647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184065377292293535421038431 276098065938440303131557647)
  ·
    refine ⟨414147098907660454697336471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276098065938440303131557647 414147098907660454697336471)
    ·
      refine ⟨621220648361490682046004707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414147098907660454697336471 621220648361490682046004707)
      ·
        refine ⟨931830972542236023069007061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621220648361490682046004707 931830972542236023069007061)
        ·
          refine ⟨21839788418958656790679853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 931830972542236023069007061 21839788418958656790679853)
          ·
            refine ⟨8189920657109496296504945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21839788418958656790679853 8189920657109496296504945)
            ·
              refine ⟨6142440492832122222378709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8189920657109496296504945 6142440492832122222378709)
              ·
                refine ⟨143963449050752864587001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6142440492832122222378709 143963449050752864587001)
                ·
                  rfl

theorem cell23_7569931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 7].length) (baseStart_7569931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569931 prefixEnd_7569931 := by exact prefixLift 7569931
  have htrace : WordTrace (prefixWord ++ tailWord_7569931) baseStart_7569931 baseEnd_7569931 := by
    simpa [prefixWord, tailWord_7569931, baseEnd_7569931] using wordTrace_append hprefix tailTrace_7569931
  have hstable : (prefixWord ++ tailWord_7569931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569931).length < 2 ^ (prefixWord ++ tailWord_7569931).sum := by decide
  have hdescent : baseEnd_7569931 < baseStart_7569931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569941 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_7569941 : Nat := 118140960795 + 7569941 * 2 ^ 59
def prefixEnd_7569941 : Nat := 4983230072969 + 3 ^ 40 * 7569941 * 2
def baseEnd_7569941 : Nat := 3887018259176872304723981

theorem tailTrace_7569941 : CollatzResearch.WordTrace tailWord_7569941 prefixEnd_7569941 3887018259176872304723981 := by
  unfold tailWord_7569941
  simp only [CollatzResearch.WordTrace]
  refine ⟨276098430668404074839421677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184065620445602716559614451 276098430668404074839421677)
  ·
    refine ⟨103536911500651528064783129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276098430668404074839421677 103536911500651528064783129)
    ·
      refine ⟨77652683625488646048587347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103536911500651528064783129 77652683625488646048587347)
      ·
        refine ⟨116479025438232969072881021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77652683625488646048587347 116479025438232969072881021)
        ·
          refine ⟨43679634539337363402330383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116479025438232969072881021 43679634539337363402330383)
          ·
            refine ⟨65519451809006045103495575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43679634539337363402330383 65519451809006045103495575)
            ·
              refine ⟨98279177713509067655243363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65519451809006045103495575 98279177713509067655243363)
              ·
                refine ⟨147418766570263601482865045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98279177713509067655243363 147418766570263601482865045)
                ·
                  refine ⟨6910254682981106319509299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147418766570263601482865045 6910254682981106319509299)
                  ·
                    refine ⟨10365382024471659479263949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910254682981106319509299 10365382024471659479263949)
                    ·
                      refine ⟨3887018259176872304723981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10365382024471659479263949 3887018259176872304723981)
                      ·
                        rfl

theorem cell23_7569941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_7569941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569941 prefixEnd_7569941 := by exact prefixLift 7569941
  have htrace : WordTrace (prefixWord ++ tailWord_7569941) baseStart_7569941 baseEnd_7569941 := by
    simpa [prefixWord, tailWord_7569941, baseEnd_7569941] using wordTrace_append hprefix tailTrace_7569941
  have hstable : (prefixWord ++ tailWord_7569941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569941).length < 2 ^ (prefixWord ++ tailWord_7569941).sum := by decide
  have hdescent : baseEnd_7569941 < baseStart_7569941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569947 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_7569947 : Nat := 118140960795 + 7569947 * 2 ^ 59
def prefixEnd_7569947 : Nat := 4983230072969 + 3 ^ 40 * 7569947 * 2
def baseEnd_7569947 : Nat := 3887021340060799281248953

theorem tailTrace_7569947 : CollatzResearch.WordTrace tailWord_7569947 prefixEnd_7569947 3887021340060799281248953 := by
  unfold tailWord_7569947
  simp only [CollatzResearch.WordTrace]
  refine ⟨276098649506382337864140095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184065766337588225242760063 276098649506382337864140095)
  ·
    refine ⟨414147974259573506796210143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276098649506382337864140095 414147974259573506796210143)
    ·
      refine ⟨621221961389360260194315215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414147974259573506796210143 621221961389360260194315215)
      ·
        refine ⟨931832942084040390291472823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621221961389360260194315215 931832942084040390291472823)
        ·
          refine ⟨1397749413126060585437209235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931832942084040390291472823 1397749413126060585437209235)
          ·
            refine ⟨2096624119689090878155813853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397749413126060585437209235 2096624119689090878155813853)
            ·
              refine ⟨786234044883409079308430195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2096624119689090878155813853 786234044883409079308430195)
              ·
                refine ⟨1179351067325113618962645293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786234044883409079308430195 1179351067325113618962645293)
                ·
                  refine ⟨442256650246917607110991985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179351067325113618962645293 442256650246917607110991985)
                  ·
                    refine ⟨331692487685188205333243989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 442256650246917607110991985 331692487685188205333243989)
                    ·
                      refine ⟨3887021340060799281248953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 331692487685188205333243989 3887021340060799281248953)
                      ·
                        rfl

theorem cell23_7569947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_7569947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569947 prefixEnd_7569947 := by exact prefixLift 7569947
  have htrace : WordTrace (prefixWord ++ tailWord_7569947) baseStart_7569947 baseEnd_7569947 := by
    simpa [prefixWord, tailWord_7569947, baseEnd_7569947] using wordTrace_append hprefix tailTrace_7569947
  have hstable : (prefixWord ++ tailWord_7569947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569947).length < 2 ^ (prefixWord ++ tailWord_7569947).sum := by decide
  have hdescent : baseEnd_7569947 < baseStart_7569947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569951 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 5, 3, 2]
def baseStart_7569951 : Nat := 118140960795 + 7569951 * 2 ^ 59
def prefixEnd_7569951 : Nat := 4983230072969 + 3 ^ 40 * 7569951 * 2
def baseEnd_7569951 : Nat := 3887023393983417265598935

theorem tailTrace_7569951 : CollatzResearch.WordTrace tailWord_7569951 prefixEnd_7569951 3887023393983417265598935 := by
  unfold tailWord_7569951
  simp only [CollatzResearch.WordTrace]
  refine ⟨276098795398367846547285707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184065863598911897698190471 276098795398367846547285707)
  ·
    refine ⟨414148193097551769820928561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276098795398367846547285707 414148193097551769820928561)
    ·
      refine ⟨310611144823163827365696421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414148193097551769820928561 310611144823163827365696421)
      ·
        refine ⟨58239589654343217631068079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310611144823163827365696421 58239589654343217631068079)
        ·
          refine ⟨87359384481514826446602119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58239589654343217631068079 87359384481514826446602119)
          ·
            refine ⟨131039076722272239669903179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87359384481514826446602119 131039076722272239669903179)
            ·
              refine ⟨196558615083408359504854769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131039076722272239669903179 196558615083408359504854769)
              ·
                refine ⟨147418961312556269628641077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196558615083408359504854769 147418961312556269628641077)
                ·
                  refine ⟨13820527623052150277685101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147418961312556269628641077 13820527623052150277685101)
                  ·
                    refine ⟨5182697858644556354131913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13820527623052150277685101 5182697858644556354131913)
                    ·
                      refine ⟨3887023393983417265598935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182697858644556354131913 3887023393983417265598935)
                      ·
                        rfl

theorem cell23_7569951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_7569951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569951 prefixEnd_7569951 := by exact prefixLift 7569951
  have htrace : WordTrace (prefixWord ++ tailWord_7569951) baseStart_7569951 baseEnd_7569951 := by
    simpa [prefixWord, tailWord_7569951, baseEnd_7569951] using wordTrace_append hprefix tailTrace_7569951
  have hstable : (prefixWord ++ tailWord_7569951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569951).length < 2 ^ (prefixWord ++ tailWord_7569951).sum := by decide
  have hdescent : baseEnd_7569951 < baseStart_7569951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569954 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7569954 : Nat := 118140960795 + 7569954 * 2 ^ 59
def prefixEnd_7569954 : Nat := 4983230072969 + 3 ^ 40 * 7569954 * 2
def baseEnd_7569954 : Nat := 3887024934425380753861421

theorem tailTrace_7569954 : CollatzResearch.WordTrace tailWord_7569954 prefixEnd_7569954 3887024934425380753861421 := by
  unfold tailWord_7569954
  simp only [CollatzResearch.WordTrace]
  refine ⟨69024726204339244514911229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184065936544904652039763277 69024726204339244514911229)
  ·
    refine ⟨25884272326627216693091711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69024726204339244514911229 25884272326627216693091711)
    ·
      refine ⟨38826408489940825039637567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25884272326627216693091711 38826408489940825039637567)
      ·
        refine ⟨58239612734911237559456351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38826408489940825039637567 58239612734911237559456351)
        ·
          refine ⟨87359419102366856339184527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58239612734911237559456351 87359419102366856339184527)
          ·
            refine ⟨131039128653550284508776791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87359419102366856339184527 131039128653550284508776791)
            ·
              refine ⟨196558692980325426763165187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131039128653550284508776791 196558692980325426763165187)
              ·
                refine ⟨294838039470488140144747781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196558692980325426763165187 294838039470488140144747781)
                ·
                  refine ⟨55282132400716526277140209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294838039470488140144747781 55282132400716526277140209)
                  ·
                    refine ⟨41461599300537394707855157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55282132400716526277140209 41461599300537394707855157)
                    ·
                      refine ⟨3887024934425380753861421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41461599300537394707855157 3887024934425380753861421)
                      ·
                        rfl

theorem cell23_7569954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7569954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569954 prefixEnd_7569954 := by exact prefixLift 7569954
  have htrace : WordTrace (prefixWord ++ tailWord_7569954) baseStart_7569954 baseEnd_7569954 := by
    simpa [prefixWord, tailWord_7569954, baseEnd_7569954] using wordTrace_append hprefix tailTrace_7569954
  have hstable : (prefixWord ++ tailWord_7569954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569954).length < 2 ^ (prefixWord ++ tailWord_7569954).sum := by decide
  have hdescent : baseEnd_7569954 < baseStart_7569954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569959 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7569959 : Nat := 118140960795 + 7569959 * 2 ^ 59
def prefixEnd_7569959 : Nat := 4983230072969 + 3 ^ 40 * 7569959 * 2
def baseEnd_7569959 : Nat := 3887027501828653234298899

theorem tailTrace_7569959 : CollatzResearch.WordTrace tailWord_7569959 prefixEnd_7569959 3887027501828653234298899 := by
  unfold tailWord_7569959
  simp only [CollatzResearch.WordTrace]
  refine ⟨276099087182338863913576931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184066058121559242609051287 276099087182338863913576931)
  ·
    refine ⟨414148630773508295870365397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276099087182338863913576931 414148630773508295870365397)
    ·
      refine ⟨9706608533754100684461689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 414148630773508295870365397 9706608533754100684461689)
      ·
        refine ⟨7279956400315575513346267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9706608533754100684461689 7279956400315575513346267)
        ·
          refine ⟨10919934600473363270019401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7279956400315575513346267 10919934600473363270019401)
          ·
            refine ⟨8189950950355022452514551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10919934600473363270019401 8189950950355022452514551)
            ·
              refine ⟨12284926425532533678771827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189950950355022452514551 12284926425532533678771827)
              ·
                refine ⟨18427389638298800518157741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12284926425532533678771827 18427389638298800518157741)
                ·
                  refine ⟨6910271114362050194309153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18427389638298800518157741 6910271114362050194309153)
                  ·
                    refine ⟨5182703335771537645731865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6910271114362050194309153 5182703335771537645731865)
                    ·
                      refine ⟨3887027501828653234298899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182703335771537645731865 3887027501828653234298899)
                      ·
                        rfl

theorem cell23_7569959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7569959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569959 prefixEnd_7569959 := by exact prefixLift 7569959
  have htrace : WordTrace (prefixWord ++ tailWord_7569959) baseStart_7569959 baseEnd_7569959 := by
    simpa [prefixWord, tailWord_7569959, baseEnd_7569959] using wordTrace_append hprefix tailTrace_7569959
  have hstable : (prefixWord ++ tailWord_7569959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569959).length < 2 ^ (prefixWord ++ tailWord_7569959).sum := by decide
  have hdescent : baseEnd_7569959 < baseStart_7569959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569965 : List Nat := [1, 5, 4, 1, 1, 1, 2, 8]
def baseStart_7569965 : Nat := 118140960795 + 7569965 * 2 ^ 59
def prefixEnd_7569965 : Nat := 4983230072969 + 3 ^ 40 * 7569965 * 2
def baseEnd_7569965 : Nat := 143964095656021489289773

theorem tailTrace_7569965 : CollatzResearch.WordTrace tailWord_7569965 prefixEnd_7569965 143964095656021489289773 := by
  unfold tailWord_7569965
  simp only [CollatzResearch.WordTrace]
  refine ⟨276099306020317126938295349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184066204013544751292196899 276099306020317126938295349)
  ·
    refine ⟨25884309939404730650465189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276099306020317126938295349 25884309939404730650465189)
    ·
      refine ⟨4853308113638386996962223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25884309939404730650465189 4853308113638386996962223)
      ·
        refine ⟨7279962170457580495443335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853308113638386996962223 7279962170457580495443335)
        ·
          refine ⟨10919943255686370743165003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7279962170457580495443335 10919943255686370743165003)
          ·
            refine ⟨16379914883529556114747505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919943255686370743165003 16379914883529556114747505)
            ·
              refine ⟨12284936162647167086060629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16379914883529556114747505 12284936162647167086060629)
              ·
                refine ⟨143964095656021489289773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12284936162647167086060629 143964095656021489289773)
                ·
                  rfl

theorem cell23_7569965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 8].length) (baseStart_7569965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569965 prefixEnd_7569965 := by exact prefixLift 7569965
  have htrace : WordTrace (prefixWord ++ tailWord_7569965) baseStart_7569965 baseEnd_7569965 := by
    simpa [prefixWord, tailWord_7569965, baseEnd_7569965] using wordTrace_append hprefix tailTrace_7569965
  have hstable : (prefixWord ++ tailWord_7569965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569965).length < 2 ^ (prefixWord ++ tailWord_7569965).sum := by decide
  have hdescent : baseEnd_7569965 < baseStart_7569965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569984 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_7569984 : Nat := 118140960795 + 7569984 * 2 ^ 59
def prefixEnd_7569984 : Nat := 4983230072969 + 3 ^ 40 * 7569984 * 2
def baseEnd_7569984 : Nat := 3887040338845015636486283

theorem tailTrace_7569984 : CollatzResearch.WordTrace tailWord_7569984 prefixEnd_7569984 3887040338845015636486283 := by
  unfold tailWord_7569984
  simp only [CollatzResearch.WordTrace]
  refine ⟨138049999503624146591618503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184066666004832195455491337 138049999503624146591618503)
  ·
    refine ⟨207074999255436219887427755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138049999503624146591618503 207074999255436219887427755)
    ·
      refine ⟨310612498883154329831141633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207074999255436219887427755 310612498883154329831141633)
      ·
        refine ⟨232959374162365747373356225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310612498883154329831141633 232959374162365747373356225)
        ·
          refine ⟨174719530621774310530017169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232959374162365747373356225 174719530621774310530017169)
          ·
            refine ⟨131039647966330732897512877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174719530621774310530017169 131039647966330732897512877)
            ·
              refine ⟨49139867987374024836567329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131039647966330732897512877 49139867987374024836567329)
              ·
                refine ⟨36854900990530518627425497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49139867987374024836567329 36854900990530518627425497)
                ·
                  refine ⟨27641175742897888970569123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36854900990530518627425497 27641175742897888970569123)
                  ·
                    refine ⟨41461763614346833455853685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27641175742897888970569123 41461763614346833455853685)
                    ·
                      refine ⟨3887040338845015636486283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41461763614346833455853685 3887040338845015636486283)
                      ·
                        rfl

theorem cell23_7569984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_7569984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569984 prefixEnd_7569984 := by exact prefixLift 7569984
  have htrace : WordTrace (prefixWord ++ tailWord_7569984) baseStart_7569984 baseEnd_7569984 := by
    simpa [prefixWord, tailWord_7569984, baseEnd_7569984] using wordTrace_append hprefix tailTrace_7569984
  have hstable : (prefixWord ++ tailWord_7569984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569984).length < 2 ^ (prefixWord ++ tailWord_7569984).sum := by decide
  have hdescent : baseEnd_7569984 < baseStart_7569984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569985 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_7569985 : Nat := 118140960795 + 7569985 * 2 ^ 59
def prefixEnd_7569985 : Nat := 4983230072969 + 3 ^ 40 * 7569985 * 2
def baseEnd_7569985 : Nat := 3887040852325670132573779

theorem tailTrace_7569985 : CollatzResearch.WordTrace tailWord_7569985 prefixEnd_7569985 3887040852325670132573779 := by
  unfold tailWord_7569985
  simp only [CollatzResearch.WordTrace]
  refine ⟨276100035480244670354023409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184066690320163113569348939 276100035480244670354023409)
  ·
    refine ⟨207075026610183502765517557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276100035480244670354023409 207075026610183502765517557)
    ·
      refine ⟨19413283744704703384267271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207075026610183502765517557 19413283744704703384267271)
      ·
        refine ⟨29119925617057055076400907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413283744704703384267271 29119925617057055076400907)
        ·
          refine ⟨43679888425585582614601361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29119925617057055076400907 43679888425585582614601361)
          ·
            refine ⟨32759916319189186960951021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43679888425585582614601361 32759916319189186960951021)
            ·
              refine ⟨12284968619695945110356633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32759916319189186960951021 12284968619695945110356633)
              ·
                refine ⟨9213726464771958832767475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12284968619695945110356633 9213726464771958832767475)
                ·
                  refine ⟨13820589697157938249151213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9213726464771958832767475 13820589697157938249151213)
                  ·
                    refine ⟨5182721136434226843431705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13820589697157938249151213 5182721136434226843431705)
                    ·
                      refine ⟨3887040852325670132573779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182721136434226843431705 3887040852325670132573779)
                      ·
                        rfl

theorem cell23_7569985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_7569985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569985 prefixEnd_7569985 := by exact prefixLift 7569985
  have htrace : WordTrace (prefixWord ++ tailWord_7569985) baseStart_7569985 baseEnd_7569985 := by
    simpa [prefixWord, tailWord_7569985, baseEnd_7569985] using wordTrace_append hprefix tailTrace_7569985
  have hstable : (prefixWord ++ tailWord_7569985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569985).length < 2 ^ (prefixWord ++ tailWord_7569985).sum := by decide
  have hdescent : baseEnd_7569985 < baseStart_7569985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7569998 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_7569998 : Nat := 118140960795 + 7569998 * 2 ^ 59
def prefixEnd_7569998 : Nat := 4983230072969 + 3 ^ 40 * 7569998 * 2
def baseEnd_7569998 : Nat := 3887047527574178581711219

theorem tailTrace_7569998 : CollatzResearch.WordTrace tailWord_7569998 prefixEnd_7569998 3887047527574178581711219 := by
  unfold tailWord_7569998
  simp only [CollatzResearch.WordTrace]
  refine ⟨34512563703649696696780831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184067006419465049049497765 34512563703649696696780831)
  ·
    refine ⟨51768845555474545045171247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34512563703649696696780831 51768845555474545045171247)
    ·
      refine ⟨77653268333211817567756871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51768845555474545045171247 77653268333211817567756871)
      ·
        refine ⟨116479902499817726351635307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77653268333211817567756871 116479902499817726351635307)
        ·
          refine ⟨174719853749726589527452961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116479902499817726351635307 174719853749726589527452961)
          ·
            refine ⟨131039890312294942145589721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174719853749726589527452961 131039890312294942145589721)
            ·
              refine ⟨98279917734221206609192291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131039890312294942145589721 98279917734221206609192291)
              ·
                refine ⟨147419876601331809913788437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98279917734221206609192291 147419876601331809913788437)
                ·
                  refine ⟨6910306715687428589708833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147419876601331809913788437 6910306715687428589708833)
                  ·
                    refine ⟨5182730036765571442281625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6910306715687428589708833 5182730036765571442281625)
                    ·
                      refine ⟨3887047527574178581711219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182730036765571442281625 3887047527574178581711219)
                      ·
                        rfl

theorem cell23_7569998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_7569998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7569998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7569998 prefixEnd_7569998 := by exact prefixLift 7569998
  have htrace : WordTrace (prefixWord ++ tailWord_7569998) baseStart_7569998 baseEnd_7569998 := by
    simpa [prefixWord, tailWord_7569998, baseEnd_7569998] using wordTrace_append hprefix tailTrace_7569998
  have hstable : (prefixWord ++ tailWord_7569998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7569998).length < 2 ^ (prefixWord ++ tailWord_7569998).sum := by decide
  have hdescent : baseEnd_7569998 < baseStart_7569998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7569998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570038 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_7570038 : Nat := 118140960795 + 7570038 * 2 ^ 59
def prefixEnd_7570038 : Nat := 4983230072969 + 3 ^ 40 * 7570038 * 2
def baseEnd_7570038 : Nat := 431896451866706491690115

theorem tailTrace_7570038 : CollatzResearch.WordTrace tailWord_7570038 prefixEnd_7570038 431896451866706491690115 := by
  unfold tailWord_7570038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256373034315791275356423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184067979032701773603801845 17256373034315791275356423)
  ·
    refine ⟨25884559551473686913034635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17256373034315791275356423 25884559551473686913034635)
    ·
      refine ⟨38826839327210530369551953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25884559551473686913034635 38826839327210530369551953)
      ·
        refine ⟨29120129495407897777163965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38826839327210530369551953 29120129495407897777163965)
        ·
          refine ⟨10920048560777961666436487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29120129495407897777163965 10920048560777961666436487)
          ·
            refine ⟨16380072841166942499654731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10920048560777961666436487 16380072841166942499654731)
            ·
              refine ⟨24570109261750413749482097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16380072841166942499654731 24570109261750413749482097)
              ·
                refine ⟨18427581946312810312111573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24570109261750413749482097 18427581946312810312111573)
                ·
                  refine ⟨431896451866706491690115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18427581946312810312111573 431896451866706491690115)
                  ·
                    rfl

theorem cell23_7570038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_7570038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570038 prefixEnd_7570038 := by exact prefixLift 7570038
  have htrace : WordTrace (prefixWord ++ tailWord_7570038) baseStart_7570038 baseEnd_7570038 := by
    simpa [prefixWord, tailWord_7570038, baseEnd_7570038] using wordTrace_append hprefix tailTrace_7570038
  have hstable : (prefixWord ++ tailWord_7570038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570038).length < 2 ^ (prefixWord ++ tailWord_7570038).sum := by decide
  have hdescent : baseEnd_7570038 < baseStart_7570038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570044 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_7570044 : Nat := 118140960795 + 7570044 * 2 ^ 59
def prefixEnd_7570044 : Nat := 4983230072969 + 3 ^ 40 * 7570044 * 2
def baseEnd_7570044 : Nat := 3887071147684285401736007

theorem tailTrace_7570044 : CollatzResearch.WordTrace tailWord_7570044 prefixEnd_7570044 3887071147684285401736007 := by
  unfold tailWord_7570044
  simp only [CollatzResearch.WordTrace]
  refine ⟨138051093693515461715210593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184068124924687282286947457 138051093693515461715210593)
  ·
    refine ⟨103538320270136596286407945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138051093693515461715210593 103538320270136596286407945)
    ·
      refine ⟨77653740202602447214805959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103538320270136596286407945 77653740202602447214805959)
      ·
        refine ⟨116480610303903670822208939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77653740202602447214805959 116480610303903670822208939)
        ·
          refine ⟨174720915455855506233313409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116480610303903670822208939 174720915455855506233313409)
          ·
            refine ⟨131040686591891629674985057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174720915455855506233313409 131040686591891629674985057)
            ·
              refine ⟨98280514943918722256238793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131040686591891629674985057 98280514943918722256238793)
              ·
                refine ⟨73710386207939041692179095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98280514943918722256238793 73710386207939041692179095)
                ·
                  refine ⟨110565579311908562538268643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73710386207939041692179095 110565579311908562538268643)
                  ·
                    refine ⟨165848368967862843807402965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110565579311908562538268643 165848368967862843807402965)
                    ·
                      refine ⟨3887071147684285401736007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165848368967862843807402965 3887071147684285401736007)
                      ·
                        rfl

theorem cell23_7570044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_7570044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570044 prefixEnd_7570044 := by exact prefixLift 7570044
  have htrace : WordTrace (prefixWord ++ tailWord_7570044) baseStart_7570044 baseEnd_7570044 := by
    simpa [prefixWord, tailWord_7570044, baseEnd_7570044] using wordTrace_append hprefix tailTrace_7570044
  have hstable : (prefixWord ++ tailWord_7570044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570044).length < 2 ^ (prefixWord ++ tailWord_7570044).sum := by decide
  have hdescent : baseEnd_7570044 < baseStart_7570044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570051 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 2, 5]
def baseStart_7570051 : Nat := 118140960795 + 7570051 * 2 ^ 59
def prefixEnd_7570051 : Nat := 4983230072969 + 3 ^ 40 * 7570051 * 2
def baseEnd_7570051 : Nat := 1295691580682955624782825

theorem tailTrace_7570051 : CollatzResearch.WordTrace tailWord_7570051 prefixEnd_7570051 1295691580682955624782825 := by
  unfold tailWord_7570051
  simp only [CollatzResearch.WordTrace]
  refine ⟨276102442698005563625926007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184068295132003709083950671 276102442698005563625926007)
  ·
    refine ⟨414153664047008345438889011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276102442698005563625926007 414153664047008345438889011)
    ·
      refine ⟨621230496070512518158333517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414153664047008345438889011 621230496070512518158333517)
      ·
        refine ⟨232961436026442194309375069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621230496070512518158333517 232961436026442194309375069)
        ·
          refine ⟨87360538509915822866015651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232961436026442194309375069 87360538509915822866015651)
          ·
            refine ⟨131040807764873734299023477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87360538509915822866015651 131040807764873734299023477)
            ·
              refine ⟨12285075727956912590533451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131040807764873734299023477 12285075727956912590533451)
              ·
                refine ⟨18427613591935368885800177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12285075727956912590533451 18427613591935368885800177)
                ·
                  refine ⟨13820710193951526664350133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18427613591935368885800177 13820710193951526664350133)
                  ·
                    refine ⟨1295691580682955624782825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13820710193951526664350133 1295691580682955624782825)
                    ·
                      rfl

theorem cell23_7570051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 5].length) (baseStart_7570051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570051 prefixEnd_7570051 := by exact prefixLift 7570051
  have htrace : WordTrace (prefixWord ++ tailWord_7570051) baseStart_7570051 baseEnd_7570051 := by
    simpa [prefixWord, tailWord_7570051, baseEnd_7570051] using wordTrace_append hprefix tailTrace_7570051
  have hstable : (prefixWord ++ tailWord_7570051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570051).length < 2 ^ (prefixWord ++ tailWord_7570051).sum := by decide
  have hdescent : baseEnd_7570051 < baseStart_7570051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570071 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7570071 : Nat := 118140960795 + 7570071 * 2 ^ 59
def prefixEnd_7570071 : Nat := 4983230072969 + 3 ^ 40 * 7570071 * 2
def baseEnd_7570071 : Nat := 3887085011661956796098383

theorem tailTrace_7570071 : CollatzResearch.WordTrace tailWord_7570071 prefixEnd_7570071 3887085011661956796098383 := by
  unfold tailWord_7570071
  simp only [CollatzResearch.WordTrace]
  refine ⟨276103172157933107041654067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184068781438622071361102711 276103172157933107041654067)
  ·
    refine ⟨414154758236899660562481101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276103172157933107041654067 414154758236899660562481101)
    ·
      refine ⟨155308034338837372710930413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414154758236899660562481101 155308034338837372710930413)
      ·
        refine ⟨58240512877064014766598905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155308034338837372710930413 58240512877064014766598905)
        ·
          refine ⟨43680384657798011074949179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58240512877064014766598905 43680384657798011074949179)
          ·
            refine ⟨65520576986697016612423769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43680384657798011074949179 65520576986697016612423769)
            ·
              refine ⟨49140432740022762459317827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65520576986697016612423769 49140432740022762459317827)
              ·
                refine ⟨73710649110034143688976741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49140432740022762459317827 73710649110034143688976741)
                ·
                  refine ⟨13820746708131401941683139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73710649110034143688976741 13820746708131401941683139)
                  ·
                    refine ⟨20731120062197102912524709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13820746708131401941683139 20731120062197102912524709)
                    ·
                      refine ⟨3887085011661956796098383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20731120062197102912524709 3887085011661956796098383)
                      ·
                        rfl

theorem cell23_7570071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7570071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570071 prefixEnd_7570071 := by exact prefixLift 7570071
  have htrace : WordTrace (prefixWord ++ tailWord_7570071) baseStart_7570071 baseEnd_7570071 := by
    simpa [prefixWord, tailWord_7570071, baseEnd_7570071] using wordTrace_append hprefix tailTrace_7570071
  have hstable : (prefixWord ++ tailWord_7570071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570071).length < 2 ^ (prefixWord ++ tailWord_7570071).sum := by decide
  have hdescent : baseEnd_7570071 < baseStart_7570071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570104 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_7570104 : Nat := 118140960795 + 7570104 * 2 ^ 59
def prefixEnd_7570104 : Nat := 4983230072969 + 3 ^ 40 * 7570104 * 2
def baseEnd_7570104 : Nat := 3887101956523555166985731

theorem tailTrace_7570104 : CollatzResearch.WordTrace tailWord_7570104 prefixEnd_7570104 3887101956523555166985731 := by
  unfold tailWord_7570104
  simp only [CollatzResearch.WordTrace]
  refine ⟨138052187883406776838802683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184069583844542369118403577 138052187883406776838802683)
  ·
    refine ⟨207078281825110165258204025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138052187883406776838802683 207078281825110165258204025)
    ·
      refine ⟨155308711368832623943653019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207078281825110165258204025 155308711368832623943653019)
      ·
        refine ⟨232963067053248935915479529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155308711368832623943653019 232963067053248935915479529)
        ·
          refine ⟨174722300289936701936609647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232963067053248935915479529 174722300289936701936609647)
          ·
            refine ⟨262083450434905052904914471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174722300289936701936609647 262083450434905052904914471)
            ·
              refine ⟨393125175652357579357371707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262083450434905052904914471 393125175652357579357371707)
              ·
                refine ⟨589687763478536369036057561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393125175652357579357371707 589687763478536369036057561)
                ·
                  refine ⟨442265822608902276777043171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589687763478536369036057561 442265822608902276777043171)
                  ·
                    refine ⟨663398733913353415165564757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 442265822608902276777043171 663398733913353415165564757)
                    ·
                      refine ⟨3887101956523555166985731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 663398733913353415165564757 3887101956523555166985731)
                      ·
                        rfl

theorem cell23_7570104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_7570104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570104 prefixEnd_7570104 := by exact prefixLift 7570104
  have htrace : WordTrace (prefixWord ++ tailWord_7570104) baseStart_7570104 baseEnd_7570104 := by
    simpa [prefixWord, tailWord_7570104, baseEnd_7570104] using wordTrace_append hprefix tailTrace_7570104
  have hstable : (prefixWord ++ tailWord_7570104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570104).length < 2 ^ (prefixWord ++ tailWord_7570104).sum := by decide
  have hdescent : baseEnd_7570104 < baseStart_7570104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570108 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_7570108 : Nat := 118140960795 + 7570108 * 2 ^ 59
def prefixEnd_7570108 : Nat := 4983230072969 + 3 ^ 40 * 7570108 * 2
def baseEnd_7570108 : Nat := 3887104010446173151335713

theorem tailTrace_7570108 : CollatzResearch.WordTrace tailWord_7570108 prefixEnd_7570108 3887104010446173151335713 := by
  unfold tailWord_7570108
  simp only [CollatzResearch.WordTrace]
  refine ⟨138052260829399531180375489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184069681105866041573833985 138052260829399531180375489)
  ·
    refine ⟨103539195622049648385281617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138052260829399531180375489 103539195622049648385281617)
    ·
      refine ⟨77654396716537236288961213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103539195622049648385281617 77654396716537236288961213)
      ·
        refine ⟨29120398768701463608360455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77654396716537236288961213 29120398768701463608360455)
        ·
          refine ⟨43680598153052195412540683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29120398768701463608360455 43680598153052195412540683)
          ·
            refine ⟨65520897229578293118811025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43680598153052195412540683 65520897229578293118811025)
            ·
              refine ⟨49140672922183719839108269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65520897229578293118811025 49140672922183719839108269)
              ·
                refine ⟨18427752345818894939665601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49140672922183719839108269 18427752345818894939665601)
                ·
                  refine ⟨13820814259364171204749201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18427752345818894939665601 13820814259364171204749201)
                  ·
                    refine ⟨10365610694523128403561901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13820814259364171204749201 10365610694523128403561901)
                    ·
                      refine ⟨3887104010446173151335713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10365610694523128403561901 3887104010446173151335713)
                      ·
                        rfl

theorem cell23_7570108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_7570108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570108 prefixEnd_7570108 := by exact prefixLift 7570108
  have htrace : WordTrace (prefixWord ++ tailWord_7570108) baseStart_7570108 baseEnd_7570108 := by
    simpa [prefixWord, tailWord_7570108, baseEnd_7570108] using wordTrace_append hprefix tailTrace_7570108
  have hstable : (prefixWord ++ tailWord_7570108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570108).length < 2 ^ (prefixWord ++ tailWord_7570108).sum := by decide
  have hdescent : baseEnd_7570108 < baseStart_7570108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570132 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_7570132 : Nat := 118140960795 + 7570132 * 2 ^ 59
def prefixEnd_7570132 : Nat := 4983230072969 + 3 ^ 40 * 7570132 * 2
def baseEnd_7570132 : Nat := 1295705444660627019145201

theorem tailTrace_7570132 : CollatzResearch.WordTrace tailWord_7570132 prefixEnd_7570132 1295705444660627019145201 := by
  unfold tailWord_7570132
  simp only [CollatzResearch.WordTrace]
  refine ⟨138052698505356057229812325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184070264673808076306416433 138052698505356057229812325)
  ·
    refine ⟨25884880969754260730589811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138052698505356057229812325 25884880969754260730589811)
    ·
      refine ⟨38827321454631391095884717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25884880969754260730589811 38827321454631391095884717)
      ·
        refine ⟨14560245545486771660956769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38827321454631391095884717 14560245545486771660956769)
        ·
          refine ⟨10920184159115078745717577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14560245545486771660956769 10920184159115078745717577)
          ·
            refine ⟨8190138119336309059288183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10920184159115078745717577 8190138119336309059288183)
            ·
              refine ⟨12285207179004463588932275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190138119336309059288183 12285207179004463588932275)
              ·
                refine ⟨18427810768506695383398413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12285207179004463588932275 18427810768506695383398413)
                ·
                  refine ⟨6910429038190010768774405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18427810768506695383398413 6910429038190010768774405)
                  ·
                    refine ⟨1295705444660627019145201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6910429038190010768774405 1295705444660627019145201)
                    ·
                      rfl

theorem cell23_7570132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_7570132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570132 prefixEnd_7570132 := by exact prefixLift 7570132
  have htrace : WordTrace (prefixWord ++ tailWord_7570132) baseStart_7570132 baseEnd_7570132 := by
    simpa [prefixWord, tailWord_7570132, baseEnd_7570132] using wordTrace_append hprefix tailTrace_7570132
  have hstable : (prefixWord ++ tailWord_7570132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570132).length < 2 ^ (prefixWord ++ tailWord_7570132).sum := by decide
  have hdescent : baseEnd_7570132 < baseStart_7570132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570145 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 6]
def baseStart_7570145 : Nat := 118140960795 + 7570145 * 2 ^ 59
def prefixEnd_7570145 : Nat := 4983230072969 + 3 ^ 40 * 7570145 * 2
def baseEnd_7570145 : Nat := 431902556581154389619227

theorem tailTrace_7570145 : CollatzResearch.WordTrace tailWord_7570145 prefixEnd_7570145 431902556581154389619227 := by
  unfold tailWord_7570145
  simp only [CollatzResearch.WordTrace]
  refine ⟨276105871159665017679847889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184070580773110011786565259 276105871159665017679847889)
  ·
    refine ⟨207079403369748763259885917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276105871159665017679847889 207079403369748763259885917)
    ·
      refine ⟨77654776263655786222457219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207079403369748763259885917 77654776263655786222457219)
      ·
        refine ⟨116482164395483679333685829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77654776263655786222457219 116482164395483679333685829)
        ·
          refine ⟨21840405824153189875066093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116482164395483679333685829 21840405824153189875066093)
          ·
            refine ⟨8190152184057446203149785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21840405824153189875066093 8190152184057446203149785)
            ·
              refine ⟨6142614138043084652362339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8190152184057446203149785 6142614138043084652362339)
              ·
                refine ⟨9213921207064626978543509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6142614138043084652362339 9213921207064626978543509)
                ·
                  refine ⟨431902556581154389619227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9213921207064626978543509 431902556581154389619227)
                  ·
                    rfl

theorem cell23_7570145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 6].length) (baseStart_7570145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570145 prefixEnd_7570145 := by exact prefixLift 7570145
  have htrace : WordTrace (prefixWord ++ tailWord_7570145) baseStart_7570145 baseEnd_7570145 := by
    simpa [prefixWord, tailWord_7570145, baseEnd_7570145] using wordTrace_append hprefix tailTrace_7570145
  have hstable : (prefixWord ++ tailWord_7570145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570145).length < 2 ^ (prefixWord ++ tailWord_7570145).sum := by decide
  have hdescent : baseEnd_7570145 < baseStart_7570145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570158 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_7570158 : Nat := 118140960795 + 7570158 * 2 ^ 59
def prefixEnd_7570158 : Nat := 4983230072969 + 3 ^ 40 * 7570158 * 2
def baseEnd_7570158 : Nat := 1295709894826299318570161

theorem tailTrace_7570158 : CollatzResearch.WordTrace tailWord_7570158 prefixEnd_7570158 1295709894826299318570161 := by
  unfold tailWord_7570158
  simp only [CollatzResearch.WordTrace]
  refine ⟨34513293163577240112508891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184070896872411947266714085 34513293163577240112508891)
  ·
    refine ⟨51769939745365860168763337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34513293163577240112508891 51769939745365860168763337)
    ·
      refine ⟨38827454809024395126572503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51769939745365860168763337 38827454809024395126572503)
      ·
        refine ⟨58241182213536592689858755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38827454809024395126572503 58241182213536592689858755)
        ·
          refine ⟨87361773320304889034788133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58241182213536592689858755 87361773320304889034788133)
          ·
            refine ⟨16380332497557166694022775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87361773320304889034788133 16380332497557166694022775)
            ·
              refine ⟨24570498746335750041034163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16380332497557166694022775 24570498746335750041034163)
              ·
                refine ⟨36855748119503625061551245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24570498746335750041034163 36855748119503625061551245)
                ·
                  refine ⟨13820905544813859398081717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36855748119503625061551245 13820905544813859398081717)
                  ·
                    refine ⟨1295709894826299318570161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13820905544813859398081717 1295709894826299318570161)
                    ·
                      rfl

theorem cell23_7570158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_7570158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570158 prefixEnd_7570158 := by exact prefixLift 7570158
  have htrace : WordTrace (prefixWord ++ tailWord_7570158) baseStart_7570158 baseEnd_7570158 := by
    simpa [prefixWord, tailWord_7570158, baseEnd_7570158] using wordTrace_append hprefix tailTrace_7570158
  have hstable : (prefixWord ++ tailWord_7570158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570158).length < 2 ^ (prefixWord ++ tailWord_7570158).sum := by decide
  have hdescent : baseEnd_7570158 < baseStart_7570158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570191 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_7570191 : Nat := 118140960795 + 7570191 * 2 ^ 59
def prefixEnd_7570191 : Nat := 4983230072969 + 3 ^ 40 * 7570191 * 2
def baseEnd_7570191 : Nat := 3887146629340496326597831

theorem tailTrace_7570191 : CollatzResearch.WordTrace tailWord_7570191 prefixEnd_7570191 3887146629340496326597831 := by
  unfold tailWord_7570191
  simp only [CollatzResearch.WordTrace]
  refine ⟨276107548917498367536022427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184071699278332245024014951 276107548917498367536022427)
  ·
    refine ⟨414161323376247551304033641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276107548917498367536022427 414161323376247551304033641)
    ·
      refine ⟨310620992532185663478025231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414161323376247551304033641 310620992532185663478025231)
      ·
        refine ⟨465931488798278495217037847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310620992532185663478025231 465931488798278495217037847)
        ·
          refine ⟨698897233197417742825556771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465931488798278495217037847 698897233197417742825556771)
          ·
            refine ⟨1048345849796126614238335157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698897233197417742825556771 1048345849796126614238335157)
            ·
              refine ⟨98282423418386870084843921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1048345849796126614238335157 98282423418386870084843921)
              ·
                refine ⟨73711817563790152563632941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98282423418386870084843921 73711817563790152563632941)
                ·
                  refine ⟨27641931586421307211362353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73711817563790152563632941 27641931586421307211362353)
                  ·
                    refine ⟨20731448689815980408521765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27641931586421307211362353 20731448689815980408521765)
                    ·
                      refine ⟨3887146629340496326597831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20731448689815980408521765 3887146629340496326597831)
                      ·
                        rfl

theorem cell23_7570191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_7570191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570191 prefixEnd_7570191 := by exact prefixLift 7570191
  have htrace : WordTrace (prefixWord ++ tailWord_7570191) baseStart_7570191 baseEnd_7570191 := by
    simpa [prefixWord, tailWord_7570191, baseEnd_7570191] using wordTrace_append hprefix tailTrace_7570191
  have hstable : (prefixWord ++ tailWord_7570191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570191).length < 2 ^ (prefixWord ++ tailWord_7570191).sum := by decide
  have hdescent : baseEnd_7570191 < baseStart_7570191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570195 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 3, 2, 2]
def baseStart_7570195 : Nat := 118140960795 + 7570195 * 2 ^ 59
def prefixEnd_7570195 : Nat := 4983230072969 + 3 ^ 40 * 7570195 * 2
def baseEnd_7570195 : Nat := 3887148683263114310947813

theorem tailTrace_7570195 : CollatzResearch.WordTrace tailWord_7570195 prefixEnd_7570195 3887148683263114310947813 := by
  unfold tailWord_7570195
  simp only [CollatzResearch.WordTrace]
  refine ⟨276107694809483876219168039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184071796539655917479445359 276107694809483876219168039)
  ·
    refine ⟨414161542214225814328752059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276107694809483876219168039 414161542214225814328752059)
    ·
      refine ⟨621242313321338721493128089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414161542214225814328752059 621242313321338721493128089)
      ·
        refine ⟨465931734991004041119846067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621242313321338721493128089 465931734991004041119846067)
        ·
          refine ⟨698897602486506061679769101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465931734991004041119846067 698897602486506061679769101)
          ·
            refine ⟨262086600932439773129913413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 698897602486506061679769101 262086600932439773129913413)
            ·
              refine ⟨49141237674832457461858765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262086600932439773129913413 49141237674832457461858765)
              ·
                refine ⟨18427964128062171548197037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49141237674832457461858765 18427964128062171548197037)
                ·
                  refine ⟨6910486548023314330573889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18427964128062171548197037 6910486548023314330573889)
                  ·
                    refine ⟨5182864911017485747930417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6910486548023314330573889 5182864911017485747930417)
                    ·
                      refine ⟨3887148683263114310947813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182864911017485747930417 3887148683263114310947813)
                      ·
                        rfl

theorem cell23_7570195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 2, 2].length) (baseStart_7570195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570195 prefixEnd_7570195 := by exact prefixLift 7570195
  have htrace : WordTrace (prefixWord ++ tailWord_7570195) baseStart_7570195 baseEnd_7570195 := by
    simpa [prefixWord, tailWord_7570195, baseEnd_7570195] using wordTrace_append hprefix tailTrace_7570195
  have hstable : (prefixWord ++ tailWord_7570195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570195).length < 2 ^ (prefixWord ++ tailWord_7570195).sum := by decide
  have hdescent : baseEnd_7570195 < baseStart_7570195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570208 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7570208 : Nat := 118140960795 + 7570208 * 2 ^ 59
def prefixEnd_7570208 : Nat := 4983230072969 + 3 ^ 40 * 7570208 * 2
def baseEnd_7570208 : Nat := 3887155358511622760085253

theorem tailTrace_7570208 : CollatzResearch.WordTrace tailWord_7570208 prefixEnd_7570208 3887155358511622760085253 := by
  unfold tailWord_7570208
  simp only [CollatzResearch.WordTrace]
  refine ⟨138054084479218389719695639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184072112638957852959594185 138054084479218389719695639)
  ·
    refine ⟨207081126718827584579543459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138054084479218389719695639 207081126718827584579543459)
    ·
      refine ⟨310621690078241376869315189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207081126718827584579543459 310621690078241376869315189)
      ·
        refine ⟨29120783444835129081498299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310621690078241376869315189 29120783444835129081498299)
        ·
          refine ⟨43681175167252693622247449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29120783444835129081498299 43681175167252693622247449)
          ·
            refine ⟨32760881375439520216685587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43681175167252693622247449 32760881375439520216685587)
            ·
              refine ⟨49141322063159280325028381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32760881375439520216685587 49141322063159280325028381)
              ·
                refine ⟨18427995773684730121885643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49141322063159280325028381 18427995773684730121885643)
                ·
                  refine ⟨27641993660527095182828465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18427995773684730121885643 27641993660527095182828465)
                  ·
                    refine ⟨20731495245395321387121349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27641993660527095182828465 20731495245395321387121349)
                    ·
                      refine ⟨3887155358511622760085253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20731495245395321387121349 3887155358511622760085253)
                      ·
                        rfl

theorem cell23_7570208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7570208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570208 prefixEnd_7570208 := by exact prefixLift 7570208
  have htrace : WordTrace (prefixWord ++ tailWord_7570208) baseStart_7570208 baseEnd_7570208 := by
    simpa [prefixWord, tailWord_7570208, baseEnd_7570208] using wordTrace_append hprefix tailTrace_7570208
  have hstable : (prefixWord ++ tailWord_7570208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570208).length < 2 ^ (prefixWord ++ tailWord_7570208).sum := by decide
  have hdescent : baseEnd_7570208 < baseStart_7570208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570229 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_7570229 : Nat := 118140960795 + 7570229 * 2 ^ 59
def prefixEnd_7570229 : Nat := 4983230072969 + 3 ^ 40 * 7570229 * 2
def baseEnd_7570229 : Nat := 3887166141605367177922657

theorem tailTrace_7570229 : CollatzResearch.WordTrace tailWord_7570229 prefixEnd_7570229 3887166141605367177922657 := by
  unfold tailWord_7570229
  simp only [CollatzResearch.WordTrace]
  refine ⟨276108934891360700025905741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184072623260907133350603827 276108934891360700025905741)
  ·
    refine ⟨103540850584260262509714653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276108934891360700025905741 103540850584260262509714653)
    ·
      refine ⟨38827818969097598441142995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103540850584260262509714653 38827818969097598441142995)
      ·
        refine ⟨58241728453646397661714493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38827818969097598441142995 58241728453646397661714493)
        ·
          refine ⟨21840648170117399123142935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58241728453646397661714493 21840648170117399123142935)
          ·
            refine ⟨32760972255176098684714403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21840648170117399123142935 32760972255176098684714403)
            ·
              refine ⟨49141458382764148027071605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32760972255176098684714403 49141458382764148027071605)
              ·
                refine ⟨4607011723384138877537963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49141458382764148027071605 4607011723384138877537963)
                ·
                  refine ⟨6910517585076208316306945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607011723384138877537963 6910517585076208316306945)
                  ·
                    refine ⟨5182888188807156237230209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6910517585076208316306945 5182888188807156237230209)
                    ·
                      refine ⟨3887166141605367177922657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182888188807156237230209 3887166141605367177922657)
                      ·
                        rfl

theorem cell23_7570229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_7570229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570229 prefixEnd_7570229 := by exact prefixLift 7570229
  have htrace : WordTrace (prefixWord ++ tailWord_7570229) baseStart_7570229 baseEnd_7570229 := by
    simpa [prefixWord, tailWord_7570229, baseEnd_7570229] using wordTrace_append hprefix tailTrace_7570229
  have hstable : (prefixWord ++ tailWord_7570229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570229).length < 2 ^ (prefixWord ++ tailWord_7570229).sum := by decide
  have hdescent : baseEnd_7570229 < baseStart_7570229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570245 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_7570245 : Nat := 118140960795 + 7570245 * 2 ^ 59
def prefixEnd_7570245 : Nat := 4983230072969 + 3 ^ 40 * 7570245 * 2
def baseEnd_7570245 : Nat := 3887174357295839115322583

theorem tailTrace_7570245 : CollatzResearch.WordTrace tailWord_7570245 prefixEnd_7570245 3887174357295839115322583 := by
  unfold tailWord_7570245
  simp only [CollatzResearch.WordTrace]
  refine ⟨276109518459302734758488189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184073012306201823172325459 276109518459302734758488189)
  ·
    refine ⟨103541069422238525534433071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276109518459302734758488189 103541069422238525534433071)
    ·
      refine ⟨155311604133357788301649607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103541069422238525534433071 155311604133357788301649607)
      ·
        refine ⟨232967406200036682452474411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155311604133357788301649607 232967406200036682452474411)
        ·
          refine ⟨349451109300055023678711617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232967406200036682452474411 349451109300055023678711617)
          ·
            refine ⟨262088331975041267759033713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349451109300055023678711617 262088331975041267759033713)
            ·
              refine ⟨196566248981280950819275285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262088331975041267759033713 196566248981280950819275285)
              ·
                refine ⟨9214042920997544569653529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196566248981280950819275285 9214042920997544569653529)
                ·
                  refine ⟨6910532190748158427240147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9214042920997544569653529 6910532190748158427240147)
                  ·
                    refine ⟨10365798286122237640860221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910532190748158427240147 10365798286122237640860221)
                    ·
                      refine ⟨3887174357295839115322583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10365798286122237640860221 3887174357295839115322583)
                      ·
                        rfl

theorem cell23_7570245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_7570245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570245 prefixEnd_7570245 := by exact prefixLift 7570245
  have htrace : WordTrace (prefixWord ++ tailWord_7570245) baseStart_7570245 baseEnd_7570245 := by
    simpa [prefixWord, tailWord_7570245, baseEnd_7570245] using wordTrace_append hprefix tailTrace_7570245
  have hstable : (prefixWord ++ tailWord_7570245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570245).length < 2 ^ (prefixWord ++ tailWord_7570245).sum := by decide
  have hdescent : baseEnd_7570245 < baseStart_7570245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570272 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 1, 3, 2]
def baseStart_7570272 : Nat := 118140960795 + 7570272 * 2 ^ 59
def prefixEnd_7570272 : Nat := 4983230072969 + 3 ^ 40 * 7570272 * 2
def baseEnd_7570272 : Nat := 3887188221273510509684959

theorem tailTrace_7570272 : CollatzResearch.WordTrace tailWord_7570272 prefixEnd_7570272 3887188221273510509684959 := by
  unfold tailWord_7570272
  simp only [CollatzResearch.WordTrace]
  refine ⟨138055251615102459184860535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184073668820136612246480713 138055251615102459184860535)
  ·
    refine ⟨207082877422653688777290803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138055251615102459184860535 207082877422653688777290803)
    ·
      refine ⟨310624316133980533165936205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207082877422653688777290803 310624316133980533165936205)
      ·
        refine ⟨116484118550242699937226077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310624316133980533165936205 116484118550242699937226077)
        ·
          refine ⟨43681544456341012476459779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116484118550242699937226077 43681544456341012476459779)
          ·
            refine ⟨65522316684511518714689669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43681544456341012476459779 65522316684511518714689669)
            ·
              refine ⟨12285434378345909759004313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65522316684511518714689669 12285434378345909759004313)
              ·
                refine ⟨9214075783759432319253235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12285434378345909759004313 9214075783759432319253235)
                ·
                  refine ⟨13821113675639148478879853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9214075783759432319253235 13821113675639148478879853)
                  ·
                    refine ⟨5182917628364680679579945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13821113675639148478879853 5182917628364680679579945)
                    ·
                      refine ⟨3887188221273510509684959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182917628364680679579945 3887188221273510509684959)
                      ·
                        rfl

theorem cell23_7570272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_7570272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570272 prefixEnd_7570272 := by exact prefixLift 7570272
  have htrace : WordTrace (prefixWord ++ tailWord_7570272) baseStart_7570272 baseEnd_7570272 := by
    simpa [prefixWord, tailWord_7570272, baseEnd_7570272] using wordTrace_append hprefix tailTrace_7570272
  have hstable : (prefixWord ++ tailWord_7570272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570272).length < 2 ^ (prefixWord ++ tailWord_7570272).sum := by decide
  have hdescent : baseEnd_7570272 < baseStart_7570272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570285 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_7570285 : Nat := 118140960795 + 7570285 * 2 ^ 59
def prefixEnd_7570285 : Nat := 4983230072969 + 3 ^ 40 * 7570285 * 2
def baseEnd_7570285 : Nat := 3887194896522018958822399

theorem tailTrace_7570285 : CollatzResearch.WordTrace tailWord_7570285 prefixEnd_7570285 3887194896522018958822399 := by
  unfold tailWord_7570285
  simp only [CollatzResearch.WordTrace]
  refine ⟨276110977379157821589944309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184073984919438547726629539 276110977379157821589944309)
  ·
    refine ⟨25885404129296045774057279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276110977379157821589944309 25885404129296045774057279)
    ·
      refine ⟨38828106193944068661085919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25885404129296045774057279 38828106193944068661085919)
      ·
        refine ⟨58242159290916102991628879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38828106193944068661085919 58242159290916102991628879)
        ·
          refine ⟨87363238936374154487443319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58242159290916102991628879 87363238936374154487443319)
          ·
            refine ⟨131044858404561231731164979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87363238936374154487443319 131044858404561231731164979)
            ·
              refine ⟨196567287606841847596747469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131044858404561231731164979 196567287606841847596747469)
              ·
                refine ⟨73712732852565692848780301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196567287606841847596747469 73712732852565692848780301)
                ·
                  refine ⟨27642274819712134818292613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73712732852565692848780301 27642274819712134818292613)
                  ·
                    refine ⟨5182926528696025278429865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27642274819712134818292613 5182926528696025278429865)
                    ·
                      refine ⟨3887194896522018958822399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182926528696025278429865 3887194896522018958822399)
                      ·
                        rfl

theorem cell23_7570285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_7570285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570285 prefixEnd_7570285 := by exact prefixLift 7570285
  have htrace : WordTrace (prefixWord ++ tailWord_7570285) baseStart_7570285 baseEnd_7570285 := by
    simpa [prefixWord, tailWord_7570285, baseEnd_7570285] using wordTrace_append hprefix tailTrace_7570285
  have hstable : (prefixWord ++ tailWord_7570285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570285).length < 2 ^ (prefixWord ++ tailWord_7570285).sum := by decide
  have hdescent : baseEnd_7570285 < baseStart_7570285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570291 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 9]
def baseStart_7570291 : Nat := 118140960795 + 7570291 * 2 ^ 59
def prefixEnd_7570291 : Nat := 4983230072969 + 3 ^ 40 * 7570291 * 2
def baseEnd_7570291 : Nat := 431910886378438437260819

theorem tailTrace_7570291 : CollatzResearch.WordTrace tailWord_7570291 prefixEnd_7570291 431910886378438437260819 := by
  unfold tailWord_7570291
  simp only [CollatzResearch.WordTrace]
  refine ⟨276111196217136084614662727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184074130811424056409775151 276111196217136084614662727)
  ·
    refine ⟨414166794325704126921994091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276111196217136084614662727 414166794325704126921994091)
    ·
      refine ⟨621250191488556190382991137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414166794325704126921994091 621250191488556190382991137)
      ·
        refine ⟨465937643616417142787243353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621250191488556190382991137 465937643616417142787243353)
        ·
          refine ⟨349453232712312857090432515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465937643616417142787243353 349453232712312857090432515)
          ·
            refine ⟨524179849068469285635648773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349453232712312857090432515 524179849068469285635648773)
            ·
              refine ⟨98283721700337991056684145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 524179849068469285635648773 98283721700337991056684145)
              ·
                refine ⟨73712791275253493292513109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98283721700337991056684145 73712791275253493292513109)
                ·
                  refine ⟨431910886378438437260819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73712791275253493292513109 431910886378438437260819)
                  ·
                    rfl

theorem cell23_7570291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 9].length) (baseStart_7570291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570291 prefixEnd_7570291 := by exact prefixLift 7570291
  have htrace : WordTrace (prefixWord ++ tailWord_7570291) baseStart_7570291 baseEnd_7570291 := by
    simpa [prefixWord, tailWord_7570291, baseEnd_7570291] using wordTrace_append hprefix tailTrace_7570291
  have hstable : (prefixWord ++ tailWord_7570291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570291).length < 2 ^ (prefixWord ++ tailWord_7570291).sum := by decide
  have hdescent : baseEnd_7570291 < baseStart_7570291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570375 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_7570375 : Nat := 118140960795 + 7570375 * 2 ^ 59
def prefixEnd_7570375 : Nat := 4983230072969 + 3 ^ 40 * 7570375 * 2
def baseEnd_7570375 : Nat := 3887241109780923606696985

theorem tailTrace_7570375 : CollatzResearch.WordTrace tailWord_7570375 prefixEnd_7570375 3887241109780923606696985 := by
  unfold tailWord_7570375
  simp only [CollatzResearch.WordTrace]
  refine ⟨276114259948831766960720579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184076173299221177973813719 276114259948831766960720579)
  ·
    refine ⟨414171389923247650441080869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276114259948831766960720579 414171389923247650441080869)
    ·
      refine ⟨77657135610608934457702663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414171389923247650441080869 77657135610608934457702663)
      ·
        refine ⟨116485703415913401686553995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77657135610608934457702663 116485703415913401686553995)
        ·
          refine ⟨174728555123870102529830993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116485703415913401686553995 174728555123870102529830993)
          ·
            refine ⟨131046416342902576897373245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174728555123870102529830993 131046416342902576897373245)
            ·
              refine ⟨49142406128588466336514967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131046416342902576897373245 49142406128588466336514967)
              ·
                refine ⟨73713609192882699504772451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49142406128588466336514967 73713609192882699504772451)
                ·
                  refine ⟨110570413789324049257158677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73713609192882699504772451 110570413789324049257158677)
                  ·
                    refine ⟨5182988146374564808929313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110570413789324049257158677 5182988146374564808929313)
                    ·
                      refine ⟨3887241109780923606696985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5182988146374564808929313 3887241109780923606696985)
                      ·
                        rfl

theorem cell23_7570375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_7570375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570375 prefixEnd_7570375 := by exact prefixLift 7570375
  have htrace : WordTrace (prefixWord ++ tailWord_7570375) baseStart_7570375 baseEnd_7570375 := by
    simpa [prefixWord, tailWord_7570375, baseEnd_7570375] using wordTrace_append hprefix tailTrace_7570375
  have hstable : (prefixWord ++ tailWord_7570375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570375).length < 2 ^ (prefixWord ++ tailWord_7570375).sum := by decide
  have hdescent : baseEnd_7570375 < baseStart_7570375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570385 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 3, 4]
def baseStart_7570385 : Nat := 118140960795 + 7570385 * 2 ^ 59
def prefixEnd_7570385 : Nat := 4983230072969 + 3 ^ 40 * 7570385 * 2
def baseEnd_7570385 : Nat := 1295748748195822855857313

theorem tailTrace_7570385 : CollatzResearch.WordTrace tailWord_7570385 prefixEnd_7570385 1295748748195822855857313 := by
  unfold tailWord_7570385
  simp only [CollatzResearch.WordTrace]
  refine ⟨276114624678795538668584609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184076416452530359112389739 276114624678795538668584609)
  ·
    refine ⟨207085968509096654001438457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276114624678795538668584609 207085968509096654001438457)
    ·
      refine ⟨155314476381822490501078843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207085968509096654001438457 155314476381822490501078843)
      ·
        refine ⟨232971714572733735751618265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155314476381822490501078843 232971714572733735751618265)
        ·
          refine ⟨174728785929550301813713699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232971714572733735751618265 174728785929550301813713699)
          ·
            refine ⟨262093178894325452720570549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174728785929550301813713699 262093178894325452720570549)
            ·
              refine ⟨24571235521343011192553489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262093178894325452720570549 24571235521343011192553489)
              ·
                refine ⟨18428426641007258394415117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24571235521343011192553489 18428426641007258394415117)
                ·
                  refine ⟨6910659990377721897905669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18428426641007258394415117 6910659990377721897905669)
                  ·
                    refine ⟨1295748748195822855857313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6910659990377721897905669 1295748748195822855857313)
                    ·
                      rfl

theorem cell23_7570385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_7570385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570385 prefixEnd_7570385 := by exact prefixLift 7570385
  have htrace : WordTrace (prefixWord ++ tailWord_7570385) baseStart_7570385 baseEnd_7570385 := by
    simpa [prefixWord, tailWord_7570385, baseEnd_7570385] using wordTrace_append hprefix tailTrace_7570385
  have hstable : (prefixWord ++ tailWord_7570385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570385).length < 2 ^ (prefixWord ++ tailWord_7570385).sum := by decide
  have hdescent : baseEnd_7570385 < baseStart_7570385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570389 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_7570389 : Nat := 118140960795 + 7570389 * 2 ^ 59
def prefixEnd_7570389 : Nat := 4983230072969 + 3 ^ 40 * 7570389 * 2
def baseEnd_7570389 : Nat := 1295749432836695517307307

theorem tailTrace_7570389 : CollatzResearch.WordTrace tailWord_7570389 prefixEnd_7570389 1295749432836695517307307 := by
  unfold tailWord_7570389
  simp only [CollatzResearch.WordTrace]
  refine ⟨276114770570781047351730221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184076513713854031567820147 276114770570781047351730221)
  ·
    refine ⟨103543038964042892756898833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276114770570781047351730221 103543038964042892756898833)
    ·
      refine ⟨77657279223032169567674125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103543038964042892756898833 77657279223032169567674125)
      ·
        refine ⟨29121479708637063587877797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77657279223032169567674125 29121479708637063587877797)
        ·
          refine ⟨5460277445369449422727087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29121479708637063587877797 5460277445369449422727087)
          ·
            refine ⟨8190416168054174134090631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460277445369449422727087 8190416168054174134090631)
            ·
              refine ⟨12285624252081261201135947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190416168054174134090631 12285624252081261201135947)
              ·
                refine ⟨18428436378121891801703921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12285624252081261201135947 18428436378121891801703921)
                ·
                  refine ⟨13821327283591418851277941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18428436378121891801703921 13821327283591418851277941)
                  ·
                    refine ⟨1295749432836695517307307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13821327283591418851277941 1295749432836695517307307)
                    ·
                      rfl

theorem cell23_7570389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_7570389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570389 prefixEnd_7570389 := by exact prefixLift 7570389
  have htrace : WordTrace (prefixWord ++ tailWord_7570389) baseStart_7570389 baseEnd_7570389 := by
    simpa [prefixWord, tailWord_7570389, baseEnd_7570389] using wordTrace_append hprefix tailTrace_7570389
  have hstable : (prefixWord ++ tailWord_7570389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570389).length < 2 ^ (prefixWord ++ tailWord_7570389).sum := by decide
  have hdescent : baseEnd_7570389 < baseStart_7570389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570392 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_7570392 : Nat := 118140960795 + 7570392 * 2 ^ 59
def prefixEnd_7570392 : Nat := 4983230072969 + 3 ^ 40 * 7570392 * 2
def baseEnd_7570392 : Nat := 3887249838952050040184407

theorem tailTrace_7570392 : CollatzResearch.WordTrace tailWord_7570392 prefixEnd_7570392 3887249838952050040184407 := by
  unfold tailWord_7570392
  simp only [CollatzResearch.WordTrace]
  refine ⟨138057439994885089432044715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184076586659846785909392953 138057439994885089432044715)
  ·
    refine ⟨207086159992327634148067073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138057439994885089432044715 207086159992327634148067073)
    ·
      refine ⟨155314619994245725611050305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207086159992327634148067073 155314619994245725611050305)
      ·
        refine ⟨116485964995684294208287729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155314619994245725611050305 116485964995684294208287729)
        ·
          refine ⟨87364473746763220656215797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116485964995684294208287729 87364473746763220656215797)
          ·
            refine ⟨8190419413759051936520231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87364473746763220656215797 8190419413759051936520231)
            ·
              refine ⟨12285629120638577904780347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190419413759051936520231 12285629120638577904780347)
              ·
                refine ⟨18428443680957866857170521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12285629120638577904780347 18428443680957866857170521)
                ·
                  refine ⟨13821332760718400142877891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18428443680957866857170521 13821332760718400142877891)
                  ·
                    refine ⟨20731999141077600214316837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13821332760718400142877891 20731999141077600214316837)
                    ·
                      refine ⟨3887249838952050040184407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20731999141077600214316837 3887249838952050040184407)
                      ·
                        rfl

theorem cell23_7570392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_7570392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570392 prefixEnd_7570392 := by exact prefixLift 7570392
  have htrace : WordTrace (prefixWord ++ tailWord_7570392) baseStart_7570392 baseEnd_7570392 := by
    simpa [prefixWord, tailWord_7570392, baseEnd_7570392] using wordTrace_append hprefix tailTrace_7570392
  have hstable : (prefixWord ++ tailWord_7570392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570392).length < 2 ^ (prefixWord ++ tailWord_7570392).sum := by decide
  have hdescent : baseEnd_7570392 < baseStart_7570392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570415 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 6]
def baseStart_7570415 : Nat := 118140960795 + 7570415 * 2 ^ 59
def prefixEnd_7570415 : Nat := 4983230072969 + 3 ^ 40 * 7570415 * 2
def baseEnd_7570415 : Nat := 431917961000789272244089

theorem tailTrace_7570415 : CollatzResearch.WordTrace tailWord_7570415 prefixEnd_7570415 431917961000789272244089 := by
  unfold tailWord_7570415
  simp only [CollatzResearch.WordTrace]
  refine ⟨276115718868686853792176699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184077145912457902528117799 276115718868686853792176699)
  ·
    refine ⟨414173578303030280688265049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276115718868686853792176699 414173578303030280688265049)
    ·
      refine ⟨310630183727272710516198787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414173578303030280688265049 310630183727272710516198787)
      ·
        refine ⟨465945275590909065774298181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310630183727272710516198787 465945275590909065774298181)
        ·
          refine ⟨87364739173295449832680909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465945275590909065774298181 87364739173295449832680909)
          ·
            refine ⟨32761777189985793687255341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87364739173295449832680909 32761777189985793687255341)
            ·
              refine ⟨12285666446244672632720753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32761777189985793687255341 12285666446244672632720753)
              ·
                refine ⟨9214249834683504474540565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12285666446244672632720753 9214249834683504474540565)
                ·
                  refine ⟨431917961000789272244089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9214249834683504474540565 431917961000789272244089)
                  ·
                    rfl

theorem cell23_7570415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 6].length) (baseStart_7570415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570415 prefixEnd_7570415 := by exact prefixLift 7570415
  have htrace : WordTrace (prefixWord ++ tailWord_7570415) baseStart_7570415 baseEnd_7570415 := by
    simpa [prefixWord, tailWord_7570415, baseEnd_7570415] using wordTrace_append hprefix tailTrace_7570415
  have hstable : (prefixWord ++ tailWord_7570415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570415).length < 2 ^ (prefixWord ++ tailWord_7570415).sum := by decide
  have hdescent : baseEnd_7570415 < baseStart_7570415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570475 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 4, 4]
def baseStart_7570475 : Nat := 118140960795 + 7570475 * 2 ^ 59
def prefixEnd_7570475 : Nat := 4983230072969 + 3 ^ 40 * 7570475 * 2
def baseEnd_7570475 : Nat := 1295764152615457738482175

theorem tailTrace_7570475 : CollatzResearch.WordTrace tailWord_7570475 prefixEnd_7570475 1295764152615457738482175 := by
  unfold tailWord_7570475
  simp only [CollatzResearch.WordTrace]
  refine ⟨276117907248469484039360879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184078604832312989359573919 276117907248469484039360879)
  ·
    refine ⟨414176860872704226059041319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276117907248469484039360879 414176860872704226059041319)
    ·
      refine ⟨621265291309056339088561979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414176860872704226059041319 621265291309056339088561979)
      ·
        refine ⟨931897936963584508632842969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621265291309056339088561979 931897936963584508632842969)
        ·
          refine ⟨698923452722688381474632227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931897936963584508632842969 698923452722688381474632227)
          ·
            refine ⟨1048385179084032572211948341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698923452722688381474632227 1048385179084032572211948341)
            ·
              refine ⟨98286110539128053644870157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1048385179084032572211948341 98286110539128053644870157)
              ·
                refine ⟨36857291452173020116826309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98286110539128053644870157 36857291452173020116826309)
                ·
                  refine ⟨6910742147282441271904933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36857291452173020116826309 6910742147282441271904933)
                  ·
                    refine ⟨1295764152615457738482175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6910742147282441271904933 1295764152615457738482175)
                    ·
                      rfl

theorem cell23_7570475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 4].length) (baseStart_7570475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570475 prefixEnd_7570475 := by exact prefixLift 7570475
  have htrace : WordTrace (prefixWord ++ tailWord_7570475) baseStart_7570475 baseEnd_7570475 := by
    simpa [prefixWord, tailWord_7570475, baseEnd_7570475] using wordTrace_append hprefix tailTrace_7570475
  have hstable : (prefixWord ++ tailWord_7570475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570475).length < 2 ^ (prefixWord ++ tailWord_7570475).sum := by decide
  have hdescent : baseEnd_7570475 < baseStart_7570475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570476 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 1, 1, 3]
def baseStart_7570476 : Nat := 118140960795 + 7570476 * 2 ^ 59
def prefixEnd_7570476 : Nat := 4983230072969 + 3 ^ 40 * 7570476 * 2
def baseEnd_7570476 : Nat := 3887292971327027711534021

theorem tailTrace_7570476 : CollatzResearch.WordTrace tailWord_7570476 prefixEnd_7570476 3887292971327027711534021 := by
  unfold tailWord_7570476
  simp only [CollatzResearch.WordTrace]
  refine ⟨138058971860732930605073641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184078629147643907473431521 138058971860732930605073641)
  ·
    refine ⟨103544228895549697953805231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138058971860732930605073641 103544228895549697953805231)
    ·
      refine ⟨155316343343324546930707847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103544228895549697953805231 155316343343324546930707847)
      ·
        refine ⟨232974515014986820396061771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155316343343324546930707847 232974515014986820396061771)
        ·
          refine ⟨349461772522480230594092657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232974515014986820396061771 349461772522480230594092657)
          ·
            refine ⟨262096329391860172945569493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349461772522480230594092657 262096329391860172945569493)
            ·
              refine ⟨6142882720121722803411785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 262096329391860172945569493 6142882720121722803411785)
              ·
                refine ⟨4607162040091292102558839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6142882720121722803411785 4607162040091292102558839)
                ·
                  refine ⟨6910743060136938153838259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607162040091292102558839 6910743060136938153838259)
                  ·
                    refine ⟨10366114590205407230757389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910743060136938153838259 10366114590205407230757389)
                    ·
                      refine ⟨3887292971327027711534021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366114590205407230757389 3887292971327027711534021)
                      ·
                        rfl

theorem cell23_7570476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_7570476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570476 prefixEnd_7570476 := by exact prefixLift 7570476
  have htrace : WordTrace (prefixWord ++ tailWord_7570476) baseStart_7570476 baseEnd_7570476 := by
    simpa [prefixWord, tailWord_7570476, baseEnd_7570476] using wordTrace_append hprefix tailTrace_7570476
  have hstable : (prefixWord ++ tailWord_7570476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570476).length < 2 ^ (prefixWord ++ tailWord_7570476).sum := by decide
  have hdescent : baseEnd_7570476 < baseStart_7570476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570485 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_7570485 : Nat := 118140960795 + 7570485 * 2 ^ 59
def prefixEnd_7570485 : Nat := 4983230072969 + 3 ^ 40 * 7570485 * 2
def baseEnd_7570485 : Nat := 3887297592652918176321479

theorem tailTrace_7570485 : CollatzResearch.WordTrace tailWord_7570485 prefixEnd_7570485 3887297592652918176321479 := by
  unfold tailWord_7570485
  simp only [CollatzResearch.WordTrace]
  refine ⟨276118271978433255747224909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184078847985622170498149939 276118271978433255747224909)
  ·
    refine ⟨103544351991912470905209341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276118271978433255747224909 103544351991912470905209341)
    ·
      refine ⟨38829131996967176589453503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103544351991912470905209341 38829131996967176589453503)
      ·
        refine ⟨58243697995450764884180255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38829131996967176589453503 58243697995450764884180255)
        ·
          refine ⟨87365546993176147326270383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58243697995450764884180255 87365546993176147326270383)
          ·
            refine ⟨131048320489764220989405575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87365546993176147326270383 131048320489764220989405575)
            ·
              refine ⟨196572480734646331484108363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131048320489764220989405575 196572480734646331484108363)
              ·
                refine ⟨294858721101969497226162545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196572480734646331484108363 294858721101969497226162545)
                ·
                  refine ⟨221144040826477122919621909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294858721101969497226162545 221144040826477122919621909)
                  ·
                    refine ⟨10366126913741115136857277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221144040826477122919621909 10366126913741115136857277)
                    ·
                      refine ⟨3887297592652918176321479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366126913741115136857277 3887297592652918176321479)
                      ·
                        rfl

theorem cell23_7570485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_7570485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570485 prefixEnd_7570485 := by exact prefixLift 7570485
  have htrace : WordTrace (prefixWord ++ tailWord_7570485) baseStart_7570485 baseEnd_7570485 := by
    simpa [prefixWord, tailWord_7570485, baseEnd_7570485] using wordTrace_append hprefix tailTrace_7570485
  have hstable : (prefixWord ++ tailWord_7570485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570485).length < 2 ^ (prefixWord ++ tailWord_7570485).sum := by decide
  have hdescent : baseEnd_7570485 < baseStart_7570485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570495 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_7570495 : Nat := 118140960795 + 7570495 * 2 ^ 59
def prefixEnd_7570495 : Nat := 4983230072969 + 3 ^ 40 * 7570495 * 2
def baseEnd_7570495 : Nat := 3887302727459463137196433

theorem tailTrace_7570495 : CollatzResearch.WordTrace tailWord_7570495 prefixEnd_7570495 3887302727459463137196433 := by
  unfold tailWord_7570495
  simp only [CollatzResearch.WordTrace]
  refine ⟨276118636708397027455088939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184079091138931351636725959 276118636708397027455088939)
  ·
    refine ⟨414177955062595541182633409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276118636708397027455088939 414177955062595541182633409)
    ·
      refine ⟨310633466296946655886975057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414177955062595541182633409 310633466296946655886975057)
      ·
        refine ⟨232975099722709991915231293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310633466296946655886975057 232975099722709991915231293)
        ·
          refine ⟨87365662396016246968211735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232975099722709991915231293 87365662396016246968211735)
          ·
            refine ⟨131048493594024370452317603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87365662396016246968211735 131048493594024370452317603)
            ·
              refine ⟨196572740391036555678476405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131048493594024370452317603 196572740391036555678476405)
              ·
                refine ⟨18428694411659677094857163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196572740391036555678476405 18428694411659677094857163)
                ·
                  refine ⟨27643041617489515642285745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18428694411659677094857163 27643041617489515642285745)
                  ·
                    refine ⟨20732281213117136731714309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27643041617489515642285745 20732281213117136731714309)
                    ·
                      refine ⟨3887302727459463137196433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20732281213117136731714309 3887302727459463137196433)
                      ·
                        rfl

theorem cell23_7570495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_7570495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570495 prefixEnd_7570495 := by exact prefixLift 7570495
  have htrace : WordTrace (prefixWord ++ tailWord_7570495) baseStart_7570495 baseEnd_7570495 := by
    simpa [prefixWord, tailWord_7570495, baseEnd_7570495] using wordTrace_append hprefix tailTrace_7570495
  have hstable : (prefixWord ++ tailWord_7570495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570495).length < 2 ^ (prefixWord ++ tailWord_7570495).sum := by decide
  have hdescent : baseEnd_7570495 < baseStart_7570495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570515 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 3]
def baseStart_7570515 : Nat := 118140960795 + 7570515 * 2 ^ 59
def prefixEnd_7570515 : Nat := 4983230072969 + 3 ^ 40 * 7570515 * 2
def baseEnd_7570515 : Nat := 3887312997072553058946341

theorem tailTrace_7570515 : CollatzResearch.WordTrace tailWord_7570515 prefixEnd_7570515 3887312997072553058946341 := by
  unfold tailWord_7570515
  simp only [CollatzResearch.WordTrace]
  refine ⟨276119366168324570870816999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184079577445549713913877999 276119366168324570870816999)
  ·
    refine ⟨414179049252486856306225499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276119366168324570870816999 414179049252486856306225499)
    ·
      refine ⟨621268573878730284459338249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414179049252486856306225499 621268573878730284459338249)
      ·
        refine ⟨465951430409047713344503687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621268573878730284459338249 465951430409047713344503687)
        ·
          refine ⟨698927145613571570016755531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465951430409047713344503687 698927145613571570016755531)
          ·
            refine ⟨1048390718420357355025133297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698927145613571570016755531 1048390718420357355025133297)
            ·
              refine ⟨786293038815268016268849973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048390718420357355025133297 786293038815268016268849973)
              ·
                refine ⟨73714972388931376525204685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 786293038815268016268849973 73714972388931376525204685)
                ·
                  refine ⟨27643114645849266196951757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73714972388931376525204685 27643114645849266196951757)
                  ·
                    refine ⟨10366167992193474823856909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27643114645849266196951757 10366167992193474823856909)
                    ·
                      refine ⟨3887312997072553058946341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366167992193474823856909 3887312997072553058946341)
                      ·
                        rfl

theorem cell23_7570515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_7570515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570515 prefixEnd_7570515 := by exact prefixLift 7570515
  have htrace : WordTrace (prefixWord ++ tailWord_7570515) baseStart_7570515 baseEnd_7570515 := by
    simpa [prefixWord, tailWord_7570515, baseEnd_7570515] using wordTrace_append hprefix tailTrace_7570515
  have hstable : (prefixWord ++ tailWord_7570515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570515).length < 2 ^ (prefixWord ++ tailWord_7570515).sum := by decide
  have hdescent : baseEnd_7570515 < baseStart_7570515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570535 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 2, 7]
def baseStart_7570535 : Nat := 118140960795 + 7570535 * 2 ^ 59
def prefixEnd_7570535 : Nat := 4983230072969 + 3 ^ 40 * 7570535 * 2
def baseEnd_7570535 : Nat := 1295774422228547660232083

theorem tailTrace_7570535 : CollatzResearch.WordTrace tailWord_7570535 prefixEnd_7570535 1295774422228547660232083 := by
  unfold tailWord_7570535
  simp only [CollatzResearch.WordTrace]
  refine ⟨276120095628252114286545059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184080063752168076191030039 276120095628252114286545059)
  ·
    refine ⟨414180143442378171429817589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276120095628252114286545059 414180143442378171429817589)
    ·
      refine ⟨38829388447722953571545399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 414180143442378171429817589 38829388447722953571545399)
      ·
        refine ⟨58244082671584430357318099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38829388447722953571545399 58244082671584430357318099)
        ·
          refine ⟨87366124007376645535977149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58244082671584430357318099 87366124007376645535977149)
          ·
            refine ⟨32762296502766242075991431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87366124007376645535977149 32762296502766242075991431)
            ·
              refine ⟨49143444754149363113987147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32762296502766242075991431 49143444754149363113987147)
              ·
                refine ⟨73715167131224044670980721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49143444754149363113987147 73715167131224044670980721)
                ·
                  refine ⟨55286375348418033503235541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73715167131224044670980721 55286375348418033503235541)
                  ·
                    refine ⟨1295774422228547660232083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55286375348418033503235541 1295774422228547660232083)
                    ·
                      rfl

theorem cell23_7570535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_7570535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570535 prefixEnd_7570535 := by exact prefixLift 7570535
  have htrace : WordTrace (prefixWord ++ tailWord_7570535) baseStart_7570535 baseEnd_7570535 := by
    simpa [prefixWord, tailWord_7570535, baseEnd_7570535] using wordTrace_append hprefix tailTrace_7570535
  have hstable : (prefixWord ++ tailWord_7570535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570535).length < 2 ^ (prefixWord ++ tailWord_7570535).sum := by decide
  have hdescent : baseEnd_7570535 < baseStart_7570535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570699 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 3]
def baseStart_7570699 : Nat := 118140960795 + 7570699 * 2 ^ 59
def prefixEnd_7570699 : Nat := 4983230072969 + 3 ^ 40 * 7570699 * 2
def baseEnd_7570699 : Nat := 3887407477512980339045495

theorem tailTrace_7570699 : CollatzResearch.WordTrace tailWord_7570699 prefixEnd_7570699 3887407477512980339045495 := by
  unfold tailWord_7570699
  simp only [CollatzResearch.WordTrace]
  refine ⟨276126077199657970295515151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184084051466438646863676767 276126077199657970295515151)
  ·
    refine ⟨414189115799486955443272727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276126077199657970295515151 414189115799486955443272727)
    ·
      refine ⟨621283673699230433164909091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414189115799486955443272727 621283673699230433164909091)
      ·
        refine ⟨931925510548845649747363637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621283673699230433164909091 931925510548845649747363637)
        ·
          refine ⟨87368016613954279663815341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 931925510548845649747363637 87368016613954279663815341)
          ·
            refine ⟨32763006230232854873930753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87368016613954279663815341 32763006230232854873930753)
            ·
              refine ⟨24572254672674641155448065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32763006230232854873930753 24572254672674641155448065)
              ·
                refine ⟨18429191004505980866586049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24572254672674641155448065 18429191004505980866586049)
                ·
                  refine ⟨13821893253379485649939537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18429191004505980866586049 13821893253379485649939537)
                  ·
                    refine ⟨10366419940034614237454653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13821893253379485649939537 10366419940034614237454653)
                    ·
                      refine ⟨3887407477512980339045495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366419940034614237454653 3887407477512980339045495)
                      ·
                        rfl

theorem cell23_7570699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 3].length) (baseStart_7570699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570699 prefixEnd_7570699 := by exact prefixLift 7570699
  have htrace : WordTrace (prefixWord ++ tailWord_7570699) baseStart_7570699 baseEnd_7570699 := by
    simpa [prefixWord, tailWord_7570699, baseEnd_7570699] using wordTrace_append hprefix tailTrace_7570699
  have hstable : (prefixWord ++ tailWord_7570699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570699).length < 2 ^ (prefixWord ++ tailWord_7570699).sum := by decide
  have hdescent : baseEnd_7570699 < baseStart_7570699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570733 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7570733 : Nat := 118140960795 + 7570733 * 2 ^ 59
def prefixEnd_7570733 : Nat := 4983230072969 + 3 ^ 40 * 7570733 * 2
def baseEnd_7570733 : Nat := 3887424935855233206020339

theorem tailTrace_7570733 : CollatzResearch.WordTrace tailWord_7570733 prefixEnd_7570733 3887424935855233206020339 := by
  unfold tailWord_7570733
  simp only [CollatzResearch.WordTrace]
  refine ⟨276127317281534794102252853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184084878187689862734835235 276127317281534794102252853)
  ·
    refine ⟨25886935995143886947086205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276127317281534794102252853 25886935995143886947086205)
    ·
      refine ⟨9707600998178957605157327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25886935995143886947086205 9707600998178957605157327)
      ·
        refine ⟨14561401497268436407735991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707600998178957605157327 14561401497268436407735991)
        ·
          refine ⟨21842102245902654611603987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561401497268436407735991 21842102245902654611603987)
          ·
            refine ⟨32763153368853981917405981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21842102245902654611603987 32763153368853981917405981)
            ·
              refine ⟨12286182513320243219027243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32763153368853981917405981 12286182513320243219027243)
              ·
                refine ⟨18429273769980364828540865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286182513320243219027243 18429273769980364828540865)
                ·
                  refine ⟨13821955327485273621405649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18429273769980364828540865 13821955327485273621405649)
                  ·
                    refine ⟨10366466495613955216054237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13821955327485273621405649 10366466495613955216054237)
                    ·
                      refine ⟨3887424935855233206020339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366466495613955216054237 3887424935855233206020339)
                      ·
                        rfl

theorem cell23_7570733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7570733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570733 prefixEnd_7570733 := by exact prefixLift 7570733
  have htrace : WordTrace (prefixWord ++ tailWord_7570733) baseStart_7570733 baseEnd_7570733 := by
    simpa [prefixWord, tailWord_7570733, baseEnd_7570733] using wordTrace_append hprefix tailTrace_7570733
  have hstable : (prefixWord ++ tailWord_7570733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570733).length < 2 ^ (prefixWord ++ tailWord_7570733).sum := by decide
  have hdescent : baseEnd_7570733 < baseStart_7570733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570762 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_7570762 : Nat := 118140960795 + 7570762 * 2 ^ 59
def prefixEnd_7570762 : Nat := 4983230072969 + 3 ^ 40 * 7570762 * 2
def baseEnd_7570762 : Nat := 1295813275598071197519235

theorem tailTrace_7570762 : CollatzResearch.WordTrace tailWord_7570762 prefixEnd_7570762 1295813275598071197519235 := by
  unfold tailWord_7570762
  simp only [CollatzResearch.WordTrace]
  refine ⟨69032093749607433013764635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184085583332286488036705693 69032093749607433013764635)
  ·
    refine ⟨103548140624411149520646953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69032093749607433013764635 103548140624411149520646953)
    ·
      refine ⟨77661105468308362140485215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103548140624411149520646953 77661105468308362140485215)
      ·
        refine ⟨116491658202462543210727823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77661105468308362140485215 116491658202462543210727823)
        ·
          refine ⟨174737487303693814816091735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116491658202462543210727823 174737487303693814816091735)
          ·
            refine ⟨262106230955540722224137603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174737487303693814816091735 262106230955540722224137603)
            ·
              refine ⟨393159346433311083336206405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262106230955540722224137603 393159346433311083336206405)
              ·
                refine ⟨73717377456245828125538701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393159346433311083336206405 73717377456245828125538701)
                ·
                  refine ⟨27644016546092185547077013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73717377456245828125538701 27644016546092185547077013)
                  ·
                    refine ⟨1295813275598071197519235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27644016546092185547077013 1295813275598071197519235)
                    ·
                      rfl

theorem cell23_7570762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_7570762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570762 prefixEnd_7570762 := by exact prefixLift 7570762
  have htrace : WordTrace (prefixWord ++ tailWord_7570762) baseStart_7570762 baseEnd_7570762 := by
    simpa [prefixWord, tailWord_7570762, baseEnd_7570762] using wordTrace_append hprefix tailTrace_7570762
  have hstable : (prefixWord ++ tailWord_7570762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570762).length < 2 ^ (prefixWord ++ tailWord_7570762).sum := by decide
  have hdescent : baseEnd_7570762 < baseStart_7570762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570786 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_7570786 : Nat := 118140960795 + 7570786 * 2 ^ 59
def prefixEnd_7570786 : Nat := 4983230072969 + 3 ^ 40 * 7570786 * 2
def baseEnd_7570786 : Nat := 3887452150329921498657595

theorem tailTrace_7570786 : CollatzResearch.WordTrace tailWord_7570786 prefixEnd_7570786 3887452150329921498657595 := by
  unfold tailWord_7570786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69032312587585696038483053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184086166900228522769288141 69032312587585696038483053)
  ·
    refine ⟨25887117220344636014431145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69032312587585696038483053 25887117220344636014431145)
    ·
      refine ⟨19415337915258477010823359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25887117220344636014431145 19415337915258477010823359)
      ·
        refine ⟨29123006872887715516235039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19415337915258477010823359 29123006872887715516235039)
        ·
          refine ⟨43684510309331573274352559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29123006872887715516235039 43684510309331573274352559)
          ·
            refine ⟨65526765463997359911528839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43684510309331573274352559 65526765463997359911528839)
            ·
              refine ⟨98290148195996039867293259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65526765463997359911528839 98290148195996039867293259)
              ·
                refine ⟨147435222293994059800939889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98290148195996039867293259 147435222293994059800939889)
                ·
                  refine ⟨110576416720495544850704917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147435222293994059800939889 110576416720495544850704917)
                  ·
                    refine ⟨5183269533773228664876793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110576416720495544850704917 5183269533773228664876793)
                    ·
                      refine ⟨3887452150329921498657595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5183269533773228664876793 3887452150329921498657595)
                      ·
                        rfl

theorem cell23_7570786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_7570786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570786 prefixEnd_7570786 := by exact prefixLift 7570786
  have htrace : WordTrace (prefixWord ++ tailWord_7570786) baseStart_7570786 baseEnd_7570786 := by
    simpa [prefixWord, tailWord_7570786, baseEnd_7570786] using wordTrace_append hprefix tailTrace_7570786
  have hstable : (prefixWord ++ tailWord_7570786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570786).length < 2 ^ (prefixWord ++ tailWord_7570786).sum := by decide
  have hdescent : baseEnd_7570786 < baseStart_7570786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570814 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7570814 : Nat := 118140960795 + 7570814 * 2 ^ 59
def prefixEnd_7570814 : Nat := 4983230072969 + 3 ^ 40 * 7570814 * 2
def baseEnd_7570814 : Nat := 3887466527788247389107467

theorem tailTrace_7570814 : CollatzResearch.WordTrace tailWord_7570814 prefixEnd_7570814 3887466527788247389107467 := by
  unfold tailWord_7570814
  simp only [CollatzResearch.WordTrace]
  refine ⟨34516283949280168116993937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184086847729494229957300997 34516283949280168116993937)
  ·
    refine ⟨25887212961960126087745453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34516283949280168116993937 25887212961960126087745453)
    ·
      refine ⟨9707704860735047282904545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25887212961960126087745453 9707704860735047282904545)
      ·
        refine ⟨7280778645551285462178409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9707704860735047282904545 7280778645551285462178409)
        ·
          refine ⟨5460583984163464096633807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7280778645551285462178409 5460583984163464096633807)
          ·
            refine ⟨8190875976245196144950711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460583984163464096633807 8190875976245196144950711)
            ·
              refine ⟨12286313964367794217426067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190875976245196144950711 12286313964367794217426067)
              ·
                refine ⟨18429470946551691326139101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286313964367794217426067 18429470946551691326139101)
                ·
                  refine ⟨6911051604956884247302163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18429470946551691326139101 6911051604956884247302163)
                  ·
                    refine ⟨10366577407435326370953245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6911051604956884247302163 10366577407435326370953245)
                    ·
                      refine ⟨3887466527788247389107467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366577407435326370953245 3887466527788247389107467)
                      ·
                        rfl

theorem cell23_7570814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7570814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570814 prefixEnd_7570814 := by exact prefixLift 7570814
  have htrace : WordTrace (prefixWord ++ tailWord_7570814) baseStart_7570814 baseEnd_7570814 := by
    simpa [prefixWord, tailWord_7570814, baseEnd_7570814] using wordTrace_append hprefix tailTrace_7570814
  have hstable : (prefixWord ++ tailWord_7570814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570814).length < 2 ^ (prefixWord ++ tailWord_7570814).sum := by decide
  have hdescent : baseEnd_7570814 < baseStart_7570814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570820 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_7570820 : Nat := 118140960795 + 7570820 * 2 ^ 59
def prefixEnd_7570820 : Nat := 4983230072969 + 3 ^ 40 * 7570820 * 2
def baseEnd_7570820 : Nat := 3887469608672174365632439

theorem tailTrace_7570820 : CollatzResearch.WordTrace tailWord_7570820 prefixEnd_7570820 3887469608672174365632439 := by
  unfold tailWord_7570820
  simp only [CollatzResearch.WordTrace]
  refine ⟨138065245216109803980334957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184086993621479738640446609 138065245216109803980334957)
  ·
    refine ⟨51774466956041176492625609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138065245216109803980334957 51774466956041176492625609)
    ·
      refine ⟨38830850217030882369469207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51774466956041176492625609 38830850217030882369469207)
      ·
        refine ⟨58246275325546323554203811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38830850217030882369469207 58246275325546323554203811)
        ·
          refine ⟨87369412988319485331305717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58246275325546323554203811 87369412988319485331305717)
          ·
            refine ⟨8190882467654951749809911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87369412988319485331305717 8190882467654951749809911)
            ·
              refine ⟨12286323701482427624714867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190882467654951749809911 12286323701482427624714867)
              ·
                refine ⟨18429485552223641437072301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286323701482427624714867 18429485552223641437072301)
                ·
                  refine ⟨6911057082083865538902113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18429485552223641437072301 6911057082083865538902113)
                  ·
                    refine ⟨5183292811562899154176585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6911057082083865538902113 5183292811562899154176585)
                    ·
                      refine ⟨3887469608672174365632439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5183292811562899154176585 3887469608672174365632439)
                      ·
                        rfl

theorem cell23_7570820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_7570820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570820 prefixEnd_7570820 := by exact prefixLift 7570820
  have htrace : WordTrace (prefixWord ++ tailWord_7570820) baseStart_7570820 baseEnd_7570820 := by
    simpa [prefixWord, tailWord_7570820, baseEnd_7570820] using wordTrace_append hprefix tailTrace_7570820
  have hstable : (prefixWord ++ tailWord_7570820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570820).length < 2 ^ (prefixWord ++ tailWord_7570820).sum := by decide
  have hdescent : baseEnd_7570820 < baseStart_7570820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570840 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7570840 : Nat := 118140960795 + 7570840 * 2 ^ 59
def prefixEnd_7570840 : Nat := 4983230072969 + 3 ^ 40 * 7570840 * 2
def baseEnd_7570840 : Nat := 3887479878285264287382347

theorem tailTrace_7570840 : CollatzResearch.WordTrace tailWord_7570840 prefixEnd_7570840 3887479878285264287382347 := by
  unfold tailWord_7570840
  simp only [CollatzResearch.WordTrace]
  refine ⟨138065609946073575688198987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184087479928098100917598649 138065609946073575688198987)
  ·
    refine ⟨207098414919110363532298481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138065609946073575688198987 207098414919110363532298481)
    ·
      refine ⟨155323811189332772649223861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207098414919110363532298481 155323811189332772649223861)
      ·
        refine ⟨14561607298999947435864737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155323811189332772649223861 14561607298999947435864737)
        ·
          refine ⟨10921205474249960576898553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14561607298999947435864737 10921205474249960576898553)
          ·
            refine ⟨8190904105687470432673915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10921205474249960576898553 8190904105687470432673915)
            ·
              refine ⟨12286356158531205649010873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190904105687470432673915 12286356158531205649010873)
              ·
                refine ⟨9214767118898404236758155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12286356158531205649010873 9214767118898404236758155)
                ·
                  refine ⟨13822150678347606355137233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9214767118898404236758155 13822150678347606355137233)
                  ·
                    refine ⟨10366613008760704766352925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13822150678347606355137233 10366613008760704766352925)
                    ·
                      refine ⟨3887479878285264287382347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366613008760704766352925 3887479878285264287382347)
                      ·
                        rfl

theorem cell23_7570840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7570840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570840 prefixEnd_7570840 := by exact prefixLift 7570840
  have htrace : WordTrace (prefixWord ++ tailWord_7570840) baseStart_7570840 baseEnd_7570840 := by
    simpa [prefixWord, tailWord_7570840, baseEnd_7570840] using wordTrace_append hprefix tailTrace_7570840
  have hstable : (prefixWord ++ tailWord_7570840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570840).length < 2 ^ (prefixWord ++ tailWord_7570840).sum := by decide
  have hdescent : baseEnd_7570840 < baseStart_7570840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570926 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_7570926 : Nat := 118140960795 + 7570926 * 2 ^ 59
def prefixEnd_7570926 : Nat := 4983230072969 + 3 ^ 40 * 7570926 * 2
def baseEnd_7570926 : Nat := 3887524037621550950906951

theorem tailTrace_7570926 : CollatzResearch.WordTrace tailWord_7570926 prefixEnd_7570926 3887524037621550950906951 := by
  unfold tailWord_7570926
  simp only [CollatzResearch.WordTrace]
  refine ⟨34516794571229448508003579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184089571046557058709352421 34516794571229448508003579)
  ·
    refine ⟨51775191856844172762005369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34516794571229448508003579 51775191856844172762005369)
    ·
      refine ⟨38831393892633129571504027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51775191856844172762005369 38831393892633129571504027)
      ·
        refine ⟨58247090838949694357256041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38831393892633129571504027 58247090838949694357256041)
        ·
          refine ⟨43685318129212270767942031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58247090838949694357256041 43685318129212270767942031)
          ·
            refine ⟨65527977193818406151913047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43685318129212270767942031 65527977193818406151913047)
            ·
              refine ⟨98291965790727609227869571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65527977193818406151913047 98291965790727609227869571)
              ·
                refine ⟨147437948686091413841804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98291965790727609227869571 147437948686091413841804357)
                ·
                  refine ⟨27644615378642140095338317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147437948686091413841804357 27644615378642140095338317)
                  ·
                    refine ⟨10366730766990802535751869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27644615378642140095338317 10366730766990802535751869)
                    ·
                      refine ⟨3887524037621550950906951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10366730766990802535751869 3887524037621550950906951)
                      ·
                        rfl

theorem cell23_7570926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_7570926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570926 prefixEnd_7570926 := by exact prefixLift 7570926
  have htrace : WordTrace (prefixWord ++ tailWord_7570926) baseStart_7570926 baseEnd_7570926 := by
    simpa [prefixWord, tailWord_7570926, baseEnd_7570926] using wordTrace_append hprefix tailTrace_7570926
  have hstable : (prefixWord ++ tailWord_7570926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570926).length < 2 ^ (prefixWord ++ tailWord_7570926).sum := by decide
  have hdescent : baseEnd_7570926 < baseStart_7570926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570933 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 7]
def baseStart_7570933 : Nat := 118140960795 + 7570933 * 2 ^ 59
def prefixEnd_7570933 : Nat := 4983230072969 + 3 ^ 40 * 7570933 * 2
def baseEnd_7570933 : Nat := 431947514665125824835491

theorem tailTrace_7570933 : CollatzResearch.WordTrace tailWord_7570933 prefixEnd_7570933 431947514665125824835491 := by
  unfold tailWord_7570933
  simp only [CollatzResearch.WordTrace]
  refine ⟨276134611880810228259533453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184089741253873485506355635 276134611880810228259533453)
  ·
    refine ⟨103550479455303835597325045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276134611880810228259533453 103550479455303835597325045)
    ·
      refine ⟨9707857448934734587249223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103550479455303835597325045 9707857448934734587249223)
      ·
        refine ⟨14561786173402101880873835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707857448934734587249223 14561786173402101880873835)
        ·
          refine ⟨21842679260103152821310753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561786173402101880873835 21842679260103152821310753)
          ·
            refine ⟨16382009445077364615983065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21842679260103152821310753 16382009445077364615983065)
            ·
              refine ⟨12286507083808023461987299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16382009445077364615983065 12286507083808023461987299)
              ·
                refine ⟨18429760625712035192980949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286507083808023461987299 18429760625712035192980949)
                ·
                  refine ⟨431947514665125824835491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18429760625712035192980949 431947514665125824835491)
                  ·
                    rfl

theorem cell23_7570933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_7570933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570933 prefixEnd_7570933 := by exact prefixLift 7570933
  have htrace : WordTrace (prefixWord ++ tailWord_7570933) baseStart_7570933 baseEnd_7570933 := by
    simpa [prefixWord, tailWord_7570933, baseEnd_7570933] using wordTrace_append hprefix tailTrace_7570933
  have hstable : (prefixWord ++ tailWord_7570933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570933).length < 2 ^ (prefixWord ++ tailWord_7570933).sum := by decide
  have hdescent : baseEnd_7570933 < baseStart_7570933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571073 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7571073 : Nat := 118140960795 + 7571073 * 2 ^ 59
def prefixEnd_7571073 : Nat := 4983230072969 + 3 ^ 40 * 7571073 * 2
def baseEnd_7571073 : Nat := 3887599519277761875768775

theorem tailTrace_7571073 : CollatzResearch.WordTrace tailWord_7571073 prefixEnd_7571073 3887599519277761875768775 := by
  unfold tailWord_7571073
  simp only [CollatzResearch.WordTrace]
  refine ⟨276139718100303032169629873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184093145400202021446419915 276139718100303032169629873)
  ·
    refine ⟨207104788575227274127222405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276139718100303032169629873 207104788575227274127222405)
    ·
      refine ⟨38832147857855113898854201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207104788575227274127222405 38832147857855113898854201)
      ·
        refine ⟨29124110893391335424140651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38832147857855113898854201 29124110893391335424140651)
        ·
          refine ⟨43686166340087003136210977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29124110893391335424140651 43686166340087003136210977)
          ·
            refine ⟨32764624755065252352158233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43686166340087003136210977 32764624755065252352158233)
            ·
              refine ⟨24573468566298939264118675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32764624755065252352158233 24573468566298939264118675)
              ·
                refine ⟨36860202849448408896178013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24573468566298939264118675 36860202849448408896178013)
                ·
                  refine ⟨13822576068543153336066755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36860202849448408896178013 13822576068543153336066755)
                  ·
                    refine ⟨20733864102814730004100133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13822576068543153336066755 20733864102814730004100133)
                    ·
                      refine ⟨3887599519277761875768775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20733864102814730004100133 3887599519277761875768775)
                      ·
                        rfl

theorem cell23_7571073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7571073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571073 prefixEnd_7571073 := by exact prefixLift 7571073
  have htrace : WordTrace (prefixWord ++ tailWord_7571073) baseStart_7571073 baseEnd_7571073 := by
    simpa [prefixWord, tailWord_7571073, baseEnd_7571073] using wordTrace_append hprefix tailTrace_7571073
  have hstable : (prefixWord ++ tailWord_7571073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571073).length < 2 ^ (prefixWord ++ tailWord_7571073).sum := by decide
  have hdescent : baseEnd_7571073 < baseStart_7571073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571096 : List Nat := [2, 1, 2, 4, 1, 3, 10]
def baseStart_7571096 : Nat := 118140960795 + 7571096 * 2 ^ 59
def prefixEnd_7571096 : Nat := 4983230072969 + 3 ^ 40 * 7571096 * 2
def baseEnd_7571096 : Nat := 47995201596701423281249

theorem tailTrace_7571096 : CollatzResearch.WordTrace tailWord_7571096 prefixEnd_7571096 47995201596701423281249 := by
  unfold tailWord_7571096
  simp only [CollatzResearch.WordTrace]
  refine ⟨138070278489609853548858571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184093704652813138065144761 138070278489609853548858571)
  ·
    refine ⟨207105417734414780323287857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138070278489609853548858571 207105417734414780323287857)
    ·
      refine ⟨155329063300811085242465893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207105417734414780323287857 155329063300811085242465893)
      ·
        refine ⟨29124199368902078482962355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155329063300811085242465893 29124199368902078482962355)
        ·
          refine ⟨43686299053353117724443533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29124199368902078482962355 43686299053353117724443533)
          ·
            refine ⟨16382362145007419146666325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43686299053353117724443533 16382362145007419146666325)
            ·
              refine ⟨47995201596701423281249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16382362145007419146666325 47995201596701423281249)
              ·
                rfl

theorem cell23_7571096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 10].length) (baseStart_7571096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571096 prefixEnd_7571096 := by exact prefixLift 7571096
  have htrace : WordTrace (prefixWord ++ tailWord_7571096) baseStart_7571096 baseEnd_7571096 := by
    simpa [prefixWord, tailWord_7571096, baseEnd_7571096] using wordTrace_append hprefix tailTrace_7571096
  have hstable : (prefixWord ++ tailWord_7571096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571096).length < 2 ^ (prefixWord ++ tailWord_7571096).sum := by decide
  have hdescent : baseEnd_7571096 < baseStart_7571096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571100 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_7571100 : Nat := 118140960795 + 7571100 * 2 ^ 59
def prefixEnd_7571100 : Nat := 4983230072969 + 3 ^ 40 * 7571100 * 2
def baseEnd_7571100 : Nat := 1295871127751811090043717

theorem tailTrace_7571100 : CollatzResearch.WordTrace tailWord_7571100 prefixEnd_7571100 1295871127751811090043717 := by
  unfold tailWord_7571100
  simp only [CollatzResearch.WordTrace]
  refine ⟨138070351435602607890431377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184093801914136810520575169 138070351435602607890431377)
  ·
    refine ⟨103552763576701955917823533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138070351435602607890431377 103552763576701955917823533)
    ·
      refine ⟨38832286341263233469183825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103552763576701955917823533 38832286341263233469183825)
      ·
        refine ⟨29124214755947425101887869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38832286341263233469183825 29124214755947425101887869)
        ·
          refine ⟨10921580533480284413207951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29124214755947425101887869 10921580533480284413207951)
          ·
            refine ⟨16382370800220426619811927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10921580533480284413207951 16382370800220426619811927)
            ·
              refine ⟨24573556200330639929717891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16382370800220426619811927 24573556200330639929717891)
              ·
                refine ⟨36860334300495959894576837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24573556200330639929717891 36860334300495959894576837)
                ·
                  refine ⟨6911312681342992480233157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36860334300495959894576837 6911312681342992480233157)
                  ·
                    refine ⟨1295871127751811090043717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6911312681342992480233157 1295871127751811090043717)
                    ·
                      rfl

theorem cell23_7571100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_7571100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571100 prefixEnd_7571100 := by exact prefixLift 7571100
  have htrace : WordTrace (prefixWord ++ tailWord_7571100) baseStart_7571100 baseEnd_7571100 := by
    simpa [prefixWord, tailWord_7571100, baseEnd_7571100] using wordTrace_append hprefix tailTrace_7571100
  have hstable : (prefixWord ++ tailWord_7571100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571100).length < 2 ^ (prefixWord ++ tailWord_7571100).sum := by decide
  have hdescent : baseEnd_7571100 < baseStart_7571100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571107 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 1, 2, 2]
def baseStart_7571107 : Nat := 118140960795 + 7571107 * 2 ^ 59
def prefixEnd_7571107 : Nat := 4983230072969 + 3 ^ 40 * 7571107 * 2
def baseEnd_7571107 : Nat := 3887616977620014742743619

theorem tailTrace_7571107 : CollatzResearch.WordTrace tailWord_7571107 prefixEnd_7571107 3887616977620014742743619 := by
  unfold tailWord_7571107
  simp only [CollatzResearch.WordTrace]
  refine ⟨276140958182179855976367575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184093972121453237317578383 276140958182179855976367575)
  ·
    refine ⟨414211437273269783964551363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276140958182179855976367575 414211437273269783964551363)
    ·
      refine ⟨621317155909904675946827045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414211437273269783964551363 621317155909904675946827045)
      ·
        refine ⟨116496966733107126740030071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 621317155909904675946827045 116496966733107126740030071)
        ·
          refine ⟨174745450099660690110045107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116496966733107126740030071 174745450099660690110045107)
          ·
            refine ⟨262118175149491035165067661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174745450099660690110045107 262118175149491035165067661)
            ·
              refine ⟨98294315681059138186900373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262118175149491035165067661 98294315681059138186900373)
              ·
                refine ⟨4607546047549647102510955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98294315681059138186900373 4607546047549647102510955)
                ·
                  refine ⟨6911319071324470653766433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607546047549647102510955 6911319071324470653766433)
                  ·
                    refine ⟨5183489303493352990324825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6911319071324470653766433 5183489303493352990324825)
                    ·
                      refine ⟨3887616977620014742743619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5183489303493352990324825 3887616977620014742743619)
                      ·
                        rfl

theorem cell23_7571107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_7571107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571107 prefixEnd_7571107 := by exact prefixLift 7571107
  have htrace : WordTrace (prefixWord ++ tailWord_7571107) baseStart_7571107 baseEnd_7571107 := by
    simpa [prefixWord, tailWord_7571107, baseEnd_7571107] using wordTrace_append hprefix tailTrace_7571107
  have hstable : (prefixWord ++ tailWord_7571107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571107).length < 2 ^ (prefixWord ++ tailWord_7571107).sum := by decide
  have hdescent : baseEnd_7571107 < baseStart_7571107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571117 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7571117 : Nat := 118140960795 + 7571117 * 2 ^ 59
def prefixEnd_7571117 : Nat := 4983230072969 + 3 ^ 40 * 7571117 * 2
def baseEnd_7571117 : Nat := 1295874037475519901206191

theorem tailTrace_7571117 : CollatzResearch.WordTrace tailWord_7571117 prefixEnd_7571117 1295874037475519901206191 := by
  unfold tailWord_7571117
  simp only [CollatzResearch.WordTrace]
  refine ⟨276141322912143627684231605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184094215274762418456154403 276141322912143627684231605)
  ·
    refine ⟨25888249023013465095396713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276141322912143627684231605 25888249023013465095396713)
    ·
      refine ⟨19416186767260098821547535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25888249023013465095396713 19416186767260098821547535)
      ·
        refine ⟨29124280150890148232321303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19416186767260098821547535 29124280150890148232321303)
        ·
          refine ⟨43686420226335222348481955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29124280150890148232321303 43686420226335222348481955)
          ·
            refine ⟨65529630339502833522722933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43686420226335222348481955 65529630339502833522722933)
            ·
              refine ⟨6143402844328390642755275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65529630339502833522722933 6143402844328390642755275)
              ·
                refine ⟨9215104266492585964132913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143402844328390642755275 9215104266492585964132913)
                ·
                  refine ⟨6911328199869439473099685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9215104266492585964132913 6911328199869439473099685)
                  ·
                    refine ⟨1295874037475519901206191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6911328199869439473099685 1295874037475519901206191)
                    ·
                      rfl

theorem cell23_7571117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7571117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571117 prefixEnd_7571117 := by exact prefixLift 7571117
  have htrace : WordTrace (prefixWord ++ tailWord_7571117) baseStart_7571117 baseEnd_7571117 := by
    simpa [prefixWord, tailWord_7571117, baseEnd_7571117] using wordTrace_append hprefix tailTrace_7571117
  have hstable : (prefixWord ++ tailWord_7571117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571117).length < 2 ^ (prefixWord ++ tailWord_7571117).sum := by decide
  have hdescent : baseEnd_7571117 < baseStart_7571117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571136 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_7571136 : Nat := 118140960795 + 7571136 * 2 ^ 59
def prefixEnd_7571136 : Nat := 4983230072969 + 3 ^ 40 * 7571136 * 2
def baseEnd_7571136 : Nat := 3887631868558995129280985

theorem tailTrace_7571136 : CollatzResearch.WordTrace tailWord_7571136 prefixEnd_7571136 3887631868558995129280985 := by
  unfold tailWord_7571136
  simp only [CollatzResearch.WordTrace]
  refine ⟨138071007949537396964586631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184094677266049862619448841 138071007949537396964586631)
  ·
    refine ⟨207106511924306095446879947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138071007949537396964586631 207106511924306095446879947)
    ·
      refine ⟨310659767886459143170319921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207106511924306095446879947 310659767886459143170319921)
      ·
        refine ⟨232994825914844357377739941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310659767886459143170319921 232994825914844357377739941)
        ·
          refine ⟨43686529859033317008326239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232994825914844357377739941 43686529859033317008326239)
          ·
            refine ⟨65529794788549975512489359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43686529859033317008326239 65529794788549975512489359)
            ·
              refine ⟨98294692182824963268734039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65529794788549975512489359 98294692182824963268734039)
              ·
                refine ⟨147442038274237444903101059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98294692182824963268734039 147442038274237444903101059)
                ·
                  refine ⟨221163057411356167354651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147442038274237444903101059 221163057411356167354651589)
                  ·
                    refine ⟨41468073264629281378997173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221163057411356167354651589 41468073264629281378997173)
                    ·
                      refine ⟨3887631868558995129280985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41468073264629281378997173 3887631868558995129280985)
                      ·
                        rfl

theorem cell23_7571136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_7571136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571136 prefixEnd_7571136 := by exact prefixLift 7571136
  have htrace : WordTrace (prefixWord ++ tailWord_7571136) baseStart_7571136 baseEnd_7571136 := by
    simpa [prefixWord, tailWord_7571136, baseEnd_7571136] using wordTrace_append hprefix tailTrace_7571136
  have hstable : (prefixWord ++ tailWord_7571136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571136).length < 2 ^ (prefixWord ++ tailWord_7571136).sum := by decide
  have hdescent : baseEnd_7571136 < baseStart_7571136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571140 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_7571140 : Nat := 118140960795 + 7571140 * 2 ^ 59
def prefixEnd_7571140 : Nat := 4983230072969 + 3 ^ 40 * 7571140 * 2
def baseEnd_7571140 : Nat := 3887633922481613113630967

theorem tailTrace_7571140 : CollatzResearch.WordTrace tailWord_7571140 prefixEnd_7571140 3887633922481613113630967 := by
  unfold tailWord_7571140
  simp only [CollatzResearch.WordTrace]
  refine ⟨138071080895530151306159437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184094774527373535074879249 138071080895530151306159437)
  ·
    refine ⟨51776655335823806739809789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138071080895530151306159437 51776655335823806739809789)
    ·
      refine ⟨19416245750933927527428671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51776655335823806739809789 19416245750933927527428671)
      ·
        refine ⟨29124368626400891291143007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19416245750933927527428671 29124368626400891291143007)
        ·
          refine ⟨43686552939601336936714511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29124368626400891291143007 43686552939601336936714511)
          ·
            refine ⟨65529829409402005405071767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43686552939601336936714511 65529829409402005405071767)
            ·
              refine ⟨98294744114103008107607651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65529829409402005405071767 98294744114103008107607651)
              ·
                refine ⟨147442116171154512161411477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98294744114103008107607651 147442116171154512161411477)
                ·
                  refine ⟨6911349195522867757566163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147442116171154512161411477 6911349195522867757566163)
                  ·
                    refine ⟨10367023793284301636349245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6911349195522867757566163 10367023793284301636349245)
                    ·
                      refine ⟨3887633922481613113630967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367023793284301636349245 3887633922481613113630967)
                      ·
                        rfl

theorem cell23_7571140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_7571140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571140 prefixEnd_7571140 := by exact prefixLift 7571140
  have htrace : WordTrace (prefixWord ++ tailWord_7571140) baseStart_7571140 baseEnd_7571140 := by
    simpa [prefixWord, tailWord_7571140, baseEnd_7571140] using wordTrace_append hprefix tailTrace_7571140
  have hstable : (prefixWord ++ tailWord_7571140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571140).length < 2 ^ (prefixWord ++ tailWord_7571140).sum := by decide
  have hdescent : baseEnd_7571140 < baseStart_7571140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571158 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7571158 : Nat := 118140960795 + 7571158 * 2 ^ 59
def prefixEnd_7571158 : Nat := 4983230072969 + 3 ^ 40 * 7571158 * 2
def baseEnd_7571158 : Nat := 3887643165133394043205885

theorem tailTrace_7571158 : CollatzResearch.WordTrace tailWord_7571158 prefixEnd_7571158 3887643165133394043205885 := by
  unfold tailWord_7571158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258926144062193230404633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184095212203330061124316085 17258926144062193230404633)
  ·
    refine ⟨12944194608046644922803475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17258926144062193230404633 12944194608046644922803475)
    ·
      refine ⟨19416291912069967384205213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944194608046644922803475 19416291912069967384205213)
      ·
        refine ⟨7281109467026237769076955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19416291912069967384205213 7281109467026237769076955)
        ·
          refine ⟨10921664200539356653615433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281109467026237769076955 10921664200539356653615433)
          ·
            refine ⟨8191248150404517490211575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10921664200539356653615433 8191248150404517490211575)
            ·
              refine ⟨12286872225606776235317363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8191248150404517490211575 12286872225606776235317363)
              ·
                refine ⟨18430308338410164352976045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286872225606776235317363 18430308338410164352976045)
                ·
                  refine ⟨6911365626903811632366017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18430308338410164352976045 6911365626903811632366017)
                  ·
                    refine ⟨5183524220177858724274513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6911365626903811632366017 5183524220177858724274513)
                    ·
                      refine ⟨3887643165133394043205885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5183524220177858724274513 3887643165133394043205885)
                      ·
                        rfl

theorem cell23_7571158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7571158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571158 prefixEnd_7571158 := by exact prefixLift 7571158
  have htrace : WordTrace (prefixWord ++ tailWord_7571158) baseStart_7571158 baseEnd_7571158 := by
    simpa [prefixWord, tailWord_7571158, baseEnd_7571158] using wordTrace_append hprefix tailTrace_7571158
  have hstable : (prefixWord ++ tailWord_7571158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571158).length < 2 ^ (prefixWord ++ tailWord_7571158).sum := by decide
  have hdescent : baseEnd_7571158 < baseStart_7571158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571250 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_7571250 : Nat := 118140960795 + 7571250 * 2 ^ 59
def prefixEnd_7571250 : Nat := 4983230072969 + 3 ^ 40 * 7571250 * 2
def baseEnd_7571250 : Nat := 1295896801784535894418487

theorem tailTrace_7571250 : CollatzResearch.WordTrace tailWord_7571250 prefixEnd_7571250 1295896801784535894418487 := by
  unfold tailWord_7571250
  simp only [CollatzResearch.WordTrace]
  refine ⟨69036543455165447849705801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184097449213774527599215469 69036543455165447849705801)
  ·
    refine ⟨51777407591374085887279351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69036543455165447849705801 51777407591374085887279351)
    ·
      refine ⟨77666111387061128830919027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51777407591374085887279351 77666111387061128830919027)
      ·
        refine ⟨116499167080591693246378541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77666111387061128830919027 116499167080591693246378541)
        ·
          refine ⟨43687187655221884967391953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116499167080591693246378541 43687187655221884967391953)
          ·
            refine ⟨32765390741416413725543965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43687187655221884967391953 32765390741416413725543965)
            ·
              refine ⟨12287021528031155147078987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32765390741416413725543965 12287021528031155147078987)
              ·
                refine ⟨18430532292046732720618481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12287021528031155147078987 18430532292046732720618481)
                ·
                  refine ⟨13822899219035049540463861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18430532292046732720618481 13822899219035049540463861)
                  ·
                    refine ⟨1295896801784535894418487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13822899219035049540463861 1295896801784535894418487)
                    ·
                      rfl

theorem cell23_7571250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_7571250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571250 prefixEnd_7571250 := by exact prefixLift 7571250
  have htrace : WordTrace (prefixWord ++ tailWord_7571250) baseStart_7571250 baseEnd_7571250 := by
    simpa [prefixWord, tailWord_7571250, baseEnd_7571250] using wordTrace_append hprefix tailTrace_7571250
  have hstable : (prefixWord ++ tailWord_7571250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571250).length < 2 ^ (prefixWord ++ tailWord_7571250).sum := by decide
  have hdescent : baseEnd_7571250 < baseStart_7571250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571254 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_7571254 : Nat := 118140960795 + 7571254 * 2 ^ 59
def prefixEnd_7571254 : Nat := 4983230072969 + 3 ^ 40 * 7571254 * 2
def baseEnd_7571254 : Nat := 431965828808469518622827

theorem tailTrace_7571254 : CollatzResearch.WordTrace tailWord_7571254 prefixEnd_7571254 431965828808469518622827 := by
  unfold tailWord_7571254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259144982040456255123051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184097546475098200054645877 17259144982040456255123051)
  ·
    refine ⟨25888717473060684382684577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17259144982040456255123051 25888717473060684382684577)
    ·
      refine ⟨19416538104795513287013433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25888717473060684382684577 19416538104795513287013433)
      ·
        refine ⟨14562403578596634965260075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19416538104795513287013433 14562403578596634965260075)
        ·
          refine ⟨21843605367894952447890113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14562403578596634965260075 21843605367894952447890113)
          ·
            refine ⟨16382704025921214335917585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21843605367894952447890113 16382704025921214335917585)
            ·
              refine ⟨12287028019440910751938189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16382704025921214335917585 12287028019440910751938189)
              ·
                refine ⟨4607635507290341531976821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12287028019440910751938189 4607635507290341531976821)
                ·
                  refine ⟨431965828808469518622827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4607635507290341531976821 431965828808469518622827)
                  ·
                    rfl

theorem cell23_7571254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_7571254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571254 prefixEnd_7571254 := by exact prefixLift 7571254
  have htrace : WordTrace (prefixWord ++ tailWord_7571254) baseStart_7571254 baseEnd_7571254 := by
    simpa [prefixWord, tailWord_7571254, baseEnd_7571254] using wordTrace_append hprefix tailTrace_7571254
  have hstable : (prefixWord ++ tailWord_7571254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571254).length < 2 ^ (prefixWord ++ tailWord_7571254).sum := by decide
  have hdescent : baseEnd_7571254 < baseStart_7571254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571310 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_7571310 : Nat := 118140960795 + 7571310 * 2 ^ 59
def prefixEnd_7571310 : Nat := 4983230072969 + 3 ^ 40 * 7571310 * 2
def baseEnd_7571310 : Nat := 431969023799208605389465

theorem tailTrace_7571310 : CollatzResearch.WordTrace tailWord_7571310 prefixEnd_7571310 431969023799208605389465 := by
  unfold tailWord_7571310
  simp only [CollatzResearch.WordTrace]
  refine ⟨34518545275055552705750923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184098908133629614430671589 34518545275055552705750923)
  ·
    refine ⟨51777817912583329058626385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34518545275055552705750923 51777817912583329058626385)
    ·
      refine ⟨38833363434437496793969789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51777817912583329058626385 38833363434437496793969789)
      ·
        refine ⟨14562511287914061297738671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38833363434437496793969789 14562511287914061297738671)
        ·
          refine ⟨21843766931871091946608007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14562511287914061297738671 21843766931871091946608007)
          ·
            refine ⟨32765650397806637919912011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21843766931871091946608007 32765650397806637919912011)
            ·
              refine ⟨49148475596709956879868017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32765650397806637919912011 49148475596709956879868017)
              ·
                refine ⟨36861356697532467659901013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49148475596709956879868017 36861356697532467659901013)
                ·
                  refine ⟨431969023799208605389465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36861356697532467659901013 431969023799208605389465)
                  ·
                    rfl

theorem cell23_7571310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_7571310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571310 prefixEnd_7571310 := by exact prefixLift 7571310
  have htrace : WordTrace (prefixWord ++ tailWord_7571310) baseStart_7571310 baseEnd_7571310 := by
    simpa [prefixWord, tailWord_7571310, baseEnd_7571310] using wordTrace_append hprefix tailTrace_7571310
  have hstable : (prefixWord ++ tailWord_7571310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571310).length < 2 ^ (prefixWord ++ tailWord_7571310).sum := by decide
  have hdescent : baseEnd_7571310 < baseStart_7571310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571323 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 5, 5]
def baseStart_7571323 : Nat := 118140960795 + 7571323 * 2 ^ 59
def prefixEnd_7571323 : Nat := 4983230072969 + 3 ^ 40 * 7571323 * 2
def baseEnd_7571323 : Nat := 1295909296480461965880875

theorem tailTrace_7571323 : CollatzResearch.WordTrace tailWord_7571323 prefixEnd_7571323 1295909296480461965880875 := by
  unfold tailWord_7571323
  simp only [CollatzResearch.WordTrace]
  refine ⟨276148836349397324866230623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184099224232931549910820415 276148836349397324866230623)
  ·
    refine ⟨414223254524095987299345935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276148836349397324866230623 414223254524095987299345935)
    ·
      refine ⟨621334881786143980949018903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414223254524095987299345935 621334881786143980949018903)
      ·
        refine ⟨932002322679215971423528355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621334881786143980949018903 932002322679215971423528355)
        ·
          refine ⟨1398003484018823957135292533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932002322679215971423528355 1398003484018823957135292533)
          ·
            refine ⟨131062826626764745981433675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1398003484018823957135292533 131062826626764745981433675)
            ·
              refine ⟨196594239940147118972150513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131062826626764745981433675 196594239940147118972150513)
              ·
                refine ⟨147445679955110339229112885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196594239940147118972150513 147445679955110339229112885)
                ·
                  refine ⟨13823032495791594302729333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147445679955110339229112885 13823032495791594302729333)
                  ·
                    refine ⟨1295909296480461965880875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13823032495791594302729333 1295909296480461965880875)
                    ·
                      rfl

theorem cell23_7571323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 5].length) (baseStart_7571323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571323 prefixEnd_7571323 := by exact prefixLift 7571323
  have htrace : WordTrace (prefixWord ++ tailWord_7571323) baseStart_7571323 baseEnd_7571323 := by
    simpa [prefixWord, tailWord_7571323, baseEnd_7571323] using wordTrace_append hprefix tailTrace_7571323
  have hstable : (prefixWord ++ tailWord_7571323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571323).length < 2 ^ (prefixWord ++ tailWord_7571323).sum := by decide
  have hdescent : baseEnd_7571323 < baseStart_7571323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571357 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_7571357 : Nat := 118140960795 + 7571357 * 2 ^ 59
def prefixEnd_7571357 : Nat := 4983230072969 + 3 ^ 40 * 7571357 * 2
def baseEnd_7571357 : Nat := 1295915115927879588205823

theorem tailTrace_7571357 : CollatzResearch.WordTrace tailWord_7571357 prefixEnd_7571357 1295915115927879588205823 := by
  unfold tailWord_7571357
  simp only [CollatzResearch.WordTrace]
  refine ⟨276150076431274148672968325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184100050954182765781978883 276150076431274148672968325)
  ·
    refine ⟨51778139330863902876181561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276150076431274148672968325 51778139330863902876181561)
    ·
      refine ⟨38833604498147927157136171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51778139330863902876181561 38833604498147927157136171)
      ·
        refine ⟨58250406747221890735704257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38833604498147927157136171 58250406747221890735704257)
        ·
          refine ⟨43687805060416418051778193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58250406747221890735704257 43687805060416418051778193)
          ·
            refine ⟨32765853795312313538833645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43687805060416418051778193 32765853795312313538833645)
            ·
              refine ⟨12287195173242117577062617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32765853795312313538833645 12287195173242117577062617)
              ·
                refine ⟨9215396379931588182796963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12287195173242117577062617 9215396379931588182796963)
                ·
                  refine ⟨13823094569897382274195445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9215396379931588182796963 13823094569897382274195445)
                  ·
                    refine ⟨1295915115927879588205823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13823094569897382274195445 1295915115927879588205823)
                    ·
                      rfl

theorem cell23_7571357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_7571357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571357 prefixEnd_7571357 := by exact prefixLift 7571357
  have htrace : WordTrace (prefixWord ++ tailWord_7571357) baseStart_7571357 baseEnd_7571357 := by
    simpa [prefixWord, tailWord_7571357, baseEnd_7571357] using wordTrace_append hprefix tailTrace_7571357
  have hstable : (prefixWord ++ tailWord_7571357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571357).length < 2 ^ (prefixWord ++ tailWord_7571357).sum := by decide
  have hdescent : baseEnd_7571357 < baseStart_7571357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571364 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_7571364 : Nat := 118140960795 + 7571364 * 2 ^ 59
def prefixEnd_7571364 : Nat := 4983230072969 + 3 ^ 40 * 7571364 * 2
def baseEnd_7571364 : Nat := 3887748942148220237229937

theorem tailTrace_7571364 : CollatzResearch.WordTrace tailWord_7571364 prefixEnd_7571364 3887748942148220237229937 := by
  unfold tailWord_7571364
  simp only [CollatzResearch.WordTrace]
  refine ⟨138075165871124394434236573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184100221161499192578982097 138075165871124394434236573)
  ·
    refine ⟨51778187201671647912838715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138075165871124394434236573 51778187201671647912838715)
    ·
      refine ⟨77667280802507471869258073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51778187201671647912838715 77667280802507471869258073)
      ·
        refine ⟨58250460601880603901943555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77667280802507471869258073 58250460601880603901943555)
        ·
          refine ⟨87375690902820905852915333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58250460601880603901943555 87375690902820905852915333)
          ·
            refine ⟨16382942044278919847421625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87375690902820905852915333 16382942044278919847421625)
            ·
              refine ⟨12287206533209189885566219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16382942044278919847421625 12287206533209189885566219)
              ·
                refine ⟨18430809799813784828349329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12287206533209189885566219 18430809799813784828349329)
                ·
                  refine ⟨13823107349860338621261997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18430809799813784828349329 13823107349860338621261997)
                  ·
                    refine ⟨5183665256197626982973249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13823107349860338621261997 5183665256197626982973249)
                    ·
                      refine ⟨3887748942148220237229937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5183665256197626982973249 3887748942148220237229937)
                      ·
                        rfl

theorem cell23_7571364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_7571364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571364 prefixEnd_7571364 := by exact prefixLift 7571364
  have htrace : WordTrace (prefixWord ++ tailWord_7571364) baseStart_7571364 baseEnd_7571364 := by
    simpa [prefixWord, tailWord_7571364, baseEnd_7571364] using wordTrace_append hprefix tailTrace_7571364
  have hstable : (prefixWord ++ tailWord_7571364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571364).length < 2 ^ (prefixWord ++ tailWord_7571364).sum := by decide
  have hdescent : baseEnd_7571364 < baseStart_7571364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571388 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7571388 : Nat := 118140960795 + 7571388 * 2 ^ 59
def prefixEnd_7571388 : Nat := 4983230072969 + 3 ^ 40 * 7571388 * 2
def baseEnd_7571388 : Nat := 3887761265683928143329827

theorem tailTrace_7571388 : CollatzResearch.WordTrace tailWord_7571388 prefixEnd_7571388 3887761265683928143329827 := by
  unfold tailWord_7571388
  simp only [CollatzResearch.WordTrace]
  refine ⟨138075603547080920483673409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184100804729441227311564545 138075603547080920483673409)
  ·
    refine ⟨103556702660310690362755057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138075603547080920483673409 103556702660310690362755057)
    ·
      refine ⟨77667526995233017772066293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103556702660310690362755057 77667526995233017772066293)
      ·
        refine ⟨7281330655803095416131215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77667526995233017772066293 7281330655803095416131215)
        ·
          refine ⟨10921995983704643124196823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281330655803095416131215 10921995983704643124196823)
          ·
            refine ⟨16382993975556964686295235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10921995983704643124196823 16382993975556964686295235)
            ·
              refine ⟨24574490963335447029442853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16382993975556964686295235 24574490963335447029442853)
              ·
                refine ⟨4607717055625396318020535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24574490963335447029442853 4607717055625396318020535)
                ·
                  refine ⟨6911575583438094477030803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607717055625396318020535 6911575583438094477030803)
                  ·
                    refine ⟨10367363375157141715546205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6911575583438094477030803 10367363375157141715546205)
                    ·
                      refine ⟨3887761265683928143329827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367363375157141715546205 3887761265683928143329827)
                      ·
                        rfl

theorem cell23_7571388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7571388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571388 prefixEnd_7571388 := by exact prefixLift 7571388
  have htrace : WordTrace (prefixWord ++ tailWord_7571388) baseStart_7571388 baseEnd_7571388 := by
    simpa [prefixWord, tailWord_7571388, baseEnd_7571388] using wordTrace_append hprefix tailTrace_7571388
  have hstable : (prefixWord ++ tailWord_7571388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571388).length < 2 ^ (prefixWord ++ tailWord_7571388).sum := by decide
  have hdescent : baseEnd_7571388 < baseStart_7571388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571400 : List Nat := [2, 1, 3, 1, 4, 1, 3, 8]
def baseStart_7571400 : Nat := 118140960795 + 7571400 * 2 ^ 59
def prefixEnd_7571400 : Nat := 4983230072969 + 3 ^ 40 * 7571400 * 2
def baseEnd_7571400 : Nat := 143991386201917855421473

theorem tailTrace_7571400 : CollatzResearch.WordTrace tailWord_7571400 prefixEnd_7571400 143991386201917855421473 := by
  unfold tailWord_7571400
  simp only [CollatzResearch.WordTrace]
  refine ⟨138075822385059183508391827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184101096513412244677855769 138075822385059183508391827)
  ·
    refine ⟨207113733577588775262587741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138075822385059183508391827 207113733577588775262587741)
    ·
      refine ⟨77667650091595790723470403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207113733577588775262587741 77667650091595790723470403)
      ·
        refine ⟨116501475137393686085205605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77667650091595790723470403 116501475137393686085205605)
        ·
          refine ⟨21844026588261316140976051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116501475137393686085205605 21844026588261316140976051)
          ·
            refine ⟨32766039882391974211464077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21844026588261316140976051 32766039882391974211464077)
            ·
              refine ⟨12287264955896990329299029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32766039882391974211464077 12287264955896990329299029)
              ·
                refine ⟨143991386201917855421473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12287264955896990329299029 143991386201917855421473)
                ·
                  rfl

theorem cell23_7571400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 8].length) (baseStart_7571400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571400 prefixEnd_7571400 := by exact prefixLift 7571400
  have htrace : WordTrace (prefixWord ++ tailWord_7571400) baseStart_7571400 baseEnd_7571400 := by
    simpa [prefixWord, tailWord_7571400, baseEnd_7571400] using wordTrace_append hprefix tailTrace_7571400
  have hstable : (prefixWord ++ tailWord_7571400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571400).length < 2 ^ (prefixWord ++ tailWord_7571400).sum := by decide
  have hdescent : baseEnd_7571400 < baseStart_7571400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571417 : List Nat := [1, 2, 1, 2, 6, 1, 3, 7]
def baseStart_7571417 : Nat := 118140960795 + 7571417 * 2 ^ 59
def prefixEnd_7571417 : Nat := 4983230072969 + 3 ^ 40 * 7571417 * 2
def baseEnd_7571417 : Nat := 143991709504552167772859

theorem tailTrace_7571417 : CollatzResearch.WordTrace tailWord_7571417 prefixEnd_7571417 143991709504552167772859 := by
  unfold tailWord_7571417
  simp only [CollatzResearch.WordTrace]
  refine ⟨276152264811056778920152505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184101509874037852613435003 276152264811056778920152505)
  ·
    refine ⟨207114198608292584190114379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276152264811056778920152505 207114198608292584190114379)
    ·
      refine ⟨310671297912438876285171569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207114198608292584190114379 310671297912438876285171569)
      ·
        refine ⟨233003473434329157213878677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310671297912438876285171569 233003473434329157213878677)
        ·
          refine ⟨10922037817234179244400563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233003473434329157213878677 10922037817234179244400563)
          ·
            refine ⟨16383056725851268866600845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10922037817234179244400563 16383056725851268866600845)
            ·
              refine ⟨6143646272194225824975317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16383056725851268866600845 6143646272194225824975317)
              ·
                refine ⟨143991709504552167772859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6143646272194225824975317 143991709504552167772859)
                ·
                  rfl

theorem cell23_7571417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 7].length) (baseStart_7571417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571417 prefixEnd_7571417 := by exact prefixLift 7571417
  have htrace : WordTrace (prefixWord ++ tailWord_7571417) baseStart_7571417 baseEnd_7571417 := by
    simpa [prefixWord, tailWord_7571417, baseEnd_7571417] using wordTrace_append hprefix tailTrace_7571417
  have hstable : (prefixWord ++ tailWord_7571417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571417).length < 2 ^ (prefixWord ++ tailWord_7571417).sum := by decide
  have hdescent : baseEnd_7571417 < baseStart_7571417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571427 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7571427 : Nat := 118140960795 + 7571427 * 2 ^ 59
def prefixEnd_7571427 : Nat := 4983230072969 + 3 ^ 40 * 7571427 * 2
def baseEnd_7571427 : Nat := 3887781291429453490742147

theorem tailTrace_7571427 : CollatzResearch.WordTrace tailWord_7571427 prefixEnd_7571427 3887781291429453490742147 := by
  unfold tailWord_7571427
  simp only [CollatzResearch.WordTrace]
  refine ⟨276152629541020550628016535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184101753027347033752011023 276152629541020550628016535)
  ·
    refine ⟨414228944311530825942024803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276152629541020550628016535 414228944311530825942024803)
    ·
      refine ⟨621343416467296238913037205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414228944311530825942024803 621343416467296238913037205)
      ·
        refine ⟨29125472646904511199048619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 621343416467296238913037205 29125472646904511199048619)
        ·
          refine ⟨43688208970356766798572929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29125472646904511199048619 43688208970356766798572929)
          ·
            refine ⟨32766156727767575098929697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43688208970356766798572929 32766156727767575098929697)
            ·
              refine ⟨24574617545825681324197273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32766156727767575098929697 24574617545825681324197273)
              ·
                refine ⟨18430963159369260993147955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24574617545825681324197273 18430963159369260993147955)
                ·
                  refine ⟨27646444739053891489721933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18430963159369260993147955 27646444739053891489721933)
                  ·
                    refine ⟨10367416777145209308645725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27646444739053891489721933 10367416777145209308645725)
                    ·
                      refine ⟨3887781291429453490742147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367416777145209308645725 3887781291429453490742147)
                      ·
                        rfl

theorem cell23_7571427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7571427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571427 prefixEnd_7571427 := by exact prefixLift 7571427
  have htrace : WordTrace (prefixWord ++ tailWord_7571427) baseStart_7571427 baseEnd_7571427 := by
    simpa [prefixWord, tailWord_7571427, baseEnd_7571427] using wordTrace_append hprefix tailTrace_7571427
  have hstable : (prefixWord ++ tailWord_7571427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571427).length < 2 ^ (prefixWord ++ tailWord_7571427).sum := by decide
  have hdescent : baseEnd_7571427 < baseStart_7571427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571461 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 2, 1, 3]
def baseStart_7571461 : Nat := 118140960795 + 7571461 * 2 ^ 59
def prefixEnd_7571461 : Nat := 4983230072969 + 3 ^ 40 * 7571461 * 2
def baseEnd_7571461 : Nat := 3887798749771706357716991

theorem tailTrace_7571461 : CollatzResearch.WordTrace tailWord_7571461 prefixEnd_7571461 3887798749771706357716991 := by
  unfold tailWord_7571461
  simp only [CollatzResearch.WordTrace]
  refine ⟨276153869622897374434754237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184102579748598249623169491 276153869622897374434754237)
  ·
    refine ⟨103557701108586515413032839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276153869622897374434754237 103557701108586515413032839)
    ·
      refine ⟨155336551662879773119549259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103557701108586515413032839 155336551662879773119549259)
      ·
        refine ⟨233004827494319659679323889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155336551662879773119549259 233004827494319659679323889)
        ·
          refine ⟨174753620620739744759492917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233004827494319659679323889 174753620620739744759492917)
          ·
            refine ⟨16383151933194351071202461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174753620620739744759492917 16383151933194351071202461)
            ·
              refine ⟨6143681974947881651700923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16383151933194351071202461 6143681974947881651700923)
              ·
                refine ⟨9215522962421822477551385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143681974947881651700923 9215522962421822477551385)
                ·
                  refine ⟨6911642221816366858163539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9215522962421822477551385 6911642221816366858163539)
                  ·
                    refine ⟨10367463332724550287245309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6911642221816366858163539 10367463332724550287245309)
                    ·
                      refine ⟨3887798749771706357716991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367463332724550287245309 3887798749771706357716991)
                      ·
                        rfl

theorem cell23_7571461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_7571461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571461 prefixEnd_7571461 := by exact prefixLift 7571461
  have htrace : WordTrace (prefixWord ++ tailWord_7571461) baseStart_7571461 baseEnd_7571461 := by
    simpa [prefixWord, tailWord_7571461, baseEnd_7571461] using wordTrace_append hprefix tailTrace_7571461
  have hstable : (prefixWord ++ tailWord_7571461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571461).length < 2 ^ (prefixWord ++ tailWord_7571461).sum := by decide
  have hdescent : baseEnd_7571461 < baseStart_7571461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571507 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 5]
def baseStart_7571507 : Nat := 118140960795 + 7571507 * 2 ^ 59
def prefixEnd_7571507 : Nat := 4983230072969 + 3 ^ 40 * 7571507 * 2
def baseEnd_7571507 : Nat := 431980263320201464193531

theorem tailTrace_7571507 : CollatzResearch.WordTrace tailWord_7571507 prefixEnd_7571507 431980263320201464193531 := by
  unfold tailWord_7571507
  simp only [CollatzResearch.WordTrace]
  refine ⟨276155547380730724290928775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184103698253820482860619183 276155547380730724290928775)
  ·
    refine ⟨414233321071096086436393163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276155547380730724290928775 414233321071096086436393163)
    ·
      refine ⟨621349981606644129654589745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414233321071096086436393163 621349981606644129654589745)
      ·
        refine ⟨466012486204983097240942309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621349981606644129654589745 466012486204983097240942309)
        ·
          refine ⟨87377341163434330732676683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466012486204983097240942309 87377341163434330732676683)
          ·
            refine ⟨131066011745151496099015025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87377341163434330732676683 131066011745151496099015025)
            ·
              refine ⟨98299508808863622074261269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131066011745151496099015025 98299508808863622074261269)
              ·
                refine ⟨4607789475415482284730997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98299508808863622074261269 4607789475415482284730997)
                ·
                  refine ⟨431980263320201464193531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4607789475415482284730997 431980263320201464193531)
                  ·
                    rfl

theorem cell23_7571507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 5].length) (baseStart_7571507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571507 prefixEnd_7571507 := by exact prefixLift 7571507
  have htrace : WordTrace (prefixWord ++ tailWord_7571507) baseStart_7571507 baseEnd_7571507 := by
    simpa [prefixWord, tailWord_7571507, baseEnd_7571507] using wordTrace_append hprefix tailTrace_7571507
  have hstable : (prefixWord ++ tailWord_7571507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571507).length < 2 ^ (prefixWord ++ tailWord_7571507).sum := by decide
  have hdescent : baseEnd_7571507 < baseStart_7571507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571517 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7571517 : Nat := 118140960795 + 7571517 * 2 ^ 59
def prefixEnd_7571517 : Nat := 4983230072969 + 3 ^ 40 * 7571517 * 2
def baseEnd_7571517 : Nat := 3887827504688358138616733

theorem tailTrace_7571517 : CollatzResearch.WordTrace tailWord_7571517 prefixEnd_7571517 3887827504688358138616733 := by
  unfold tailWord_7571517
  simp only [CollatzResearch.WordTrace]
  refine ⟨276155912110694495998792805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184103941407129663999195203 276155912110694495998792805)
  ·
    refine ⟨51779233520755217999773651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276155912110694495998792805 51779233520755217999773651)
    ·
      refine ⟨77668850281132826999660477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51779233520755217999773651 77668850281132826999660477)
      ·
        refine ⟨29125818855424810124872679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77668850281132826999660477 29125818855424810124872679)
        ·
          refine ⟨43688728283137215187309019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29125818855424810124872679 43688728283137215187309019)
          ·
            refine ⟨65533092424705822780963529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43688728283137215187309019 65533092424705822780963529)
            ·
              refine ⟨49149819318529367085722647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65533092424705822780963529 49149819318529367085722647)
              ·
                refine ⟨73724728977794050628583971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49149819318529367085722647 73724728977794050628583971)
                ·
                  refine ⟨110587093466691075942875957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73724728977794050628583971 110587093466691075942875957)
                  ·
                    refine ⟨10367540012502288369644621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110587093466691075942875957 10367540012502288369644621)
                    ·
                      refine ⟨3887827504688358138616733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367540012502288369644621 3887827504688358138616733)
                      ·
                        rfl

theorem cell23_7571517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7571517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571517 prefixEnd_7571517 := by exact prefixLift 7571517
  have htrace : WordTrace (prefixWord ++ tailWord_7571517) baseStart_7571517 baseEnd_7571517 := by
    simpa [prefixWord, tailWord_7571517, baseEnd_7571517] using wordTrace_append hprefix tailTrace_7571517
  have hstable : (prefixWord ++ tailWord_7571517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571517).length < 2 ^ (prefixWord ++ tailWord_7571517).sum := by decide
  have hdescent : baseEnd_7571517 < baseStart_7571517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571530 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_7571530 : Nat := 118140960795 + 7571530 * 2 ^ 59
def prefixEnd_7571530 : Nat := 4983230072969 + 3 ^ 40 * 7571530 * 2
def baseEnd_7571530 : Nat := 3887834179936866587754173

theorem tailTrace_7571530 : CollatzResearch.WordTrace tailWord_7571530 prefixEnd_7571530 3887834179936866587754173 := by
  unfold tailWord_7571530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69039096564911849804754011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184104257506431599479344029 69039096564911849804754011)
  ·
    refine ⟨103558644847367774707131017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69039096564911849804754011 103558644847367774707131017)
    ·
      refine ⟨77668983635525831030348263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103558644847367774707131017 77668983635525831030348263)
      ·
        refine ⟨116503475453288746545522395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77668983635525831030348263 116503475453288746545522395)
        ·
          refine ⟨174755213179933119818283593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116503475453288746545522395 174755213179933119818283593)
          ·
            refine ⟨131066409884949839863712695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174755213179933119818283593 131066409884949839863712695)
            ·
              refine ⟨196599614827424759795569043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131066409884949839863712695 196599614827424759795569043)
              ·
                refine ⟨294899422241137139693353565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196599614827424759795569043 294899422241137139693353565)
                ·
                  refine ⟨110587283340426427385007587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294899422241137139693353565 110587283340426427385007587)
                  ·
                    refine ⟨165880925010639641077511381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110587283340426427385007587 165880925010639641077511381)
                    ·
                      refine ⟨3887834179936866587754173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165880925010639641077511381 3887834179936866587754173)
                      ·
                        rfl

theorem cell23_7571530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_7571530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571530 prefixEnd_7571530 := by exact prefixLift 7571530
  have htrace : WordTrace (prefixWord ++ tailWord_7571530) baseStart_7571530 baseEnd_7571530 := by
    simpa [prefixWord, tailWord_7571530, baseEnd_7571530] using wordTrace_append hprefix tailTrace_7571530
  have hstable : (prefixWord ++ tailWord_7571530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571530).length < 2 ^ (prefixWord ++ tailWord_7571530).sum := by decide
  have hdescent : baseEnd_7571530 < baseStart_7571530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571594 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_7571594 : Nat := 118140960795 + 7571594 * 2 ^ 59
def prefixEnd_7571594 : Nat := 4983230072969 + 3 ^ 40 * 7571594 * 2
def baseEnd_7571594 : Nat := 3887867042698754337353879

theorem tailTrace_7571594 : CollatzResearch.WordTrace tailWord_7571594 prefixEnd_7571594 3887867042698754337353879 := by
  unfold tailWord_7571594
  simp only [CollatzResearch.WordTrace]
  refine ⟨69039680132853884537336459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184105813687610358766230557 69039680132853884537336459)
  ·
    refine ⟨103559520199280826806004689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69039680132853884537336459 103559520199280826806004689)
    ·
      refine ⟨77669640149460620104503517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103559520199280826806004689 77669640149460620104503517)
      ·
        refine ⟨29126115056047732539188819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77669640149460620104503517 29126115056047732539188819)
        ·
          refine ⟨43689172584071598808783229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29126115056047732539188819 43689172584071598808783229)
          ·
            refine ⟨16383439719026849553293711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43689172584071598808783229 16383439719026849553293711)
            ·
              refine ⟨24575159578540274329940567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16383439719026849553293711 24575159578540274329940567)
              ·
                refine ⟨36862739367810411494910851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24575159578540274329940567 36862739367810411494910851)
                ·
                  refine ⟨55294109051715617242366277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36862739367810411494910851 55294109051715617242366277)
                  ·
                    refine ⟨10367645447196678232943677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55294109051715617242366277 10367645447196678232943677)
                    ·
                      refine ⟨3887867042698754337353879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367645447196678232943677 3887867042698754337353879)
                      ·
                        rfl

theorem cell23_7571594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_7571594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571594 prefixEnd_7571594 := by exact prefixLift 7571594
  have htrace : WordTrace (prefixWord ++ tailWord_7571594) baseStart_7571594 baseEnd_7571594 := by
    simpa [prefixWord, tailWord_7571594, baseEnd_7571594] using wordTrace_append hprefix tailTrace_7571594
  have hstable : (prefixWord ++ tailWord_7571594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571594).length < 2 ^ (prefixWord ++ tailWord_7571594).sum := by decide
  have hdescent : baseEnd_7571594 < baseStart_7571594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571617 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7571617 : Nat := 118140960795 + 7571617 * 2 ^ 59
def prefixEnd_7571617 : Nat := 4983230072969 + 3 ^ 40 * 7571617 * 2
def baseEnd_7571617 : Nat := 3887878852753807747366273

theorem tailTrace_7571617 : CollatzResearch.WordTrace tailWord_7571617 prefixEnd_7571617 3887878852753807747366273 := by
  unfold tailWord_7571617
  simp only [CollatzResearch.WordTrace]
  refine ⟨276159559410332213077433105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184106372940221475384955403 276159559410332213077433105)
  ·
    refine ⟨207119669557749159808074829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276159559410332213077433105 207119669557749159808074829)
    ·
      refine ⟨77669876084155934928028061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207119669557749159808074829 77669876084155934928028061)
      ·
        refine ⟨29126203531558475598010523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77669876084155934928028061 29126203531558475598010523)
        ·
          refine ⟨43689305297337713397015785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29126203531558475598010523 43689305297337713397015785)
          ·
            refine ⟨32766978973003285047761839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43689305297337713397015785 32766978973003285047761839)
            ·
              refine ⟨49150468459504927571642759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32766978973003285047761839 49150468459504927571642759)
              ·
                refine ⟨73725702689257391357464139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49150468459504927571642759 73725702689257391357464139)
                ·
                  refine ⟨110588554033886087036196209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73725702689257391357464139 110588554033886087036196209)
                  ·
                    refine ⟨82941415525414565277147157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110588554033886087036196209 82941415525414565277147157)
                    ·
                      refine ⟨3887878852753807747366273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82941415525414565277147157 3887878852753807747366273)
                      ·
                        rfl

theorem cell23_7571617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7571617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571617 prefixEnd_7571617 := by exact prefixLift 7571617
  have htrace : WordTrace (prefixWord ++ tailWord_7571617) baseStart_7571617 baseEnd_7571617 := by
    simpa [prefixWord, tailWord_7571617, baseEnd_7571617] using wordTrace_append hprefix tailTrace_7571617
  have hstable : (prefixWord ++ tailWord_7571617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571617).length < 2 ^ (prefixWord ++ tailWord_7571617).sum := by decide
  have hdescent : baseEnd_7571617 < baseStart_7571617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571618 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7571618 : Nat := 118140960795 + 7571618 * 2 ^ 59
def prefixEnd_7571618 : Nat := 4983230072969 + 3 ^ 40 * 7571618 * 2
def baseEnd_7571618 : Nat := 1295959788744820747817923

theorem tailTrace_7571618 : CollatzResearch.WordTrace tailWord_7571618 prefixEnd_7571618 1295959788744820747817923 := by
  unfold tailWord_7571618
  simp only [CollatzResearch.WordTrace]
  refine ⟨69039898970832147562054877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184106397255552393498813005 69039898970832147562054877)
  ·
    refine ⟨25889962114062055335770579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69039898970832147562054877 25889962114062055335770579)
    ·
      refine ⟨38834943171093083003655869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25889962114062055335770579 38834943171093083003655869)
      ·
        refine ⟨14563103689159906126370951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38834943171093083003655869 14563103689159906126370951)
        ·
          refine ⟨21844655533739859189556427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14563103689159906126370951 21844655533739859189556427)
          ·
            refine ⟨32766983300609788784334641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21844655533739859189556427 32766983300609788784334641)
            ·
              refine ⟨24575237475457341588250981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32766983300609788784334641 24575237475457341588250981)
              ·
                refine ⟨4607857026648251547797059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24575237475457341588250981 4607857026648251547797059)
                ·
                  refine ⟨6911785539972377321695589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607857026648251547797059 6911785539972377321695589)
                  ·
                    refine ⟨1295959788744820747817923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6911785539972377321695589 1295959788744820747817923)
                    ·
                      rfl

theorem cell23_7571618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7571618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571618 prefixEnd_7571618 := by exact prefixLift 7571618
  have htrace : WordTrace (prefixWord ++ tailWord_7571618) baseStart_7571618 baseEnd_7571618 := by
    simpa [prefixWord, tailWord_7571618, baseEnd_7571618] using wordTrace_append hprefix tailTrace_7571618
  have hstable : (prefixWord ++ tailWord_7571618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571618).length < 2 ^ (prefixWord ++ tailWord_7571618).sum := by decide
  have hdescent : baseEnd_7571618 < baseStart_7571618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571634 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_7571634 : Nat := 118140960795 + 7571634 * 2 ^ 59
def prefixEnd_7571634 : Nat := 4983230072969 + 3 ^ 40 * 7571634 * 2
def baseEnd_7571634 : Nat := 3887887581924934180853695

theorem tailTrace_7571634 : CollatzResearch.WordTrace tailWord_7571634 prefixEnd_7571634 3887887581924934180853695 := by
  unfold tailWord_7571634
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040044862817656245200489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184106786300847083320534637 69040044862817656245200489)
  ·
    refine ⟨51780033647113242183900367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69040044862817656245200489 51780033647113242183900367)
    ·
      refine ⟨77670050470669863275850551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51780033647113242183900367 77670050470669863275850551)
      ·
        refine ⟨116505075706004794913775827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77670050470669863275850551 116505075706004794913775827)
        ·
          refine ⟨174757613559007192370663741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116505075706004794913775827 174757613559007192370663741)
          ·
            refine ⟨65534105084627697138998903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174757613559007192370663741 65534105084627697138998903)
            ·
              refine ⟨98301157626941545708498355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65534105084627697138998903 98301157626941545708498355)
              ·
                refine ⟨147451736440412318562747533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98301157626941545708498355 147451736440412318562747533)
                ·
                  refine ⟨55294401165154619461030325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147451736440412318562747533 55294401165154619461030325)
                  ·
                    refine ⟨5183850109233245574471593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55294401165154619461030325 5183850109233245574471593)
                    ·
                      refine ⟨3887887581924934180853695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5183850109233245574471593 3887887581924934180853695)
                      ·
                        rfl

theorem cell23_7571634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_7571634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571634 prefixEnd_7571634 := by exact prefixLift 7571634
  have htrace : WordTrace (prefixWord ++ tailWord_7571634) baseStart_7571634 baseEnd_7571634 := by
    simpa [prefixWord, tailWord_7571634, baseEnd_7571634] using wordTrace_append hprefix tailTrace_7571634
  have hstable : (prefixWord ++ tailWord_7571634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571634).length < 2 ^ (prefixWord ++ tailWord_7571634).sum := by decide
  have hdescent : baseEnd_7571634 < baseStart_7571634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571674 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_7571674 : Nat := 118140960795 + 7571674 * 2 ^ 59
def prefixEnd_7571674 : Nat := 4983230072969 + 3 ^ 40 * 7571674 * 2
def baseEnd_7571674 : Nat := 1295969373717038008117837

theorem tailTrace_7571674 : CollatzResearch.WordTrace tailWord_7571674 prefixEnd_7571674 1295969373717038008117837 := by
  unfold tailWord_7571674
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040409592781427953064519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184107758914083807874838717 69040409592781427953064519)
  ·
    refine ⟨103560614389172141929596779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69040409592781427953064519 103560614389172141929596779)
    ·
      refine ⟨155340921583758212894395169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103560614389172141929596779 155340921583758212894395169)
      ·
        refine ⟨116505691187818659670796377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155340921583758212894395169 116505691187818659670796377)
        ·
          refine ⟨87379268390863994753097283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116505691187818659670796377 87379268390863994753097283)
          ·
            refine ⟨131068902586295992129645925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87379268390863994753097283 131068902586295992129645925)
            ·
              refine ⟨24575419234930498524308611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131068902586295992129645925 24575419234930498524308611)
              ·
                refine ⟨36863128852395747786462917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24575419234930498524308611 36863128852395747786462917)
                ·
                  refine ⟨6911836659824202709961797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36863128852395747786462917 6911836659824202709961797)
                  ·
                    refine ⟨1295969373717038008117837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6911836659824202709961797 1295969373717038008117837)
                    ·
                      rfl

theorem cell23_7571674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_7571674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571674 prefixEnd_7571674 := by exact prefixLift 7571674
  have htrace : WordTrace (prefixWord ++ tailWord_7571674) baseStart_7571674 baseEnd_7571674 := by
    simpa [prefixWord, tailWord_7571674, baseEnd_7571674] using wordTrace_append hprefix tailTrace_7571674
  have hstable : (prefixWord ++ tailWord_7571674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571674).length < 2 ^ (prefixWord ++ tailWord_7571674).sum := by decide
  have hdescent : baseEnd_7571674 < baseStart_7571674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571682 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_7571682 : Nat := 118140960795 + 7571682 * 2 ^ 59
def prefixEnd_7571682 : Nat := 4983230072969 + 3 ^ 40 * 7571682 * 2
def baseEnd_7571682 : Nat := 431990247666261110339275

theorem tailTrace_7571682 : CollatzResearch.WordTrace tailWord_7571682 prefixEnd_7571682 431990247666261110339275 := by
  unfold tailWord_7571682
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040482538774182294637325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184107953436731152785699533 69040482538774182294637325)
  ·
    refine ⟨25890180952040318360488997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69040482538774182294637325 25890180952040318360488997)
    ·
      refine ⟨4854408928507559692591687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25890180952040318360488997 4854408928507559692591687)
      ·
        refine ⟨7281613392761339538887531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854408928507559692591687 7281613392761339538887531)
        ·
          refine ⟨10922420089142009308331297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281613392761339538887531 10922420089142009308331297)
          ·
            refine ⟨8191815066856506981248473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10922420089142009308331297 8191815066856506981248473)
            ·
              refine ⟨6143861300142380235936355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8191815066856506981248473 6143861300142380235936355)
              ·
                refine ⟨9215791950213570353904533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143861300142380235936355 9215791950213570353904533)
                ·
                  refine ⟨431990247666261110339275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9215791950213570353904533 431990247666261110339275)
                  ·
                    rfl

theorem cell23_7571682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_7571682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571682 prefixEnd_7571682 := by exact prefixLift 7571682
  have htrace : WordTrace (prefixWord ++ tailWord_7571682) baseStart_7571682 baseEnd_7571682 := by
    simpa [prefixWord, tailWord_7571682, baseEnd_7571682] using wordTrace_append hprefix tailTrace_7571682
  have hstable : (prefixWord ++ tailWord_7571682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571682).length < 2 ^ (prefixWord ++ tailWord_7571682).sum := by decide
  have hdescent : baseEnd_7571682 < baseStart_7571682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571684 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_7571684 : Nat := 118140960795 + 7571684 * 2 ^ 59
def prefixEnd_7571684 : Nat := 4983230072969 + 3 ^ 40 * 7571684 * 2
def baseEnd_7571684 : Nat := 3887913255957658985228465

theorem tailTrace_7571684 : CollatzResearch.WordTrace tailWord_7571684 prefixEnd_7571684 3887913255957658985228465 := by
  unfold tailWord_7571684
  simp only [CollatzResearch.WordTrace]
  refine ⟨138081001550544741760061053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184108002067392989013414737 138081001550544741760061053)
  ·
    refine ⟨51780375581454278160022895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138081001550544741760061053 51780375581454278160022895)
    ·
      refine ⟨77670563372181417240034343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51780375581454278160022895 77670563372181417240034343)
      ·
        refine ⟨116505845058272125860051515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77670563372181417240034343 116505845058272125860051515)
        ·
          refine ⟨174758767587408188790077273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116505845058272125860051515 174758767587408188790077273)
          ·
            refine ⟨131069075690556141592557955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174758767587408188790077273 131069075690556141592557955)
            ·
              refine ⟨196603613535834212388836933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131069075690556141592557955 196603613535834212388836933)
              ·
                refine ⟨36863177537968914822906925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196603613535834212388836933 36863177537968914822906925)
                ·
                  refine ⟨13823691576738343058590097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36863177537968914822906925 13823691576738343058590097)
                  ·
                    refine ⟨10367768682553757293942573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13823691576738343058590097 10367768682553757293942573)
                    ·
                      refine ⟨3887913255957658985228465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367768682553757293942573 3887913255957658985228465)
                      ·
                        rfl

theorem cell23_7571684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_7571684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571684 prefixEnd_7571684 := by exact prefixLift 7571684
  have htrace : WordTrace (prefixWord ++ tailWord_7571684) baseStart_7571684 baseEnd_7571684 := by
    simpa [prefixWord, tailWord_7571684, baseEnd_7571684] using wordTrace_append hprefix tailTrace_7571684
  have hstable : (prefixWord ++ tailWord_7571684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571684).length < 2 ^ (prefixWord ++ tailWord_7571684).sum := by decide
  have hdescent : baseEnd_7571684 < baseStart_7571684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571694 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7571694 : Nat := 118140960795 + 7571694 * 2 ^ 59
def prefixEnd_7571694 : Nat := 4983230072969 + 3 ^ 40 * 7571694 * 2
def baseEnd_7571694 : Nat := 3887918390764203946103419

theorem tailTrace_7571694 : CollatzResearch.WordTrace tailWord_7571694 prefixEnd_7571694 3887918390764203946103419 := by
  unfold tailWord_7571694
  simp only [CollatzResearch.WordTrace]
  refine ⟨34520295978881656903498267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184108245220702170151990757 34520295978881656903498267)
  ·
    refine ⟨51780443968322485355247401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34520295978881656903498267 51780443968322485355247401)
    ·
      refine ⟨38835332976241864016435551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51780443968322485355247401 38835332976241864016435551)
      ·
        refine ⟨58252999464362796024653327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38835332976241864016435551 58252999464362796024653327)
        ·
          refine ⟨87379499196544194036979991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58252999464362796024653327 87379499196544194036979991)
          ·
            refine ⟨131069248794816291055469987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87379499196544194036979991 131069248794816291055469987)
            ·
              refine ⟨196603873192224436583204981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131069248794816291055469987 196603873192224436583204981)
              ·
                refine ⟨18431613111771040929675467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196603873192224436583204981 18431613111771040929675467)
                ·
                  refine ⟨27647419667656561394513201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18431613111771040929675467 27647419667656561394513201)
                  ·
                    refine ⟨20735564750742421045884901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27647419667656561394513201 20735564750742421045884901)
                    ·
                      refine ⟨3887918390764203946103419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20735564750742421045884901 3887918390764203946103419)
                      ·
                        rfl

theorem cell23_7571694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7571694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571694 prefixEnd_7571694 := by exact prefixLift 7571694
  have htrace : WordTrace (prefixWord ++ tailWord_7571694) baseStart_7571694 baseEnd_7571694 := by
    simpa [prefixWord, tailWord_7571694, baseEnd_7571694] using wordTrace_append hprefix tailTrace_7571694
  have hstable : (prefixWord ++ tailWord_7571694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571694).length < 2 ^ (prefixWord ++ tailWord_7571694).sum := by decide
  have hdescent : baseEnd_7571694 < baseStart_7571694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571698 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_7571698 : Nat := 118140960795 + 7571698 * 2 ^ 59
def prefixEnd_7571698 : Nat := 4983230072969 + 3 ^ 40 * 7571698 * 2
def baseEnd_7571698 : Nat := 3887920444686821930453401

theorem tailTrace_7571698 : CollatzResearch.WordTrace tailWord_7571698 prefixEnd_7571698 3887920444686821930453401 := by
  unfold tailWord_7571698
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040628430759690977782937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184108342482025842607421165 69040628430759690977782937)
  ·
    refine ⟨51780471323069768233337203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69040628430759690977782937 51780471323069768233337203)
    ·
      refine ⟨77670706984604652350005805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51780471323069768233337203 77670706984604652350005805)
      ·
        refine ⟨29126515119226744631252177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77670706984604652350005805 29126515119226744631252177)
        ·
          refine ⟨21844886339420058473439133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29126515119226744631252177 21844886339420058473439133)
          ·
            refine ⟨8191832377282521927539675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21844886339420058473439133 8191832377282521927539675)
            ·
              refine ⟨12287748565923782891309513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8191832377282521927539675 12287748565923782891309513)
              ·
                refine ⟨9215811424442837168482135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12287748565923782891309513 9215811424442837168482135)
                ·
                  refine ⟨13823717136664255752723203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9215811424442837168482135 13823717136664255752723203)
                  ·
                    refine ⟨20735575704996383629084805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13823717136664255752723203 20735575704996383629084805)
                    ·
                      refine ⟨3887920444686821930453401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20735575704996383629084805 3887920444686821930453401)
                      ·
                        rfl

theorem cell23_7571698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_7571698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571698 prefixEnd_7571698 := by exact prefixLift 7571698
  have htrace : WordTrace (prefixWord ++ tailWord_7571698) baseStart_7571698 baseEnd_7571698 := by
    simpa [prefixWord, tailWord_7571698, baseEnd_7571698] using wordTrace_append hprefix tailTrace_7571698
  have hstable : (prefixWord ++ tailWord_7571698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571698).length < 2 ^ (prefixWord ++ tailWord_7571698).sum := by decide
  have hdescent : baseEnd_7571698 < baseStart_7571698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571727 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_7571727 : Nat := 118140960795 + 7571727 * 2 ^ 59
def prefixEnd_7571727 : Nat := 4983230072969 + 3 ^ 40 * 7571727 * 2
def baseEnd_7571727 : Nat := 3887935335625802316990767

theorem tailTrace_7571727 : CollatzResearch.WordTrace tailWord_7571727 prefixEnd_7571727 3887935335625802316990767 := by
  unfold tailWord_7571727
  simp only [CollatzResearch.WordTrace]
  refine ⟨276163571439933701863937435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184109047626622467909291623 276163571439933701863937435)
  ·
    refine ⟨414245357159900552795906153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276163571439933701863937435 414245357159900552795906153)
    ·
      refine ⟨310684017869925414596929615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414245357159900552795906153 310684017869925414596929615)
      ·
        refine ⟨466026026804888121895394423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310684017869925414596929615 466026026804888121895394423)
        ·
          refine ⟨699039040207332182843091635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466026026804888121895394423 699039040207332182843091635)
          ·
            refine ⟨1048558560310998274264637453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699039040207332182843091635 1048558560310998274264637453)
            ·
              refine ⟨393209460116624352849239045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1048558560310998274264637453 393209460116624352849239045)
              ·
                refine ⟨73726773771867066159232321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393209460116624352849239045 73726773771867066159232321)
                ·
                  refine ⟨55295080328900299619424241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73726773771867066159232321 55295080328900299619424241)
                  ·
                    refine ⟨41471310246675224714568181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55295080328900299619424241 41471310246675224714568181)
                    ·
                      refine ⟨3887935335625802316990767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41471310246675224714568181 3887935335625802316990767)
                      ·
                        rfl

theorem cell23_7571727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_7571727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571727 prefixEnd_7571727 := by exact prefixLift 7571727
  have htrace : WordTrace (prefixWord ++ tailWord_7571727) baseStart_7571727 baseEnd_7571727 := by
    simpa [prefixWord, tailWord_7571727, baseEnd_7571727] using wordTrace_append hprefix tailTrace_7571727
  have hstable : (prefixWord ++ tailWord_7571727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571727).length < 2 ^ (prefixWord ++ tailWord_7571727).sum := by decide
  have hdescent : baseEnd_7571727 < baseStart_7571727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571748 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_7571748 : Nat := 118140960795 + 7571748 * 2 ^ 59
def prefixEnd_7571748 : Nat := 4983230072969 + 3 ^ 40 * 7571748 * 2
def baseEnd_7571748 : Nat := 3887946118719546734828171

theorem tailTrace_7571748 : CollatzResearch.WordTrace tailWord_7571748 prefixEnd_7571748 3887946118719546734828171 := by
  unfold tailWord_7571748
  simp only [CollatzResearch.WordTrace]
  refine ⟨138082168686428811225225949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184109558248571748300301265 138082168686428811225225949)
  ·
    refine ⟨51780813257410804209459731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138082168686428811225225949 51780813257410804209459731)
    ·
      refine ⟨77671219886116206314189597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51780813257410804209459731 77671219886116206314189597)
      ·
        refine ⟨29126707457293577367821099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77671219886116206314189597 29126707457293577367821099)
        ·
          refine ⟨43690061185940366051731649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29126707457293577367821099 43690061185940366051731649)
          ·
            refine ⟨32767545889455274538798737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43690061185940366051731649 32767545889455274538798737)
            ·
              refine ⟨24575659417091455904099053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32767545889455274538798737 24575659417091455904099053)
              ·
                refine ⟨9215872281409295964037145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24575659417091455904099053 9215872281409295964037145)
                ·
                  refine ⟨6911904211056971973027859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9215872281409295964037145 6911904211056971973027859)
                  ·
                    refine ⟨10367856316585457959541789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6911904211056971973027859 10367856316585457959541789)
                    ·
                      refine ⟨3887946118719546734828171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10367856316585457959541789 3887946118719546734828171)
                      ·
                        rfl

theorem cell23_7571748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_7571748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571748 prefixEnd_7571748 := by exact prefixLift 7571748
  have htrace : WordTrace (prefixWord ++ tailWord_7571748) baseStart_7571748 baseEnd_7571748 := by
    simpa [prefixWord, tailWord_7571748, baseEnd_7571748] using wordTrace_append hprefix tailTrace_7571748
  have hstable : (prefixWord ++ tailWord_7571748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571748).length < 2 ^ (prefixWord ++ tailWord_7571748).sum := by decide
  have hdescent : baseEnd_7571748 < baseStart_7571748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571784 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_7571784 : Nat := 118140960795 + 7571784 * 2 ^ 59
def prefixEnd_7571784 : Nat := 4983230072969 + 3 ^ 40 * 7571784 * 2
def baseEnd_7571784 : Nat := 3887964604023108593978005

theorem tailTrace_7571784 : CollatzResearch.WordTrace tailWord_7571784 prefixEnd_7571784 3887964604023108593978005 := by
  unfold tailWord_7571784
  simp only [CollatzResearch.WordTrace]
  refine ⟨138082825200363600299381203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184110433600484800399174937 138082825200363600299381203)
  ·
    refine ⟨207124237800545400449071805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138082825200363600299381203 207124237800545400449071805)
    ·
      refine ⟨77671589175204525168401927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207124237800545400449071805 77671589175204525168401927)
      ·
        refine ⟨116507383762806787752602891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77671589175204525168401927 116507383762806787752602891)
        ·
          refine ⟨174761075644210181628904337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116507383762806787752602891 174761075644210181628904337)
          ·
            refine ⟨131070806733157636221678253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174761075644210181628904337 131070806733157636221678253)
            ·
              refine ⟨49151552524934113583129345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131070806733157636221678253 49151552524934113583129345)
              ·
                refine ⟨36863664393700585187347009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49151552524934113583129345 36863664393700585187347009)
                ·
                  refine ⟨27647748295275438890510257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36863664393700585187347009 27647748295275438890510257)
                  ·
                    refine ⟨20735811221456579167882693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27647748295275438890510257 20735811221456579167882693)
                    ·
                      refine ⟨3887964604023108593978005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20735811221456579167882693 3887964604023108593978005)
                      ·
                        rfl

theorem cell23_7571784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_7571784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571784 prefixEnd_7571784 := by exact prefixLift 7571784
  have htrace : WordTrace (prefixWord ++ tailWord_7571784) baseStart_7571784 baseEnd_7571784 := by
    simpa [prefixWord, tailWord_7571784, baseEnd_7571784] using wordTrace_append hprefix tailTrace_7571784
  have hstable : (prefixWord ++ tailWord_7571784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571784).length < 2 ^ (prefixWord ++ tailWord_7571784).sum := by decide
  have hdescent : baseEnd_7571784 < baseStart_7571784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571787 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_7571787 : Nat := 118140960795 + 7571787 * 2 ^ 59
def prefixEnd_7571787 : Nat := 4983230072969 + 3 ^ 40 * 7571787 * 2
def baseEnd_7571787 : Nat := 3887966144465072082240491

theorem tailTrace_7571787 : CollatzResearch.WordTrace tailWord_7571787 prefixEnd_7571787 3887966144465072082240491 := by
  unfold tailWord_7571787
  simp only [CollatzResearch.WordTrace]
  refine ⟨276165759819716332111121615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184110506546477554740747743 276165759819716332111121615)
  ·
    refine ⟨414248639729574498166682423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276165759819716332111121615 414248639729574498166682423)
    ·
      refine ⟨621372959594361747250023635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414248639729574498166682423 621372959594361747250023635)
      ·
        refine ⟨932059439391542620875035453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621372959594361747250023635 932059439391542620875035453)
        ·
          refine ⟨349522289771828482828138295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 932059439391542620875035453 349522289771828482828138295)
          ·
            refine ⟨524283434657742724242207443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349522289771828482828138295 524283434657742724242207443)
            ·
              refine ⟨786425151986614086363311165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524283434657742724242207443 786425151986614086363311165)
              ·
                refine ⟨294909431994980282386241687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786425151986614086363311165 294909431994980282386241687)
                ·
                  refine ⟨442364147992470423579362531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294909431994980282386241687 442364147992470423579362531)
                  ·
                    refine ⟨663546221988705635369043797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 442364147992470423579362531 663546221988705635369043797)
                    ·
                      refine ⟨3887966144465072082240491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 663546221988705635369043797 3887966144465072082240491)
                      ·
                        rfl

theorem cell23_7571787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_7571787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571787 prefixEnd_7571787 := by exact prefixLift 7571787
  have htrace : WordTrace (prefixWord ++ tailWord_7571787) baseStart_7571787 baseEnd_7571787 := by
    simpa [prefixWord, tailWord_7571787, baseEnd_7571787] using wordTrace_append hprefix tailTrace_7571787
  have hstable : (prefixWord ++ tailWord_7571787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571787).length < 2 ^ (prefixWord ++ tailWord_7571787).sum := by decide
  have hdescent : baseEnd_7571787 < baseStart_7571787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
