import V185TrunkScan23Chunk0951

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5635824 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 5, 4]
def baseStart_5635824 : Nat := 118140960795 + 5635824 * 2 ^ 59
def prefixEnd_5635824 : Nat := 4983230072969 + 3 ^ 40 * 5635824 * 2
def baseEnd_5635824 : Nat := 964628865381621015460441

theorem tailTrace_5635824 : CollatzResearch.WordTrace tailWord_5635824 prefixEnd_5635824 964628865381621015460441 := by
  unfold tailWord_5635824
  simp only [CollatzResearch.WordTrace]
  refine ⟨102777694167189822477005263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137036925556253096636007017 102777694167189822477005263)
  ·
    refine ⟨154166541250784733715507895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102777694167189822477005263 154166541250784733715507895)
    ·
      refine ⟨231249811876177100573261843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154166541250784733715507895 231249811876177100573261843)
      ·
        refine ⟨346874717814265650859892765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231249811876177100573261843 346874717814265650859892765)
        ·
          refine ⟨130078019180349619072459787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346874717814265650859892765 130078019180349619072459787)
          ·
            refine ⟨195117028770524428608689681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130078019180349619072459787 195117028770524428608689681)
            ·
              refine ⟨146337771577893321456517261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195117028770524428608689681 146337771577893321456517261)
              ·
                refine ⟨54876664341709995546193973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146337771577893321456517261 54876664341709995546193973)
                ·
                  refine ⟨5144687282035312082455685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54876664341709995546193973 5144687282035312082455685)
                  ·
                    refine ⟨964628865381621015460441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144687282035312082455685 964628865381621015460441)
                    ·
                      rfl

theorem cell23_5635824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_5635824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635824 prefixEnd_5635824 := by exact prefixLift 5635824
  have htrace : WordTrace (prefixWord ++ tailWord_5635824) baseStart_5635824 baseEnd_5635824 := by
    simpa [prefixWord, tailWord_5635824, baseEnd_5635824] using wordTrace_append hprefix tailTrace_5635824
  have hstable : (prefixWord ++ tailWord_5635824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635824).length < 2 ^ (prefixWord ++ tailWord_5635824).sum := by decide
  have hdescent : baseEnd_5635824 < baseStart_5635824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635828 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5635828 : Nat := 118140960795 + 5635828 * 2 ^ 59
def prefixEnd_5635828 : Nat := 4983230072969 + 3 ^ 40 * 5635828 * 2
def baseEnd_5635828 : Nat := 964629550022493676910435

theorem tailTrace_5635828 : CollatzResearch.WordTrace tailWord_5635828 prefixEnd_5635828 964629550022493676910435 := by
  unfold tailWord_5635828
  simp only [CollatzResearch.WordTrace]
  refine ⟨102777767113182576818578069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137037022817576769091437425 102777767113182576818578069)
  ·
    refine ⟨4817707833430433288370847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102777767113182576818578069 4817707833430433288370847)
    ·
      refine ⟨7226561750145649932556271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4817707833430433288370847 7226561750145649932556271)
      ·
        refine ⟨10839842625218474898834407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7226561750145649932556271 10839842625218474898834407)
        ·
          refine ⟨16259763937827712348251611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839842625218474898834407 16259763937827712348251611)
          ·
            refine ⟨24389645906741568522377417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16259763937827712348251611 24389645906741568522377417)
            ·
              refine ⟨18292234430056176391783063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24389645906741568522377417 18292234430056176391783063)
              ·
                refine ⟨27438351645084264587674595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18292234430056176391783063 27438351645084264587674595)
                ·
                  refine ⟨41157527467626396881511893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27438351645084264587674595 41157527467626396881511893)
                  ·
                    refine ⟨964629550022493676910435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41157527467626396881511893 964629550022493676910435)
                    ·
                      rfl

theorem cell23_5635828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5635828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635828 prefixEnd_5635828 := by exact prefixLift 5635828
  have htrace : WordTrace (prefixWord ++ tailWord_5635828) baseStart_5635828 baseEnd_5635828 := by
    simpa [prefixWord, tailWord_5635828, baseEnd_5635828] using wordTrace_append hprefix tailTrace_5635828
  have hstable : (prefixWord ++ tailWord_5635828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635828).length < 2 ^ (prefixWord ++ tailWord_5635828).sum := by decide
  have hdescent : baseEnd_5635828 < baseStart_5635828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635854 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_5635854 : Nat := 118140960795 + 5635854 * 2 ^ 59
def prefixEnd_5635854 : Nat := 4983230072969 + 3 ^ 40 * 5635854 * 2
def baseEnd_5635854 : Nat := 321544666729388658778465

theorem tailTrace_5635854 : CollatzResearch.WordTrace tailWord_5635854 prefixEnd_5635854 321544666729388658778465 := by
  unfold tailWord_5635854
  simp only [CollatzResearch.WordTrace]
  refine ⟨25694560315533870009700327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137037655016180640051735077 25694560315533870009700327)
  ·
    refine ⟨38541840473300805014550491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25694560315533870009700327 38541840473300805014550491)
    ·
      refine ⟨57812760709951207521825737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38541840473300805014550491 57812760709951207521825737)
      ·
        refine ⟨43359570532463405641369303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57812760709951207521825737 43359570532463405641369303)
        ·
          refine ⟨65039355798695108462053955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43359570532463405641369303 65039355798695108462053955)
          ·
            refine ⟨97559033698042662693080933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65039355798695108462053955 97559033698042662693080933)
            ·
              refine ⟨18292318818382999254952675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97559033698042662693080933 18292318818382999254952675)
              ·
                refine ⟨27438478227574498882429013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18292318818382999254952675 27438478227574498882429013)
                ·
                  refine ⟨321544666729388658778465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27438478227574498882429013 321544666729388658778465)
                  ·
                    rfl

theorem cell23_5635854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_5635854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635854 prefixEnd_5635854 := by exact prefixLift 5635854
  have htrace : WordTrace (prefixWord ++ tailWord_5635854) baseStart_5635854 baseEnd_5635854 := by
    simpa [prefixWord, tailWord_5635854, baseEnd_5635854] using wordTrace_append hprefix tailTrace_5635854
  have hstable : (prefixWord ++ tailWord_5635854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635854).length < 2 ^ (prefixWord ++ tailWord_5635854).sum := by decide
  have hdescent : baseEnd_5635854 < baseStart_5635854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635914 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_5635914 : Nat := 118140960795 + 5635914 * 2 ^ 59
def prefixEnd_5635914 : Nat := 4983230072969 + 3 ^ 40 * 5635914 * 2
def baseEnd_5635914 : Nat := 964644269801255898085303

theorem tailTrace_5635914 : CollatzResearch.WordTrace tailWord_5635914 prefixEnd_5635914 964644269801255898085303 := by
  unfold tailWord_5635914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51389667726013397581196699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137039113936035726883191197 51389667726013397581196699)
  ·
    refine ⟨77084501589020096371795049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51389667726013397581196699 77084501589020096371795049)
    ·
      refine ⟨57813376191765072278846287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77084501589020096371795049 57813376191765072278846287)
      ·
        refine ⟨86720064287647608418269431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57813376191765072278846287 86720064287647608418269431)
        ·
          refine ⟨130080096431471412627404147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86720064287647608418269431 130080096431471412627404147)
          ·
            refine ⟨195120144647207118941106221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130080096431471412627404147 195120144647207118941106221)
            ·
              refine ⟨73170054242702669602914833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195120144647207118941106221 73170054242702669602914833)
              ·
                refine ⟨54877540682027002202186125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73170054242702669602914833 54877540682027002202186125)
                ·
                  refine ⟨20579077755760125825819797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54877540682027002202186125 20579077755760125825819797)
                  ·
                    refine ⟨964644269801255898085303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20579077755760125825819797 964644269801255898085303)
                    ·
                      rfl

theorem cell23_5635914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_5635914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635914 prefixEnd_5635914 := by exact prefixLift 5635914
  have htrace : WordTrace (prefixWord ++ tailWord_5635914) baseStart_5635914 baseEnd_5635914 := by
    simpa [prefixWord, tailWord_5635914, baseEnd_5635914] using wordTrace_append hprefix tailTrace_5635914
  have hstable : (prefixWord ++ tailWord_5635914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635914).length < 2 ^ (prefixWord ++ tailWord_5635914).sum := by decide
  have hdescent : baseEnd_5635914 < baseStart_5635914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635921 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_5635921 : Nat := 118140960795 + 5635921 * 2 ^ 59
def prefixEnd_5635921 : Nat := 4983230072969 + 3 ^ 40 * 5635921 * 2
def baseEnd_5635921 : Nat := 2893936403768349166868377

theorem tailTrace_5635921 : CollatzResearch.WordTrace tailWord_5635921 prefixEnd_5635921 2893936403768349166868377 := by
  unfold tailWord_5635921
  simp only [CollatzResearch.WordTrace]
  refine ⟨205558926215028230520291617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137039284143352153680194411 205558926215028230520291617)
  ·
    refine ⟨154169194661271172890218713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205558926215028230520291617 154169194661271172890218713)
    ·
      refine ⟨115626895995953379667664035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154169194661271172890218713 115626895995953379667664035)
      ·
        refine ⟨173440343993930069501496053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115626895995953379667664035 173440343993930069501496053)
        ·
          refine ⟨16260032249430944015765255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173440343993930069501496053 16260032249430944015765255)
          ·
            refine ⟨24390048374146416023647883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16260032249430944015765255 24390048374146416023647883)
            ·
              refine ⟨36585072561219624035471825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24390048374146416023647883 36585072561219624035471825)
              ·
                refine ⟨27438804420914718026603869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36585072561219624035471825 27438804420914718026603869)
                ·
                  refine ⟨10289551657843019259976451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27438804420914718026603869 10289551657843019259976451)
                  ·
                    refine ⟨15434327486764528889964677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10289551657843019259976451 15434327486764528889964677)
                    ·
                      refine ⟨2893936403768349166868377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15434327486764528889964677 2893936403768349166868377)
                      ·
                        rfl

theorem cell23_5635921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_5635921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635921 prefixEnd_5635921 := by exact prefixLift 5635921
  have htrace : WordTrace (prefixWord ++ tailWord_5635921) baseStart_5635921 baseEnd_5635921 := by
    simpa [prefixWord, tailWord_5635921, baseEnd_5635921] using wordTrace_append hprefix tailTrace_5635921
  have hstable : (prefixWord ++ tailWord_5635921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635921).length < 2 ^ (prefixWord ++ tailWord_5635921).sum := by decide
  have hdescent : baseEnd_5635921 < baseStart_5635921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635938 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5635938 : Nat := 118140960795 + 5635938 * 2 ^ 59
def prefixEnd_5635938 : Nat := 4983230072969 + 3 ^ 40 * 5635938 * 2
def baseEnd_5635938 : Nat := 2893945132939475600355799

theorem tailTrace_5635938 : CollatzResearch.WordTrace tailWord_5635938 prefixEnd_5635938 2893945132939475600355799 := by
  unfold tailWord_5635938
  simp only [CollatzResearch.WordTrace]
  refine ⟨51389886563991660605915117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137039697503977761615773645 51389886563991660605915117)
  ·
    refine ⟨19271207461496872727218169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51389886563991660605915117 19271207461496872727218169)
    ·
      refine ⟨14453405596122654545413627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19271207461496872727218169 14453405596122654545413627)
      ·
        refine ⟨21680108394183981818120441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14453405596122654545413627 21680108394183981818120441)
        ·
          refine ⟨16260081295637986363590331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21680108394183981818120441 16260081295637986363590331)
          ·
            refine ⟨24390121943456979545385497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16260081295637986363590331 24390121943456979545385497)
            ·
              refine ⟨18292591457592734659039123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24390121943456979545385497 18292591457592734659039123)
              ·
                refine ⟨27438887186389101988558685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18292591457592734659039123 27438887186389101988558685)
                ·
                  refine ⟨10289582694895913245709507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27438887186389101988558685 10289582694895913245709507)
                  ·
                    refine ⟨15434374042343869868564261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10289582694895913245709507 15434374042343869868564261)
                    ·
                      refine ⟨2893945132939475600355799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15434374042343869868564261 2893945132939475600355799)
                      ·
                        rfl

theorem cell23_5635938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5635938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635938 prefixEnd_5635938 := by exact prefixLift 5635938
  have htrace : WordTrace (prefixWord ++ tailWord_5635938) baseStart_5635938 baseEnd_5635938 := by
    simpa [prefixWord, tailWord_5635938, baseEnd_5635938] using wordTrace_append hprefix tailTrace_5635938
  have hstable : (prefixWord ++ tailWord_5635938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635938).length < 2 ^ (prefixWord ++ tailWord_5635938).sum := by decide
  have hdescent : baseEnd_5635938 < baseStart_5635938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635964 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_5635964 : Nat := 118140960795 + 5635964 * 2 ^ 59
def prefixEnd_5635964 : Nat := 4983230072969 + 3 ^ 40 * 5635964 * 2
def baseEnd_5635964 : Nat := 2893958483436492498630679

theorem tailTrace_5635964 : CollatzResearch.WordTrace tailWord_5635964 prefixEnd_5635964 2893958483436492498630679 := by
  unfold tailWord_5635964
  simp only [CollatzResearch.WordTrace]
  refine ⟨102780247276936224432053473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137040329702581632576071297 102780247276936224432053473)
  ·
    refine ⟨77085185457702168324040105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102780247276936224432053473 77085185457702168324040105)
    ·
      refine ⟨57813889093276626243030079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77085185457702168324040105 57813889093276626243030079)
      ·
        refine ⟨86720833639914939364545119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57813889093276626243030079 86720833639914939364545119)
        ·
          refine ⟨130081250459872409046817679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86720833639914939364545119 130081250459872409046817679)
          ·
            refine ⟨195121875689808613570226519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130081250459872409046817679 195121875689808613570226519)
            ·
              refine ⟨292682813534712920355339779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195121875689808613570226519 292682813534712920355339779)
              ·
                refine ⟨439024220302069380533009669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292682813534712920355339779 439024220302069380533009669)
                ·
                  refine ⟨82317041306638008849939313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439024220302069380533009669 82317041306638008849939313)
                  ·
                    refine ⟨61737780979978506637454485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82317041306638008849939313 61737780979978506637454485)
                    ·
                      refine ⟨2893958483436492498630679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61737780979978506637454485 2893958483436492498630679)
                      ·
                        rfl

theorem cell23_5635964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_5635964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635964 prefixEnd_5635964 := by exact prefixLift 5635964
  have htrace : WordTrace (prefixWord ++ tailWord_5635964) baseStart_5635964 baseEnd_5635964 := by
    simpa [prefixWord, tailWord_5635964, baseEnd_5635964] using wordTrace_append hprefix tailTrace_5635964
  have hstable : (prefixWord ++ tailWord_5635964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635964).length < 2 ^ (prefixWord ++ tailWord_5635964).sum := by decide
  have hdescent : baseEnd_5635964 < baseStart_5635964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635972 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_5635972 : Nat := 118140960795 + 5635972 * 2 ^ 59
def prefixEnd_5635972 : Nat := 4983230072969 + 3 ^ 40 * 5635972 * 2
def baseEnd_5635972 : Nat := 2893962591281728467330643

theorem tailTrace_5635972 : CollatzResearch.WordTrace tailWord_5635972 prefixEnd_5635972 2893962591281728467330643 := by
  unfold tailWord_5635972
  simp only [CollatzResearch.WordTrace]
  refine ⟨102780393168921733115199085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137040524225228977486932113 102780393168921733115199085)
  ·
    refine ⟨38542647438345649918199657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102780393168921733115199085 38542647438345649918199657)
    ·
      refine ⟨28906985578759237438649743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38542647438345649918199657 28906985578759237438649743)
      ·
        refine ⟨43360478368138856157974615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28906985578759237438649743 43360478368138856157974615)
        ·
          refine ⟨65040717552208284236961923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43360478368138856157974615 65040717552208284236961923)
          ·
            refine ⟨97561076328312426355442885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65040717552208284236961923 97561076328312426355442885)
            ·
              refine ⟨18292701811558579941645541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97561076328312426355442885 18292701811558579941645541)
              ·
                refine ⟨3429881589667233739058539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18292701811558579941645541 3429881589667233739058539)
                ·
                  refine ⟨5144822384500850608587809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429881589667233739058539 5144822384500850608587809)
                  ·
                    refine ⟨3858616788375637956440857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5144822384500850608587809 3858616788375637956440857)
                    ·
                      refine ⟨2893962591281728467330643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858616788375637956440857 2893962591281728467330643)
                      ·
                        rfl

theorem cell23_5635972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_5635972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635972 prefixEnd_5635972 := by exact prefixLift 5635972
  have htrace : WordTrace (prefixWord ++ tailWord_5635972) baseStart_5635972 baseEnd_5635972 := by
    simpa [prefixWord, tailWord_5635972, baseEnd_5635972] using wordTrace_append hprefix tailTrace_5635972
  have hstable : (prefixWord ++ tailWord_5635972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635972).length < 2 ^ (prefixWord ++ tailWord_5635972).sum := by decide
  have hdescent : baseEnd_5635972 < baseStart_5635972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635982 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_5635982 : Nat := 118140960795 + 5635982 * 2 ^ 59
def prefixEnd_5635982 : Nat := 4983230072969 + 3 ^ 40 * 5635982 * 2
def baseEnd_5635982 : Nat := 964655908696091142735199

theorem tailTrace_5635982 : CollatzResearch.WordTrace tailWord_5635982 prefixEnd_5635982 964655908696091142735199 := by
  unfold tailWord_5635982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25695143883475904742282775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137040767378538158625508133 25695143883475904742282775)
  ·
    refine ⟨38542715825213857113424163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25695143883475904742282775 38542715825213857113424163)
    ·
      refine ⟨57814073737820785670136245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38542715825213857113424163 57814073737820785670136245)
      ·
        refine ⟨5420069412920698656575273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57814073737820785670136245 5420069412920698656575273)
        ·
          refine ⟨4065052059690523992431455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5420069412920698656575273 4065052059690523992431455)
          ·
            refine ⟨6097578089535785988647183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065052059690523992431455 6097578089535785988647183)
            ·
              refine ⟨9146367134303678982970775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6097578089535785988647183 9146367134303678982970775)
              ·
                refine ⟨13719550701455518474456163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9146367134303678982970775 13719550701455518474456163)
                ·
                  refine ⟨20579326052183277711684245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13719550701455518474456163 20579326052183277711684245)
                  ·
                    refine ⟨964655908696091142735199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20579326052183277711684245 964655908696091142735199)
                    ·
                      rfl

theorem cell23_5635982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_5635982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635982 prefixEnd_5635982 := by exact prefixLift 5635982
  have htrace : WordTrace (prefixWord ++ tailWord_5635982) baseStart_5635982 baseEnd_5635982 := by
    simpa [prefixWord, tailWord_5635982, baseEnd_5635982] using wordTrace_append hprefix tailTrace_5635982
  have hstable : (prefixWord ++ tailWord_5635982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635982).length < 2 ^ (prefixWord ++ tailWord_5635982).sum := by decide
  have hdescent : baseEnd_5635982 < baseStart_5635982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635984 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_5635984 : Nat := 118140960795 + 5635984 * 2 ^ 59
def prefixEnd_5635984 : Nat := 4983230072969 + 3 ^ 40 * 5635984 * 2
def baseEnd_5635984 : Nat := 2893968753049582420380587

theorem tailTrace_5635984 : CollatzResearch.WordTrace tailWord_5635984 prefixEnd_5635984 2893968753049582420380587 := by
  unfold tailWord_5635984
  simp only [CollatzResearch.WordTrace]
  refine ⟨102780612006899996139917503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137040816009199994853223337 102780612006899996139917503)
  ·
    refine ⟨154170918010349994209876255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102780612006899996139917503 154170918010349994209876255)
    ·
      refine ⟨231256377015524991314814383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154170918010349994209876255 231256377015524991314814383)
      ·
        refine ⟨346884565523287486972221575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231256377015524991314814383 346884565523287486972221575)
        ·
          refine ⟨520326848284931230458332363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346884565523287486972221575 520326848284931230458332363)
          ·
            refine ⟨780490272427396845687498545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520326848284931230458332363 780490272427396845687498545)
            ·
              refine ⟨585367704320547634265623909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780490272427396845687498545 585367704320547634265623909)
              ·
                refine ⟨109756444560102681424804483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585367704320547634265623909 109756444560102681424804483)
                ·
                  refine ⟨164634666840154022137206725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109756444560102681424804483 164634666840154022137206725)
                  ·
                    refine ⟨30869000032528879150726261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164634666840154022137206725 30869000032528879150726261)
                    ·
                      refine ⟨2893968753049582420380587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30869000032528879150726261 2893968753049582420380587)
                      ·
                        rfl

theorem cell23_5635984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_5635984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635984 prefixEnd_5635984 := by exact prefixLift 5635984
  have htrace : WordTrace (prefixWord ++ tailWord_5635984) baseStart_5635984 baseEnd_5635984 := by
    simpa [prefixWord, tailWord_5635984, baseEnd_5635984] using wordTrace_append hprefix tailTrace_5635984
  have hstable : (prefixWord ++ tailWord_5635984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635984).length < 2 ^ (prefixWord ++ tailWord_5635984).sum := by decide
  have hdescent : baseEnd_5635984 < baseStart_5635984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635992 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5635992 : Nat := 118140960795 + 5635992 * 2 ^ 59
def prefixEnd_5635992 : Nat := 4983230072969 + 3 ^ 40 * 5635992 * 2
def baseEnd_5635992 : Nat := 2893972860894818389080551

theorem tailTrace_5635992 : CollatzResearch.WordTrace tailWord_5635992 prefixEnd_5635992 2893972860894818389080551 := by
  unfold tailWord_5635992
  simp only [CollatzResearch.WordTrace]
  refine ⟨102780757898885504823063115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137041010531847339764084153 102780757898885504823063115)
  ·
    refine ⟨154171136848328257234594673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102780757898885504823063115 154171136848328257234594673)
    ·
      refine ⟨115628352636246192925946005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154171136848328257234594673 115628352636246192925946005)
      ·
        refine ⟨5420079029824040293403719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115628352636246192925946005 5420079029824040293403719)
        ·
          refine ⟨8130118544736060440105579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420079029824040293403719 8130118544736060440105579)
          ·
            refine ⟨12195177817104090660158369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8130118544736060440105579 12195177817104090660158369)
            ·
              refine ⟨9146383362828067995118777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12195177817104090660158369 9146383362828067995118777)
              ·
                refine ⟨6859787522121050996339083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9146383362828067995118777 6859787522121050996339083)
                ·
                  refine ⟨10289681283181576494508625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6859787522121050996339083 10289681283181576494508625)
                  ·
                    refine ⟨7717260962386182370881469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10289681283181576494508625 7717260962386182370881469)
                    ·
                      refine ⟨2893972860894818389080551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7717260962386182370881469 2893972860894818389080551)
                      ·
                        rfl

theorem cell23_5635992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5635992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635992 prefixEnd_5635992 := by exact prefixLift 5635992
  have htrace : WordTrace (prefixWord ++ tailWord_5635992) baseStart_5635992 baseEnd_5635992 := by
    simpa [prefixWord, tailWord_5635992, baseEnd_5635992] using wordTrace_append hprefix tailTrace_5635992
  have hstable : (prefixWord ++ tailWord_5635992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635992).length < 2 ^ (prefixWord ++ tailWord_5635992).sum := by decide
  have hdescent : baseEnd_5635992 < baseStart_5635992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636031 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_5636031 : Nat := 118140960795 + 5636031 * 2 ^ 59
def prefixEnd_5636031 : Nat := 4983230072969 + 3 ^ 40 * 5636031 * 2
def baseEnd_5636031 : Nat := 2893992886640343736492871

theorem tailTrace_5636031 : CollatzResearch.WordTrace tailWord_5636031 prefixEnd_5636031 2893992886640343736492871 := by
  unfold tailWord_5636031
  simp only [CollatzResearch.WordTrace]
  refine ⟨205562938244629719306795947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137041958829753146204530631 205562938244629719306795947)
  ·
    refine ⟨308344407366944578960193921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205562938244629719306795947 308344407366944578960193921)
    ·
      refine ⟨231258305525208434220145441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308344407366944578960193921 231258305525208434220145441)
      ·
        refine ⟨173443729143906325665109081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231258305525208434220145441 173443729143906325665109081)
        ·
          refine ⟨130082796857929744248831811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173443729143906325665109081 130082796857929744248831811)
          ·
            refine ⟨195124195286894616373247717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130082796857929744248831811 195124195286894616373247717)
            ·
              refine ⟨36585786616292740569983947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195124195286894616373247717 36585786616292740569983947)
              ·
                refine ⟨54878679924439110854975921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36585786616292740569983947 54878679924439110854975921)
                ·
                  refine ⟨41159009943329333141231941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54878679924439110854975921 41159009943329333141231941)
                  ·
                    refine ⟨7717314364374249963980989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41159009943329333141231941 7717314364374249963980989)
                    ·
                      refine ⟨2893992886640343736492871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7717314364374249963980989 2893992886640343736492871)
                      ·
                        rfl

theorem cell23_5636031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_5636031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636031 prefixEnd_5636031 := by exact prefixLift 5636031
  have htrace : WordTrace (prefixWord ++ tailWord_5636031) baseStart_5636031 baseEnd_5636031 := by
    simpa [prefixWord, tailWord_5636031, baseEnd_5636031] using wordTrace_append hprefix tailTrace_5636031
  have hstable : (prefixWord ++ tailWord_5636031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636031).length < 2 ^ (prefixWord ++ tailWord_5636031).sum := by decide
  have hdescent : baseEnd_5636031 < baseStart_5636031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636066 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5636066 : Nat := 118140960795 + 5636066 * 2 ^ 59
def prefixEnd_5636066 : Nat := 4983230072969 + 3 ^ 40 * 5636066 * 2
def baseEnd_5636066 : Nat := 2894010858463251099555211

theorem tailTrace_5636066 : CollatzResearch.WordTrace tailWord_5636066 prefixEnd_5636066 2894010858463251099555211 := by
  unfold tailWord_5636066
  simp only [CollatzResearch.WordTrace]
  refine ⟨51391053699875730071080013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137042809866335280189546701 51391053699875730071080013)
  ·
    refine ⟨19271645137453398776655005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51391053699875730071080013 19271645137453398776655005)
    ·
      refine ⟨7226866926545024541245627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19271645137453398776655005 7226866926545024541245627)
      ·
        refine ⟨10840300389817536811868441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7226866926545024541245627 10840300389817536811868441)
        ·
          refine ⟨8130225292363152608901331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10840300389817536811868441 8130225292363152608901331)
          ·
            refine ⟨12195337938544728913351997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8130225292363152608901331 12195337938544728913351997)
            ·
              refine ⟨4573251726954273342506999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12195337938544728913351997 4573251726954273342506999)
              ·
                refine ⟨6859877590431410013760499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573251726954273342506999 6859877590431410013760499)
                ·
                  refine ⟨10289816385647115020640749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6859877590431410013760499 10289816385647115020640749)
                  ·
                    refine ⟨3858681144617668132740281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10289816385647115020640749 3858681144617668132740281)
                    ·
                      refine ⟨2894010858463251099555211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858681144617668132740281 2894010858463251099555211)
                      ·
                        rfl

theorem cell23_5636066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5636066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636066 prefixEnd_5636066 := by exact prefixLift 5636066
  have htrace : WordTrace (prefixWord ++ tailWord_5636066) baseStart_5636066 baseEnd_5636066 := by
    simpa [prefixWord, tailWord_5636066, baseEnd_5636066] using wordTrace_append hprefix tailTrace_5636066
  have hstable : (prefixWord ++ tailWord_5636066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636066).length < 2 ^ (prefixWord ++ tailWord_5636066).sum := by decide
  have hdescent : baseEnd_5636066 < baseStart_5636066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636068 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 5]
def baseStart_5636068 : Nat := 118140960795 + 5636068 * 2 ^ 59
def prefixEnd_5636068 : Nat := 4983230072969 + 3 ^ 40 * 5636068 * 2
def baseEnd_5636068 : Nat := 321556876158284454636689

theorem tailTrace_5636068 : CollatzResearch.WordTrace tailWord_5636068 prefixEnd_5636068 321556876158284454636689 := by
  unfold tailWord_5636068
  simp only [CollatzResearch.WordTrace]
  refine ⟨102782143872747837312946429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137042858496997116417261905 102782143872747837312946429)
  ·
    refine ⟨38543303952280438992354911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102782143872747837312946429 38543303952280438992354911)
    ·
      refine ⟨57814955928420658488532367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38543303952280438992354911 57814955928420658488532367)
      ·
        refine ⟨86722433892630987732798551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57814955928420658488532367 86722433892630987732798551)
        ·
          refine ⟨130083650838946481599197827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86722433892630987732798551 130083650838946481599197827)
          ·
            refine ⟨195125476258419722398796741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130083650838946481599197827 195125476258419722398796741)
            ·
              refine ⟨36586026798453697949774389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195125476258419722398796741 36586026798453697949774389)
              ·
                refine ⟨3429940012355034182791349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36586026798453697949774389 3429940012355034182791349)
                ·
                  refine ⟨321556876158284454636689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3429940012355034182791349 321556876158284454636689)
                  ·
                    rfl

theorem cell23_5636068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_5636068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636068 prefixEnd_5636068 := by exact prefixLift 5636068
  have htrace : WordTrace (prefixWord ++ tailWord_5636068) baseStart_5636068 baseEnd_5636068 := by
    simpa [prefixWord, tailWord_5636068, baseEnd_5636068] using wordTrace_append hprefix tailTrace_5636068
  have hstable : (prefixWord ++ tailWord_5636068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636068).length < 2 ^ (prefixWord ++ tailWord_5636068).sum := by decide
  have hdescent : baseEnd_5636068 < baseStart_5636068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636088 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 2, 5, 2]
def baseStart_5636088 : Nat := 118140960795 + 5636088 * 2 ^ 59
def prefixEnd_5636088 : Nat := 4983230072969 + 3 ^ 40 * 5636088 * 2
def baseEnd_5636088 : Nat := 2894022155037650013480109

theorem tailTrace_5636088 : CollatzResearch.WordTrace tailWord_5636088 prefixEnd_5636088 2894022155037650013480109 := by
  unfold tailWord_5636088
  simp only [CollatzResearch.WordTrace]
  refine ⟨102782508602711609020810459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137043344803615478694413945 102782508602711609020810459)
  ·
    refine ⟨154173762904067413531215689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102782508602711609020810459 154173762904067413531215689)
    ·
      refine ⟨115630322178050560148411767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154173762904067413531215689 115630322178050560148411767)
      ·
        refine ⟨173445483267075840222617651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115630322178050560148411767 173445483267075840222617651)
        ·
          refine ⟨260168224900613760333926477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173445483267075840222617651 260168224900613760333926477)
          ·
            refine ⟨97563084337730160125222429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260168224900613760333926477 97563084337730160125222429)
            ·
              refine ⟨36586156626648810046958411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97563084337730160125222429 36586156626648810046958411)
              ·
                refine ⟨54879234939973215070437617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36586156626648810046958411 54879234939973215070437617)
                ·
                  refine ⟨41159426204979911302828213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54879234939973215070437617 41159426204979911302828213)
                  ·
                    refine ⟨3858696206716866684640145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41159426204979911302828213 3858696206716866684640145)
                    ·
                      refine ⟨2894022155037650013480109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858696206716866684640145 2894022155037650013480109)
                      ·
                        rfl

theorem cell23_5636088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_5636088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636088 prefixEnd_5636088 := by exact prefixLift 5636088
  have htrace : WordTrace (prefixWord ++ tailWord_5636088) baseStart_5636088 baseEnd_5636088 := by
    simpa [prefixWord, tailWord_5636088, baseEnd_5636088] using wordTrace_append hprefix tailTrace_5636088
  have hstable : (prefixWord ++ tailWord_5636088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636088).length < 2 ^ (prefixWord ++ tailWord_5636088).sum := by decide
  have hdescent : baseEnd_5636088 < baseStart_5636088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636091 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5]
def baseStart_5636091 : Nat := 118140960795 + 5636091 * 2 ^ 59
def prefixEnd_5636091 : Nat := 4983230072969 + 3 ^ 40 * 5636091 * 2
def baseEnd_5636091 : Nat := 2894023695479613501742595

theorem tailTrace_5636091 : CollatzResearch.WordTrace tailWord_5636091 prefixEnd_5636091 2894023695479613501742595 := by
  unfold tailWord_5636091
  simp only [CollatzResearch.WordTrace]
  refine ⟨205565126624412349553980127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137043417749608233035986751 205565126624412349553980127)
  ·
    refine ⟨308347689936618524330970191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205565126624412349553980127 308347689936618524330970191)
    ·
      refine ⟨462521534904927786496455287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308347689936618524330970191 462521534904927786496455287)
      ·
        refine ⟨693782302357391679744682931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462521534904927786496455287 693782302357391679744682931)
        ·
          refine ⟨1040673453536087519617024397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693782302357391679744682931 1040673453536087519617024397)
          ·
            refine ⟨390252545076032819856384149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1040673453536087519617024397 390252545076032819856384149)
            ·
              refine ⟨18293088050439038430768007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 390252545076032819856384149 18293088050439038430768007)
              ·
                refine ⟨27439632075658557646152011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18293088050439038430768007 27439632075658557646152011)
                ·
                  refine ⟨41159448113487836469228017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27439632075658557646152011 41159448113487836469228017)
                  ·
                    refine ⟨30869586085115877351921013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41159448113487836469228017 30869586085115877351921013)
                    ·
                      refine ⟨2894023695479613501742595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30869586085115877351921013 2894023695479613501742595)
                      ·
                        rfl

theorem cell23_5636091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_5636091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636091 prefixEnd_5636091 := by exact prefixLift 5636091
  have htrace : WordTrace (prefixWord ++ tailWord_5636091) baseStart_5636091 baseEnd_5636091 := by
    simpa [prefixWord, tailWord_5636091, baseEnd_5636091] using wordTrace_append hprefix tailTrace_5636091
  have hstable : (prefixWord ++ tailWord_5636091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636091).length < 2 ^ (prefixWord ++ tailWord_5636091).sum := by decide
  have hdescent : baseEnd_5636091 < baseStart_5636091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636131 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_5636131 : Nat := 118140960795 + 5636131 * 2 ^ 59
def prefixEnd_5636131 : Nat := 4983230072969 + 3 ^ 40 * 5636131 * 2
def baseEnd_5636131 : Nat := 2894044234705793345242411

theorem tailTrace_5636131 : CollatzResearch.WordTrace tailWord_5636131 prefixEnd_5636131 2894044234705793345242411 := by
  unfold tailWord_5636131
  simp only [CollatzResearch.WordTrace]
  refine ⟨205566585544267436385436247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137044390362844957590290831 205566585544267436385436247)
  ·
    refine ⟨308349878316401154578154371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205566585544267436385436247 308349878316401154578154371)
    ·
      refine ⟨462524817474601731867231557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308349878316401154578154371 462524817474601731867231557)
      ·
        refine ⟨86723403276487824725105917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 462524817474601731867231557 86723403276487824725105917)
        ·
          refine ⟨32521276228682934271914719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86723403276487824725105917 32521276228682934271914719)
          ·
            refine ⟨48781914343024401407872079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32521276228682934271914719 48781914343024401407872079)
            ·
              refine ⟨73172871514536602111808119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48781914343024401407872079 73172871514536602111808119)
              ·
                refine ⟨109759307271804903167712179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73172871514536602111808119 109759307271804903167712179)
                ·
                  refine ⟨164638960907707354751568269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109759307271804903167712179 164638960907707354751568269)
                  ·
                    refine ⟨61739610340390258031838101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164638960907707354751568269 61739610340390258031838101)
                    ·
                      refine ⟨2894044234705793345242411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61739610340390258031838101 2894044234705793345242411)
                      ·
                        rfl

theorem cell23_5636131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_5636131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636131 prefixEnd_5636131 := by exact prefixLift 5636131
  have htrace : WordTrace (prefixWord ++ tailWord_5636131) baseStart_5636131 baseEnd_5636131 := by
    simpa [prefixWord, tailWord_5636131, baseEnd_5636131] using wordTrace_append hprefix tailTrace_5636131
  have hstable : (prefixWord ++ tailWord_5636131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636131).length < 2 ^ (prefixWord ++ tailWord_5636131).sum := by decide
  have hdescent : baseEnd_5636131 < baseStart_5636131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636145 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 3, 4]
def baseStart_5636145 : Nat := 118140960795 + 5636145 * 2 ^ 59
def prefixEnd_5636145 : Nat := 4983230072969 + 3 ^ 40 * 5636145 * 2
def baseEnd_5636145 : Nat := 964683807811652096822449

theorem tailTrace_5636145 : CollatzResearch.WordTrace tailWord_5636145 prefixEnd_5636145 964683807811652096822449 := by
  unfold tailWord_5636145
  simp only [CollatzResearch.WordTrace]
  refine ⟨205567096166216716776445889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137044730777477811184297259 205567096166216716776445889)
  ·
    refine ⟨154175322124662537582334417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205567096166216716776445889 154175322124662537582334417)
    ·
      refine ⟨115631491593496903186750813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154175322124662537582334417 115631491593496903186750813)
      ·
        refine ⟨43361809347561338695031555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115631491593496903186750813 43361809347561338695031555)
        ·
          refine ⟨65042714021342008042547333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43361809347561338695031555 65042714021342008042547333)
          ·
            refine ⟨12195508879001626507977625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65042714021342008042547333 12195508879001626507977625)
            ·
              refine ⟨9146631659251219880983219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12195508879001626507977625 9146631659251219880983219)
              ·
                refine ⟨13719947488876829821474829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9146631659251219880983219 13719947488876829821474829)
                ·
                  refine ⟨5144980308328811183053061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13719947488876829821474829 5144980308328811183053061)
                  ·
                    refine ⟨964683807811652096822449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144980308328811183053061 964683807811652096822449)
                    ·
                      rfl

theorem cell23_5636145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_5636145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636145 prefixEnd_5636145 := by exact prefixLift 5636145
  have htrace : WordTrace (prefixWord ++ tailWord_5636145) baseStart_5636145 baseEnd_5636145 := by
    simpa [prefixWord, tailWord_5636145, baseEnd_5636145] using wordTrace_append hprefix tailTrace_5636145
  have hstable : (prefixWord ++ tailWord_5636145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636145).length < 2 ^ (prefixWord ++ tailWord_5636145).sum := by decide
  have hdescent : baseEnd_5636145 < baseStart_5636145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636195 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 4, 3, 2]
def baseStart_5636195 : Nat := 118140960795 + 5636195 * 2 ^ 59
def prefixEnd_5636195 : Nat := 4983230072969 + 3 ^ 40 * 5636195 * 2
def baseEnd_5636195 : Nat := 2894077097467681094842117

theorem tailTrace_5636195 : CollatzResearch.WordTrace tailWord_5636195 prefixEnd_5636195 2894077097467681094842117 := by
  unfold tailWord_5636195
  simp only [CollatzResearch.WordTrace]
  refine ⟨205568919816035575315766039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137045946544023716877177359 205568919816035575315766039)
  ·
    refine ⟨308353379724053362973649059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205568919816035575315766039 308353379724053362973649059)
    ·
      refine ⟨462530069586080044460473589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308353379724053362973649059 462530069586080044460473589)
      ·
        refine ⟨43362194023695004168169399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 462530069586080044460473589 43362194023695004168169399)
        ·
          refine ⟨65043291035542506252254099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43362194023695004168169399 65043291035542506252254099)
          ·
            refine ⟨97564936553313759378381149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65043291035542506252254099 97564936553313759378381149)
            ·
              refine ⟨36586851207492659766892931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97564936553313759378381149 36586851207492659766892931)
              ·
                refine ⟨54880276811238989650339397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36586851207492659766892931 54880276811238989650339397)
                ·
                  refine ⟨10290051902107310559438637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54880276811238989650339397 10290051902107310559438637)
                  ·
                    refine ⟨3858769463290241459789489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10290051902107310559438637 3858769463290241459789489)
                    ·
                      refine ⟨2894077097467681094842117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858769463290241459789489 2894077097467681094842117)
                      ·
                        rfl

theorem cell23_5636195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_5636195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636195 prefixEnd_5636195 := by exact prefixLift 5636195
  have htrace : WordTrace (prefixWord ++ tailWord_5636195) baseStart_5636195 baseEnd_5636195 := by
    simpa [prefixWord, tailWord_5636195, baseEnd_5636195] using wordTrace_append hprefix tailTrace_5636195
  have hstable : (prefixWord ++ tailWord_5636195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636195).length < 2 ^ (prefixWord ++ tailWord_5636195).sum := by decide
  have hdescent : baseEnd_5636195 < baseStart_5636195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636248 : List Nat := [2, 1, 2, 4, 3, 11]
def baseStart_5636248 : Nat := 118140960795 + 5636248 * 2 ^ 59
def prefixEnd_5636248 : Nat := 4983230072969 + 3 ^ 40 * 5636248 * 2
def baseEnd_5636248 : Nat := 11909894287828680606911

theorem tailTrace_5636248 : CollatzResearch.WordTrace tailWord_5636248 prefixEnd_5636248 11909894287828680606911 := by
  unfold tailWord_5636248
  simp only [CollatzResearch.WordTrace]
  refine ⟨102785426442421782683722699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137047235256562376911630265 102785426442421782683722699)
  ·
    refine ⟨154178139663632674025584049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102785426442421782683722699 154178139663632674025584049)
    ·
      refine ⟨115633604747724505519188037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154178139663632674025584049 115633604747724505519188037)
      ·
        refine ⟨21681300890198344784847757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115633604747724505519188037 21681300890198344784847757)
        ·
          refine ⟨8130487833824379294317909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21681300890198344784847757 8130487833824379294317909)
          ·
            refine ⟨11909894287828680606911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8130487833824379294317909 11909894287828680606911)
            ·
              rfl

theorem cell23_5636248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 11].length) (baseStart_5636248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636248 prefixEnd_5636248 := by exact prefixLift 5636248
  have htrace : WordTrace (prefixWord ++ tailWord_5636248) baseStart_5636248 baseEnd_5636248 := by
    simpa [prefixWord, tailWord_5636248, baseEnd_5636248] using wordTrace_append hprefix tailTrace_5636248
  have hstable : (prefixWord ++ tailWord_5636248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636248).length < 2 ^ (prefixWord ++ tailWord_5636248).sum := by decide
  have hdescent : baseEnd_5636248 < baseStart_5636248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636252 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_5636252 : Nat := 118140960795 + 5636252 * 2 ^ 59
def prefixEnd_5636252 : Nat := 4983230072969 + 3 ^ 40 * 5636252 * 2
def baseEnd_5636252 : Nat := 964702121954995790609785

theorem tailTrace_5636252 : CollatzResearch.WordTrace tailWord_5636252 prefixEnd_5636252 964702121954995790609785 := by
  unfold tailWord_5636252
  simp only [CollatzResearch.WordTrace]
  refine ⟨102785499388414537025295505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137047332517886049367060673 102785499388414537025295505)
  ·
    refine ⟨77089124541310902768971629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102785499388414537025295505 77089124541310902768971629)
    ·
      refine ⟨28908421702991588538364361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77089124541310902768971629 28908421702991588538364361)
      ·
        refine ⟨21681316277243691403773271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28908421702991588538364361 21681316277243691403773271)
        ·
          refine ⟨32521974415865537105659907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21681316277243691403773271 32521974415865537105659907)
          ·
            refine ⟨48782961623798305658489861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32521974415865537105659907 48782961623798305658489861)
            ·
              refine ⟨9146805304462182310966849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48782961623798305658489861 9146805304462182310966849)
              ·
                refine ⟨6860103978346636733225137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9146805304462182310966849 6860103978346636733225137)
                ·
                  refine ⟨5145077983759977549918853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6860103978346636733225137 5145077983759977549918853)
                  ·
                    refine ⟨964702121954995790609785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145077983759977549918853 964702121954995790609785)
                    ·
                      rfl

theorem cell23_5636252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_5636252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636252 prefixEnd_5636252 := by exact prefixLift 5636252
  have htrace : WordTrace (prefixWord ++ tailWord_5636252) baseStart_5636252 baseEnd_5636252 := by
    simpa [prefixWord, tailWord_5636252, baseEnd_5636252] using wordTrace_append hprefix tailTrace_5636252
  have hstable : (prefixWord ++ tailWord_5636252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636252).length < 2 ^ (prefixWord ++ tailWord_5636252).sum := by decide
  have hdescent : baseEnd_5636252 < baseStart_5636252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636275 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 3]
def baseStart_5636275 : Nat := 118140960795 + 5636275 * 2 ^ 59
def prefixEnd_5636275 : Nat := 4983230072969 + 3 ^ 40 * 5636275 * 2
def baseEnd_5636275 : Nat := 2894118175920040781841749

theorem tailTrace_5636275 : CollatzResearch.WordTrace tailWord_5636275 prefixEnd_5636275 2894118175920040781841749 := by
  unfold tailWord_5636275
  simp only [CollatzResearch.WordTrace]
  refine ⟨205571837655745748978678279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137047891770497165985785519 205571837655745748978678279)
  ·
    refine ⟨308357756483618623468017419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205571837655745748978678279 308357756483618623468017419)
    ·
      refine ⟨462536634725427935202026129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308357756483618623468017419 462536634725427935202026129)
      ·
        refine ⟨346902476044070951401519597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462536634725427935202026129 346902476044070951401519597)
        ·
          refine ⟨130088428516526606775569849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346902476044070951401519597 130088428516526606775569849)
          ·
            refine ⟨97566321387394955081677387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130088428516526606775569849 97566321387394955081677387)
            ·
              refine ⟨146349482081092432622516081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97566321387394955081677387 146349482081092432622516081)
              ·
                refine ⟨109762111560819324466887061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146349482081092432622516081 109762111560819324466887061)
                ·
                  refine ⟨5145098979413405834385331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109762111560819324466887061 5145098979413405834385331)
                  ·
                    refine ⟨7717648469120108751577997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145098979413405834385331 7717648469120108751577997)
                    ·
                      refine ⟨2894118175920040781841749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7717648469120108751577997 2894118175920040781841749)
                      ·
                        rfl

theorem cell23_5636275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_5636275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636275 prefixEnd_5636275 := by exact prefixLift 5636275
  have htrace : WordTrace (prefixWord ++ tailWord_5636275) baseStart_5636275 baseEnd_5636275 := by
    simpa [prefixWord, tailWord_5636275, baseEnd_5636275] using wordTrace_append hprefix tailTrace_5636275
  have hstable : (prefixWord ++ tailWord_5636275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636275).length < 2 ^ (prefixWord ++ tailWord_5636275).sum := by decide
  have hdescent : baseEnd_5636275 < baseStart_5636275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636292 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_5636292 : Nat := 118140960795 + 5636292 * 2 ^ 59
def prefixEnd_5636292 : Nat := 4983230072969 + 3 ^ 40 * 5636292 * 2
def baseEnd_5636292 : Nat := 2894126905091167215329171

theorem tailTrace_5636292 : CollatzResearch.WordTrace tailWord_5636292 prefixEnd_5636292 2894126905091167215329171 := by
  unfold tailWord_5636292
  simp only [CollatzResearch.WordTrace]
  refine ⟨102786228848342080441023565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137048305131122773921364753 102786228848342080441023565)
  ·
    refine ⟨38544835818128280165383837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102786228848342080441023565 38544835818128280165383837)
    ·
      refine ⟨14454313431798105062018939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38544835818128280165383837 14454313431798105062018939)
      ·
        refine ⟨21681470147697157593028409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14454313431798105062018939 21681470147697157593028409)
        ·
          refine ⟨16261102610772868194771307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21681470147697157593028409 16261102610772868194771307)
          ·
            refine ⟨24391653916159302292156961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16261102610772868194771307 24391653916159302292156961)
            ·
              refine ⟨18293740437119476719117721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24391653916159302292156961 18293740437119476719117721)
              ·
                refine ⟨13720305327839607539338291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18293740437119476719117721 13720305327839607539338291)
                ·
                  refine ⟨20580457991759411309007437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13720305327839607539338291 20580457991759411309007437)
                  ·
                    refine ⟨7717671746909779240877789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20580457991759411309007437 7717671746909779240877789)
                    ·
                      refine ⟨2894126905091167215329171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7717671746909779240877789 2894126905091167215329171)
                      ·
                        rfl

theorem cell23_5636292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_5636292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636292 prefixEnd_5636292 := by exact prefixLift 5636292
  have htrace : WordTrace (prefixWord ++ tailWord_5636292) baseStart_5636292 baseEnd_5636292 := by
    simpa [prefixWord, tailWord_5636292, baseEnd_5636292] using wordTrace_append hprefix tailTrace_5636292
  have hstable : (prefixWord ++ tailWord_5636292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636292).length < 2 ^ (prefixWord ++ tailWord_5636292).sum := by decide
  have hdescent : baseEnd_5636292 < baseStart_5636292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636309 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5636309 : Nat := 118140960795 + 5636309 * 2 ^ 59
def prefixEnd_5636309 : Nat := 4983230072969 + 3 ^ 40 * 5636309 * 2
def baseEnd_5636309 : Nat := 2894135634262293648816593

theorem tailTrace_5636309 : CollatzResearch.WordTrace tailWord_5636309 prefixEnd_5636309 2894135634262293648816593 := by
  unfold tailWord_5636309
  simp only [CollatzResearch.WordTrace]
  refine ⟨205573077737622572785415981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137048718491748381856943987 205573077737622572785415981)
  ·
    refine ⟨77089904151608464794530993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205573077737622572785415981 77089904151608464794530993)
    ·
      refine ⟨57817428113706348595898245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77089904151608464794530993 57817428113706348595898245)
      ·
        refine ⟨10840767771319940361730921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57817428113706348595898245 10840767771319940361730921)
        ·
          refine ⟨8130575828489955271298191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10840767771319940361730921 8130575828489955271298191)
          ·
            refine ⟨12195863742734932906947287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8130575828489955271298191 12195863742734932906947287)
            ·
              refine ⟨18293795614102399360420931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12195863742734932906947287 18293795614102399360420931)
              ·
                refine ⟨27440693421153599040631397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18293795614102399360420931 27440693421153599040631397)
                ·
                  refine ⟨5145130016466299820118387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27440693421153599040631397 5145130016466299820118387)
                  ·
                    refine ⟨7717695024699449730177581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145130016466299820118387 7717695024699449730177581)
                    ·
                      refine ⟨2894135634262293648816593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7717695024699449730177581 2894135634262293648816593)
                      ·
                        rfl

theorem cell23_5636309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5636309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636309 prefixEnd_5636309 := by exact prefixLift 5636309
  have htrace : WordTrace (prefixWord ++ tailWord_5636309) baseStart_5636309 baseEnd_5636309 := by
    simpa [prefixWord, tailWord_5636309, baseEnd_5636309] using wordTrace_append hprefix tailTrace_5636309
  have hstable : (prefixWord ++ tailWord_5636309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636309).length < 2 ^ (prefixWord ++ tailWord_5636309).sum := by decide
  have hdescent : baseEnd_5636309 < baseStart_5636309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 5, 4, 2]
def baseStart_5636315 : Nat := 118140960795 + 5636315 * 2 ^ 59
def prefixEnd_5636315 : Nat := 4983230072969 + 3 ^ 40 * 5636315 * 2
def baseEnd_5636315 : Nat := 2894138715146220625341565

theorem tailTrace_5636315 : CollatzResearch.WordTrace tailWord_5636315 prefixEnd_5636315 2894138715146220625341565 := by
  unfold tailWord_5636315
  simp only [CollatzResearch.WordTrace]
  refine ⟨205573296575600835810134399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137048864383733890540089599 205573296575600835810134399)
  ·
    refine ⟨308359944863401253715201599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205573296575600835810134399 308359944863401253715201599)
    ·
      refine ⟨462539917295101880572802399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308359944863401253715201599 462539917295101880572802399)
      ·
        refine ⟨693809875942652820859203599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462539917295101880572802399 693809875942652820859203599)
        ·
          refine ⟨1040714813913979231288805399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693809875942652820859203599 1040714813913979231288805399)
          ·
            refine ⟨1561072220870968846933208099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040714813913979231288805399 1561072220870968846933208099)
            ·
              refine ⟨2341608331306453270399812149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561072220870968846933208099 2341608331306453270399812149)
              ·
                refine ⟨219525781059979994099982389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2341608331306453270399812149 219525781059979994099982389)
                ·
                  refine ⟨20580541974373124446873349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219525781059979994099982389 20580541974373124446873349)
                  ·
                    refine ⟨3858851620194960833788753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20580541974373124446873349 3858851620194960833788753)
                    ·
                      refine ⟨2894138715146220625341565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858851620194960833788753 2894138715146220625341565)
                      ·
                        rfl

theorem cell23_5636315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4, 2].length) (baseStart_5636315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636315 prefixEnd_5636315 := by exact prefixLift 5636315
  have htrace : WordTrace (prefixWord ++ tailWord_5636315) baseStart_5636315 baseEnd_5636315 := by
    simpa [prefixWord, tailWord_5636315, baseEnd_5636315] using wordTrace_append hprefix tailTrace_5636315
  have hstable : (prefixWord ++ tailWord_5636315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636315).length < 2 ^ (prefixWord ++ tailWord_5636315).sum := by decide
  have hdescent : baseEnd_5636315 < baseStart_5636315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636325 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_5636325 : Nat := 118140960795 + 5636325 * 2 ^ 59
def prefixEnd_5636325 : Nat := 4983230072969 + 3 ^ 40 * 5636325 * 2
def baseEnd_5636325 : Nat := 964714616650921862072173

theorem tailTrace_5636325 : CollatzResearch.WordTrace tailWord_5636325 prefixEnd_5636325 964714616650921862072173 := by
  unfold tailWord_5636325
  simp only [CollatzResearch.WordTrace]
  refine ⟨205573661305564607517998429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137049107537043071678665619 205573661305564607517998429)
  ·
    refine ⟨77090122989586727819249411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205573661305564607517998429 77090122989586727819249411)
    ·
      refine ⟨115635184484380091728874117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77090122989586727819249411 115635184484380091728874117)
      ·
        refine ⟨21681597090821267199163897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115635184484380091728874117 21681597090821267199163897)
        ·
          refine ⟨16261197818115950399372923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21681597090821267199163897 16261197818115950399372923)
          ·
            refine ⟨24391796727173925599059385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16261197818115950399372923 24391796727173925599059385)
            ·
              refine ⟨18293847545380444199294539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24391796727173925599059385 18293847545380444199294539)
              ·
                refine ⟨27440771318070666298941809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18293847545380444199294539 27440771318070666298941809)
                ·
                  refine ⟨20580578488552999724206357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27440771318070666298941809 20580578488552999724206357)
                  ·
                    refine ⟨964714616650921862072173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20580578488552999724206357 964714616650921862072173)
                    ·
                      rfl

theorem cell23_5636325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_5636325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636325 prefixEnd_5636325 := by exact prefixLift 5636325
  have htrace : WordTrace (prefixWord ++ tailWord_5636325) baseStart_5636325 baseEnd_5636325 := by
    simpa [prefixWord, tailWord_5636325, baseEnd_5636325] using wordTrace_append hprefix tailTrace_5636325
  have hstable : (prefixWord ++ tailWord_5636325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636325).length < 2 ^ (prefixWord ++ tailWord_5636325).sum := by decide
  have hdescent : baseEnd_5636325 < baseStart_5636325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636383 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 2, 2, 2]
def baseStart_5636383 : Nat := 118140960795 + 5636383 * 2 ^ 59
def prefixEnd_5636383 : Nat := 4983230072969 + 3 ^ 40 * 5636383 * 2
def baseEnd_5636383 : Nat := 2894173631830726359291253

theorem tailTrace_5636383 : CollatzResearch.WordTrace tailWord_5636383 prefixEnd_5636383 2894173631830726359291253 := by
  unfold tailWord_5636383
  simp only [CollatzResearch.WordTrace]
  refine ⟨205575776739354483423609803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137050517826236322282406535 205575776739354483423609803)
  ·
    refine ⟨308363665109031725135414705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205575776739354483423609803 308363665109031725135414705)
    ·
      refine ⟨231272748831773793851561029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308363665109031725135414705 231272748831773793851561029)
      ·
        refine ⟨43363640405957586347167693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231272748831773793851561029 43363640405957586347167693)
        ·
          refine ⟨16261365152234094880187885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43363640405957586347167693 16261365152234094880187885)
          ·
            refine ⟨6098011932087785580070457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16261365152234094880187885 6098011932087785580070457)
            ·
              refine ⟨4573508949065839185052843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6098011932087785580070457 4573508949065839185052843)
              ·
                refine ⟨6860263423598758777579265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573508949065839185052843 6860263423598758777579265)
                ·
                  refine ⟨5145197567699069083184449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6860263423598758777579265 5145197567699069083184449)
                  ·
                    refine ⟨3858898175774301812388337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5145197567699069083184449 3858898175774301812388337)
                    ·
                      refine ⟨2894173631830726359291253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858898175774301812388337 2894173631830726359291253)
                      ·
                        rfl

theorem cell23_5636383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_5636383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636383 prefixEnd_5636383 := by exact prefixLift 5636383
  have htrace : WordTrace (prefixWord ++ tailWord_5636383) baseStart_5636383 baseEnd_5636383 := by
    simpa [prefixWord, tailWord_5636383, baseEnd_5636383] using wordTrace_append hprefix tailTrace_5636383
  have hstable : (prefixWord ++ tailWord_5636383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636383).length < 2 ^ (prefixWord ++ tailWord_5636383).sum := by decide
  have hdescent : baseEnd_5636383 < baseStart_5636383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636425 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_5636425 : Nat := 118140960795 + 5636425 * 2 ^ 59
def prefixEnd_5636425 : Nat := 4983230072969 + 3 ^ 40 * 5636425 * 2
def baseEnd_5636425 : Nat := 2894195198018215194966059

theorem tailTrace_5636425 : CollatzResearch.WordTrace tailWord_5636425 prefixEnd_5636425 2894195198018215194966059 := by
  unfold tailWord_5636425
  simp only [CollatzResearch.WordTrace]
  refine ⟨205577308605202324596638729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137051539070134883064425819 205577308605202324596638729)
  ·
    refine ⟨154182981453901743447479047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205577308605202324596638729 154182981453901743447479047)
    ·
      refine ⟨231274472180852615171218571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154182981453901743447479047 231274472180852615171218571)
      ·
        refine ⟨346911708271278922756827857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231274472180852615171218571 346911708271278922756827857)
        ·
          refine ⟨260183781203459192067620893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346911708271278922756827857 260183781203459192067620893)
          ·
            refine ⟨97568917951297197025357835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260183781203459192067620893 97568917951297197025357835)
            ·
              refine ⟨146353376926945795538036753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97568917951297197025357835 146353376926945795538036753)
              ·
                refine ⟨109765032695209346653527565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146353376926945795538036753 109765032695209346653527565)
                ·
                  refine ⟨41161887260703504995072837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109765032695209346653527565 41161887260703504995072837)
                  ·
                    refine ⟨7717853861381907186576157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41161887260703504995072837 7717853861381907186576157)
                    ·
                      refine ⟨2894195198018215194966059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7717853861381907186576157 2894195198018215194966059)
                      ·
                        rfl

theorem cell23_5636425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_5636425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636425 prefixEnd_5636425 := by exact prefixLift 5636425
  have htrace : WordTrace (prefixWord ++ tailWord_5636425) baseStart_5636425 baseEnd_5636425 := by
    simpa [prefixWord, tailWord_5636425, baseEnd_5636425] using wordTrace_append hprefix tailTrace_5636425
  have hstable : (prefixWord ++ tailWord_5636425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636425).length < 2 ^ (prefixWord ++ tailWord_5636425).sum := by decide
  have hdescent : baseEnd_5636425 < baseStart_5636425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636466 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_5636466 : Nat := 118140960795 + 5636466 * 2 ^ 59
def prefixEnd_5636466 : Nat := 4983230072969 + 3 ^ 40 * 5636466 * 2
def baseEnd_5636466 : Nat := 964738750241683178184457

theorem tailTrace_5636466 : CollatzResearch.WordTrace tailWord_5636466 prefixEnd_5636466 964738750241683178184457 := by
  unfold tailWord_5636466
  simp only [CollatzResearch.WordTrace]
  refine ⟨51394700999513447149720313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137052535998702525732587501 51394700999513447149720313)
  ·
    refine ⟨38546025749635085362290235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51394700999513447149720313 38546025749635085362290235)
    ·
      refine ⟨57819038624452628043435353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38546025749635085362290235 57819038624452628043435353)
      ·
        refine ⟨43364278968339471032576515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57819038624452628043435353 43364278968339471032576515)
        ·
          refine ⟨65046418452509206548864773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43364278968339471032576515 65046418452509206548864773)
          ·
            refine ⟨12196203459845476227912145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65046418452509206548864773 12196203459845476227912145)
            ·
              refine ⟨9147152594884107170934109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12196203459845476227912145 9147152594884107170934109)
              ·
                refine ⟨3430182223081540189100291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9147152594884107170934109 3430182223081540189100291)
                ·
                  refine ⟨5145273334622310283650437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430182223081540189100291 5145273334622310283650437)
                  ·
                    refine ⟨964738750241683178184457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145273334622310283650437 964738750241683178184457)
                    ·
                      rfl

theorem cell23_5636466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_5636466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636466 prefixEnd_5636466 := by exact prefixLift 5636466
  have htrace : WordTrace (prefixWord ++ tailWord_5636466) baseStart_5636466 baseEnd_5636466 := by
    simpa [prefixWord, tailWord_5636466, baseEnd_5636466] using wordTrace_append hprefix tailTrace_5636466
  have hstable : (prefixWord ++ tailWord_5636466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636466).length < 2 ^ (prefixWord ++ tailWord_5636466).sum := by decide
  have hdescent : baseEnd_5636466 < baseStart_5636466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636489 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 3]
def baseStart_5636489 : Nat := 118140960795 + 5636489 * 2 ^ 59
def prefixEnd_5636489 : Nat := 4983230072969 + 3 ^ 40 * 5636489 * 2
def baseEnd_5636489 : Nat := 2894228060780102944565765

theorem tailTrace_5636489 : CollatzResearch.WordTrace tailWord_5636489 prefixEnd_5636489 2894228060780102944565765 := by
  unfold tailWord_5636489
  simp only [CollatzResearch.WordTrace]
  refine ⟨205579642876970463526968521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137053095251313642351312347 205579642876970463526968521)
  ·
    refine ⟨154184732157727847645226391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205579642876970463526968521 154184732157727847645226391)
    ·
      refine ⟨231277098236591771467839587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154184732157727847645226391 231277098236591771467839587)
      ·
        refine ⟨346915647354887657201759381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231277098236591771467839587 346915647354887657201759381)
        ·
          refine ⟨16261670969760358931332471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 346915647354887657201759381 16261670969760358931332471)
          ·
            refine ⟨24392506454640538396998707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16261670969760358931332471 24392506454640538396998707)
            ·
              refine ⟨36588759681960807595498061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24392506454640538396998707 36588759681960807595498061)
              ·
                refine ⟨13720784880735302848311773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36588759681960807595498061 13720784880735302848311773)
                ·
                  refine ⟨5145294330275738568116915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13720784880735302848311773 5145294330275738568116915)
                  ·
                    refine ⟨7717941495413607852175373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145294330275738568116915 7717941495413607852175373)
                    ·
                      refine ⟨2894228060780102944565765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7717941495413607852175373 2894228060780102944565765)
                      ·
                        rfl

theorem cell23_5636489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_5636489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636489 prefixEnd_5636489 := by exact prefixLift 5636489
  have htrace : WordTrace (prefixWord ++ tailWord_5636489) baseStart_5636489 baseEnd_5636489 := by
    simpa [prefixWord, tailWord_5636489, baseEnd_5636489] using wordTrace_append hprefix tailTrace_5636489
  have hstable : (prefixWord ++ tailWord_5636489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636489).length < 2 ^ (prefixWord ++ tailWord_5636489).sum := by decide
  have hdescent : baseEnd_5636489 < baseStart_5636489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636529 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_5636529 : Nat := 118140960795 + 5636529 * 2 ^ 59
def prefixEnd_5636529 : Nat := 4983230072969 + 3 ^ 40 * 5636529 * 2
def baseEnd_5636529 : Nat := 2894248600006282788065581

theorem tailTrace_5636529 : CollatzResearch.WordTrace tailWord_5636529 prefixEnd_5636529 2894248600006282788065581 := by
  unfold tailWord_5636529
  simp only [CollatzResearch.WordTrace]
  refine ⟨205581101796825550358424641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137054067864550366905616427 205581101796825550358424641)
  ·
    refine ⟨154185826347619162768818481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205581101796825550358424641 154185826347619162768818481)
    ·
      refine ⟨115639369760714372076613861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154185826347619162768818481 115639369760714372076613861)
      ·
        refine ⟨21682381830133944764365099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115639369760714372076613861 21682381830133944764365099)
        ·
          refine ⟨32523572745200917146547649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21682381830133944764365099 32523572745200917146547649)
          ·
            refine ⟨24392679558900687859910737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32523572745200917146547649 24392679558900687859910737)
            ·
              refine ⟨18294509669175515894933053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24392679558900687859910737 18294509669175515894933053)
              ·
                refine ⟨6860441125940818460599895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18294509669175515894933053 6860441125940818460599895)
                ·
                  refine ⟨10290661688911227690899843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6860441125940818460599895 10290661688911227690899843)
                  ·
                    refine ⟨15435992533366841536349765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10290661688911227690899843 15435992533366841536349765)
                    ·
                      refine ⟨2894248600006282788065581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15435992533366841536349765 2894248600006282788065581)
                      ·
                        rfl

theorem cell23_5636529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_5636529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636529 prefixEnd_5636529 := by exact prefixLift 5636529
  have htrace : WordTrace (prefixWord ++ tailWord_5636529) baseStart_5636529 baseEnd_5636529 := by
    simpa [prefixWord, tailWord_5636529, baseEnd_5636529] using wordTrace_append hprefix tailTrace_5636529
  have hstable : (prefixWord ++ tailWord_5636529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636529).length < 2 ^ (prefixWord ++ tailWord_5636529).sum := by decide
  have hdescent : baseEnd_5636529 < baseStart_5636529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636535 : List Nat := [1, 1, 3, 1, 3, 3, 11]
def baseStart_5636535 : Nat := 118140960795 + 5636535 * 2 ^ 59
def prefixEnd_5636535 : Nat := 4983230072969 + 3 ^ 40 * 5636535 * 2
def baseEnd_5636535 : Nat := 35731502233212466229513

theorem tailTrace_5636535 : CollatzResearch.WordTrace tailWord_5636535 prefixEnd_5636535 35731502233212466229513 := by
  unfold tailWord_5636535
  simp only [CollatzResearch.WordTrace]
  refine ⟨205581320634803813383143059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137054213756535875588762039 205581320634803813383143059)
  ·
    refine ⟨308371980952205720074714589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205581320634803813383143059 308371980952205720074714589)
    ·
      refine ⟨115639492857077145028017971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308371980952205720074714589 115639492857077145028017971)
      ·
        refine ⟨173459239285615717542026957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115639492857077145028017971 173459239285615717542026957)
        ·
          refine ⟨65047214732105894078260109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173459239285615717542026957 65047214732105894078260109)
          ·
            refine ⟨24392705524539710279347541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65047214732105894078260109 24392705524539710279347541)
            ·
              refine ⟨35731502233212466229513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24392705524539710279347541 35731502233212466229513)
              ·
                rfl

theorem cell23_5636535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 11].length) (baseStart_5636535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636535 prefixEnd_5636535 := by exact prefixLift 5636535
  have htrace : WordTrace (prefixWord ++ tailWord_5636535) baseStart_5636535 baseEnd_5636535 := by
    simpa [prefixWord, tailWord_5636535, baseEnd_5636535] using wordTrace_append hprefix tailTrace_5636535
  have hstable : (prefixWord ++ tailWord_5636535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636535).length < 2 ^ (prefixWord ++ tailWord_5636535).sum := by decide
  have hdescent : baseEnd_5636535 < baseStart_5636535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636540 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5636540 : Nat := 118140960795 + 5636540 * 2 ^ 59
def prefixEnd_5636540 : Nat := 4983230072969 + 3 ^ 40 * 5636540 * 2
def baseEnd_5636540 : Nat := 2894254248293482245028031

theorem tailTrace_5636540 : CollatzResearch.WordTrace tailWord_5636540 prefixEnd_5636540 2894254248293482245028031 := by
  unfold tailWord_5636540
  simp only [CollatzResearch.WordTrace]
  refine ⟨102790751499892849618537537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137054335333190466158050049 102790751499892849618537537)
  ·
    refine ⟨77093063624919637213903153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102790751499892849618537537 77093063624919637213903153)
    ·
      refine ⟨57819797718689727910427365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77093063624919637213903153 57819797718689727910427365)
      ·
        refine ⟨10841212072254323983205131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57819797718689727910427365 10841212072254323983205131)
        ·
          refine ⟨16261818108381485974807697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10841212072254323983205131 16261818108381485974807697)
          ·
            refine ⟨12196363581286114481105773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16261818108381485974807697 12196363581286114481105773)
            ·
              refine ⟨4573636342982292930414665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12196363581286114481105773 4573636342982292930414665)
              ·
                refine ⟨3430227257236719697810999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4573636342982292930414665 3430227257236719697810999)
                ·
                  refine ⟨5145340885855079546716499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430227257236719697810999 5145340885855079546716499)
                  ·
                    refine ⟨7718011328782619320074749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145340885855079546716499 7718011328782619320074749)
                    ·
                      refine ⟨2894254248293482245028031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7718011328782619320074749 2894254248293482245028031)
                      ·
                        rfl

theorem cell23_5636540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5636540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636540 prefixEnd_5636540 := by exact prefixLift 5636540
  have htrace : WordTrace (prefixWord ++ tailWord_5636540) baseStart_5636540 baseEnd_5636540 := by
    simpa [prefixWord, tailWord_5636540, baseEnd_5636540] using wordTrace_append hprefix tailTrace_5636540
  have hstable : (prefixWord ++ tailWord_5636540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636540).length < 2 ^ (prefixWord ++ tailWord_5636540).sum := by decide
  have hdescent : baseEnd_5636540 < baseStart_5636540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636542 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5636542 : Nat := 118140960795 + 5636542 * 2 ^ 59
def prefixEnd_5636542 : Nat := 4983230072969 + 3 ^ 40 * 5636542 * 2
def baseEnd_5636542 : Nat := 2894255275254791237203021

theorem tailTrace_5636542 : CollatzResearch.WordTrace tailWord_5636542 prefixEnd_5636542 2894255275254791237203021 := by
  unfold tailWord_5636542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25697696993222306697330985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137054383963852302385765253 25697696993222306697330985)
  ·
    refine ⟨19273272744916730022998239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25697696993222306697330985 19273272744916730022998239)
    ·
      refine ⟨28909909117375095034497359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19273272744916730022998239 28909909117375095034497359)
      ·
        refine ⟨43364863676062642551746039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28909909117375095034497359 43364863676062642551746039)
        ·
          refine ⟨65047295514093963827619059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43364863676062642551746039 65047295514093963827619059)
          ·
            refine ⟨97570943271140945741428589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65047295514093963827619059 97570943271140945741428589)
            ·
              refine ⟨36589103726677854653035721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97570943271140945741428589 36589103726677854653035721)
              ·
                refine ⟨27441827795008390989776791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36589103726677854653035721 27441827795008390989776791)
                ·
                  refine ⟨41162741692512586484665187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27441827795008390989776791 41162741692512586484665187)
                  ·
                    refine ⟨61744112538768879726997781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41162741692512586484665187 61744112538768879726997781)
                    ·
                      refine ⟨2894255275254791237203021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61744112538768879726997781 2894255275254791237203021)
                      ·
                        rfl

theorem cell23_5636542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5636542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636542 prefixEnd_5636542 := by exact prefixLift 5636542
  have htrace : WordTrace (prefixWord ++ tailWord_5636542) baseStart_5636542 baseEnd_5636542 := by
    simpa [prefixWord, tailWord_5636542, baseEnd_5636542] using wordTrace_append hprefix tailTrace_5636542
  have hstable : (prefixWord ++ tailWord_5636542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636542).length < 2 ^ (prefixWord ++ tailWord_5636542).sum := by decide
  have hdescent : baseEnd_5636542 < baseStart_5636542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636552 : List Nat := [2, 1, 3, 1, 3, 3, 2, 8]
def baseStart_5636552 : Nat := 118140960795 + 5636552 * 2 ^ 59
def prefixEnd_5636552 : Nat := 4983230072969 + 3 ^ 40 * 5636552 * 2
def baseEnd_5636552 : Nat := 107194830002271711039925

theorem tailTrace_5636552 : CollatzResearch.WordTrace tailWord_5636552 prefixEnd_5636552 107194830002271711039925 := by
  unfold tailWord_5636552
  simp only [CollatzResearch.WordTrace]
  refine ⟨102790970337871112643255955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137054627117161483524341273 102790970337871112643255955)
  ·
    refine ⟨154186455506806668964883933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102790970337871112643255955 154186455506806668964883933)
    ·
      refine ⟨57819920815052500861831475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154186455506806668964883933 57819920815052500861831475)
      ·
        refine ⟨86729881222578751292747213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57819920815052500861831475 86729881222578751292747213)
        ·
          refine ⟨32523705458467031734780205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86729881222578751292747213 32523705458467031734780205)
          ·
            refine ⟨12196389546925136900542577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32523705458467031734780205 12196389546925136900542577)
            ·
              refine ⟨9147292160193852675406933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12196389546925136900542577 9147292160193852675406933)
              ·
                refine ⟨107194830002271711039925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9147292160193852675406933 107194830002271711039925)
                ·
                  rfl

theorem cell23_5636552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 8].length) (baseStart_5636552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636552 prefixEnd_5636552 := by exact prefixLift 5636552
  have htrace : WordTrace (prefixWord ++ tailWord_5636552) baseStart_5636552 baseEnd_5636552 := by
    simpa [prefixWord, tailWord_5636552, baseEnd_5636552] using wordTrace_append hprefix tailTrace_5636552
  have hstable : (prefixWord ++ tailWord_5636552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636552).length < 2 ^ (prefixWord ++ tailWord_5636552).sum := by decide
  have hdescent : baseEnd_5636552 < baseStart_5636552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636555 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_5636555 : Nat := 118140960795 + 5636555 * 2 ^ 59
def prefixEnd_5636555 : Nat := 4983230072969 + 3 ^ 40 * 5636555 * 2
def baseEnd_5636555 : Nat := 2894261950503299686340461

theorem tailTrace_5636555 : CollatzResearch.WordTrace tailWord_5636555 prefixEnd_5636555 2894261950503299686340461 := by
  unfold tailWord_5636555
  simp only [CollatzResearch.WordTrace]
  refine ⟨205582050094731356798871119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137054700063154237865914079 205582050094731356798871119)
  ·
    refine ⟨308373075142097035198306679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205582050094731356798871119 308373075142097035198306679)
    ·
      refine ⟨462559612713145552797460019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308373075142097035198306679 462559612713145552797460019)
      ·
        refine ⟨693839419069718329196190029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462559612713145552797460019 693839419069718329196190029)
        ·
          refine ⟨260189782151144373448571261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693839419069718329196190029 260189782151144373448571261)
          ·
            refine ⟨97571168306679140043214223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260189782151144373448571261 97571168306679140043214223)
            ·
              refine ⟨146356752460018710064821335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97571168306679140043214223 146356752460018710064821335)
              ·
                refine ⟨219535128690028065097232003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146356752460018710064821335 219535128690028065097232003)
                ·
                  refine ⟨329302693035042097645848005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219535128690028065097232003 329302693035042097645848005)
                  ·
                    refine ⟨61744254944070393308596501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 329302693035042097645848005 61744254944070393308596501)
                    ·
                      refine ⟨2894261950503299686340461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61744254944070393308596501 2894261950503299686340461)
                      ·
                        rfl

theorem cell23_5636555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_5636555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636555 prefixEnd_5636555 := by exact prefixLift 5636555
  have htrace : WordTrace (prefixWord ++ tailWord_5636555) baseStart_5636555 baseEnd_5636555 := by
    simpa [prefixWord, tailWord_5636555, baseEnd_5636555] using wordTrace_append hprefix tailTrace_5636555
  have hstable : (prefixWord ++ tailWord_5636555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636555).length < 2 ^ (prefixWord ++ tailWord_5636555).sum := by decide
  have hdescent : baseEnd_5636555 < baseStart_5636555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636556 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_5636556 : Nat := 118140960795 + 5636556 * 2 ^ 59
def prefixEnd_5636556 : Nat := 4983230072969 + 3 ^ 40 * 5636556 * 2
def baseEnd_5636556 : Nat := 964754154661318060809319

theorem tailTrace_5636556 : CollatzResearch.WordTrace tailWord_5636556 prefixEnd_5636556 964754154661318060809319 := by
  unfold tailWord_5636556
  simp only [CollatzResearch.WordTrace]
  refine ⟨102791043283863866984828761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137054724378485155979771681 102791043283863866984828761)
  ·
    refine ⟨77093282462897900238621571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102791043283863866984828761 77093282462897900238621571)
    ·
      refine ⟨115639923694346850357932357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77093282462897900238621571 115639923694346850357932357)
      ·
        refine ⟨21682485692690034442112317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115639923694346850357932357 21682485692690034442112317)
        ·
          refine ⟨8130932134758762915792119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21682485692690034442112317 8130932134758762915792119)
          ·
            refine ⟨12196398202138144373688179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8130932134758762915792119 12196398202138144373688179)
            ·
              refine ⟨18294597303207216560532269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12196398202138144373688179 18294597303207216560532269)
              ·
                refine ⟨6860473988702706210199601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18294597303207216560532269 6860473988702706210199601)
                ·
                  refine ⟨5145355491527029657649701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6860473988702706210199601 5145355491527029657649701)
                  ·
                    refine ⟨964754154661318060809319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145355491527029657649701 964754154661318060809319)
                    ·
                      rfl

theorem cell23_5636556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_5636556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636556 prefixEnd_5636556 := by exact prefixLift 5636556
  have htrace : WordTrace (prefixWord ++ tailWord_5636556) baseStart_5636556 baseEnd_5636556 := by
    simpa [prefixWord, tailWord_5636556, baseEnd_5636556] using wordTrace_append hprefix tailTrace_5636556
  have hstable : (prefixWord ++ tailWord_5636556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636556).length < 2 ^ (prefixWord ++ tailWord_5636556).sum := by decide
  have hdescent : baseEnd_5636556 < baseStart_5636556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636566 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5636566 : Nat := 118140960795 + 5636566 * 2 ^ 59
def prefixEnd_5636566 : Nat := 4983230072969 + 3 ^ 40 * 5636566 * 2
def baseEnd_5636566 : Nat := 2894267598790499143302911

theorem tailTrace_5636566 : CollatzResearch.WordTrace tailWord_5636566 prefixEnd_5636566 2894267598790499143302911 := by
  unfold tailWord_5636566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12848903206105719104845097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137054967531794337118347701 12848903206105719104845097)
  ·
    refine ⟨9636677404579289328633823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12848903206105719104845097 9636677404579289328633823)
    ·
      refine ⟨14455016106868933992950735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9636677404579289328633823 14455016106868933992950735)
      ·
        refine ⟨21682524160303400989426103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14455016106868933992950735 21682524160303400989426103)
        ·
          refine ⟨32523786240455101484139155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21682524160303400989426103 32523786240455101484139155)
          ·
            refine ⟨48785679360682652226208733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32523786240455101484139155 48785679360682652226208733)
            ·
              refine ⟨18294629760255994584828275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48785679360682652226208733 18294629760255994584828275)
              ·
                refine ⟨27441944640383991877242413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18294629760255994584828275 27441944640383991877242413)
                ·
                  refine ⟨10290729240143996953965905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27441944640383991877242413 10290729240143996953965905)
                  ·
                    refine ⟨7718046930107997715474429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10290729240143996953965905 7718046930107997715474429)
                    ·
                      refine ⟨2894267598790499143302911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7718046930107997715474429 2894267598790499143302911)
                      ·
                        rfl

theorem cell23_5636566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5636566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636566 prefixEnd_5636566 := by exact prefixLift 5636566
  have htrace : WordTrace (prefixWord ++ tailWord_5636566) baseStart_5636566 baseEnd_5636566 := by
    simpa [prefixWord, tailWord_5636566, baseEnd_5636566] using wordTrace_append hprefix tailTrace_5636566
  have hstable : (prefixWord ++ tailWord_5636566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636566).length < 2 ^ (prefixWord ++ tailWord_5636566).sum := by decide
  have hdescent : baseEnd_5636566 < baseStart_5636566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636597 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5636597 : Nat := 118140960795 + 5636597 * 2 ^ 59
def prefixEnd_5636597 : Nat := 4983230072969 + 3 ^ 40 * 5636597 * 2
def baseEnd_5636597 : Nat := 2894283516690788522015269

theorem tailTrace_5636597 : CollatzResearch.WordTrace tailWord_5636597 prefixEnd_5636597 2894283516690788522015269 := by
  unfold tailWord_5636597
  simp only [CollatzResearch.WordTrace]
  refine ⟨205583581960579197971900045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137055721307052798647933363 205583581960579197971900045)
  ·
    refine ⟨77093843235217199239462517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205583581960579197971900045 77093843235217199239462517)
    ·
      refine ⟨7227547803301612428699611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77093843235217199239462517 7227547803301612428699611)
      ·
        refine ⟨10841321704952418643049417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7227547803301612428699611 10841321704952418643049417)
        ·
          refine ⟨8130991278714313982287063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10841321704952418643049417 8130991278714313982287063)
          ·
            refine ⟨12196486918071470973430595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8130991278714313982287063 12196486918071470973430595)
            ·
              refine ⟨18294730377107206460145893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12196486918071470973430595 18294730377107206460145893)
              ·
                refine ⟨3430261945707601211277355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18294730377107206460145893 3430261945707601211277355)
                ·
                  refine ⟨5145392918561401816916033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430261945707601211277355 5145392918561401816916033)
                  ·
                    refine ⟨3859044688921051362687025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5145392918561401816916033 3859044688921051362687025)
                    ·
                      refine ⟨2894283516690788522015269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859044688921051362687025 2894283516690788522015269)
                      ·
                        rfl

theorem cell23_5636597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5636597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636597 prefixEnd_5636597 := by exact prefixLift 5636597
  have htrace : WordTrace (prefixWord ++ tailWord_5636597) baseStart_5636597 baseEnd_5636597 := by
    simpa [prefixWord, tailWord_5636597, baseEnd_5636597] using wordTrace_append hprefix tailTrace_5636597
  have hstable : (prefixWord ++ tailWord_5636597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636597).length < 2 ^ (prefixWord ++ tailWord_5636597).sum := by decide
  have hdescent : baseEnd_5636597 < baseStart_5636597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636636 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_5636636 : Nat := 118140960795 + 5636636 * 2 ^ 59
def prefixEnd_5636636 : Nat := 4983230072969 + 3 ^ 40 * 5636636 * 2
def baseEnd_5636636 : Nat := 2894303542436313869427589

theorem tailTrace_5636636 : CollatzResearch.WordTrace tailWord_5636636 prefixEnd_5636636 2894303542436313869427589 := by
  unfold tailWord_5636636
  simp only [CollatzResearch.WordTrace]
  refine ⟨102792502203718953816284881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137056669604958605088379841 102792502203718953816284881)
  ·
    refine ⟨77094376652789215362213661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102792502203718953816284881 77094376652789215362213661)
    ·
      refine ⟨28910391244795955760830123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77094376652789215362213661 28910391244795955760830123)
      ·
        refine ⟨43365586867193933641245185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28910391244795955760830123 43365586867193933641245185)
        ·
          refine ⟨32524190150395450230933889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43365586867193933641245185 32524190150395450230933889)
          ·
            refine ⟨24393142612796587673200417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32524190150395450230933889 24393142612796587673200417)
            ·
              refine ⟨18294856959597440754900313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24393142612796587673200417 18294856959597440754900313)
              ·
                refine ⟨13721142719698080566175235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18294856959597440754900313 13721142719698080566175235)
                ·
                  refine ⟨20581714079547120849262853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13721142719698080566175235 20581714079547120849262853)
                  ·
                    refine ⟨3859071389915085159236785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20581714079547120849262853 3859071389915085159236785)
                    ·
                      refine ⟨2894303542436313869427589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859071389915085159236785 2894303542436313869427589)
                      ·
                        rfl

theorem cell23_5636636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_5636636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636636 prefixEnd_5636636 := by exact prefixLift 5636636
  have htrace : WordTrace (prefixWord ++ tailWord_5636636) baseStart_5636636 baseEnd_5636636 := by
    simpa [prefixWord, tailWord_5636636, baseEnd_5636636] using wordTrace_append hprefix tailTrace_5636636
  have hstable : (prefixWord ++ tailWord_5636636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636636).length < 2 ^ (prefixWord ++ tailWord_5636636).sum := by decide
  have hdescent : baseEnd_5636636 < baseStart_5636636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636642 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_5636642 : Nat := 118140960795 + 5636642 * 2 ^ 59
def prefixEnd_5636642 : Nat := 4983230072969 + 3 ^ 40 * 5636642 * 2
def baseEnd_5636642 : Nat := 321589624813360093994729

theorem tailTrace_5636642 : CollatzResearch.WordTrace tailWord_5636642 prefixEnd_5636642 321589624813360093994729 := by
  unfold tailWord_5636642
  simp only [CollatzResearch.WordTrace]
  refine ⟨51396305811354042664322045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137056815496944113771525453 51396305811354042664322045)
  ·
    refine ⟨19273614679257765999120767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51396305811354042664322045 19273614679257765999120767)
    ·
      refine ⟨28910422018886648998681151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19273614679257765999120767 28910422018886648998681151)
      ·
        refine ⟨43365633028329973498021727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28910422018886648998681151 43365633028329973498021727)
        ·
          refine ⟨65048449542494960247032591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43365633028329973498021727 65048449542494960247032591)
          ·
            refine ⟨97572674313742440370548887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65048449542494960247032591 97572674313742440370548887)
            ·
              refine ⟨146359011470613660555823331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97572674313742440370548887 146359011470613660555823331)
              ·
                refine ⟨219538517205920490833734997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146359011470613660555823331 219538517205920490833734997)
                ·
                  refine ⟨321589624813360093994729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 219538517205920490833734997 321589624813360093994729)
                  ·
                    rfl

theorem cell23_5636642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_5636642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636642 prefixEnd_5636642 := by exact prefixLift 5636642
  have htrace : WordTrace (prefixWord ++ tailWord_5636642) baseStart_5636642 baseEnd_5636642 := by
    simpa [prefixWord, tailWord_5636642, baseEnd_5636642] using wordTrace_append hprefix tailTrace_5636642
  have hstable : (prefixWord ++ tailWord_5636642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636642).length < 2 ^ (prefixWord ++ tailWord_5636642).sum := by decide
  have hdescent : baseEnd_5636642 < baseStart_5636642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636647 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5636647 : Nat := 118140960795 + 5636647 * 2 ^ 59
def prefixEnd_5636647 : Nat := 4983230072969 + 3 ^ 40 * 5636647 * 2
def baseEnd_5636647 : Nat := 2894309190723513326390039

theorem tailTrace_5636647 : CollatzResearch.WordTrace tailWord_5636647 prefixEnd_5636647 2894309190723513326390039 := by
  unfold tailWord_5636647
  simp only [CollatzResearch.WordTrace]
  refine ⟨205585405610398056511220195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137056937073598704340813463 205585405610398056511220195)
  ·
    refine ⟨308378108415597084766830293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205585405610398056511220195 308378108415597084766830293)
    ·
      refine ⟨7227611915990556674222585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 308378108415597084766830293 7227611915990556674222585)
      ·
        refine ⟨5420708936992917505666939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7227611915990556674222585 5420708936992917505666939)
        ·
          refine ⟨8131063405489376258500409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420708936992917505666939 8131063405489376258500409)
          ·
            refine ⟨6098297554117032193875307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8131063405489376258500409 6098297554117032193875307)
            ·
              refine ⟨9147446331175548290812961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6098297554117032193875307 9147446331175548290812961)
              ·
                refine ⟨6860584748381661218109721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9147446331175548290812961 6860584748381661218109721)
                ·
                  refine ⟨5145438561286245913582291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6860584748381661218109721 5145438561286245913582291)
                  ·
                    refine ⟨7718157841929368870373437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145438561286245913582291 7718157841929368870373437)
                    ·
                      refine ⟨2894309190723513326390039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7718157841929368870373437 2894309190723513326390039)
                      ·
                        rfl

theorem cell23_5636647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5636647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636647 prefixEnd_5636647 := by exact prefixLift 5636647
  have htrace : WordTrace (prefixWord ++ tailWord_5636647) baseStart_5636647 baseEnd_5636647 := by
    simpa [prefixWord, tailWord_5636647, baseEnd_5636647] using wordTrace_append hprefix tailTrace_5636647
  have hstable : (prefixWord ++ tailWord_5636647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636647).length < 2 ^ (prefixWord ++ tailWord_5636647).sum := by decide
  have hdescent : baseEnd_5636647 < baseStart_5636647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636659 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 5]
def baseStart_5636659 : Nat := 118140960795 + 5636659 * 2 ^ 59
def prefixEnd_5636659 : Nat := 4983230072969 + 3 ^ 40 * 5636659 * 2
def baseEnd_5636659 : Nat := 321590594721263031048887

theorem tailTrace_5636659 : CollatzResearch.WordTrace tailWord_5636659 prefixEnd_5636659 321590594721263031048887 := by
  unfold tailWord_5636659
  simp only [CollatzResearch.WordTrace]
  refine ⟨205585843286354582560657031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137057228857569721707104687 205585843286354582560657031)
  ·
    refine ⟨308378764929531873840985547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205585843286354582560657031 308378764929531873840985547)
    ·
      refine ⟨462568147394297810761478321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308378764929531873840985547 462568147394297810761478321)
      ·
        refine ⟨346926110545723358071108741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462568147394297810761478321 346926110545723358071108741)
        ·
          refine ⟨65048645727323129638332889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346926110545723358071108741 65048645727323129638332889)
          ·
            refine ⟨48786484295492347228749667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65048645727323129638332889 48786484295492347228749667)
            ·
              refine ⟨73179726443238520843124501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48786484295492347228749667 73179726443238520843124501)
              ·
                refine ⟨3430299677026805664521461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73179726443238520843124501 3430299677026805664521461)
                ·
                  refine ⟨321590594721263031048887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3430299677026805664521461 321590594721263031048887)
                  ·
                    rfl

theorem cell23_5636659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 5].length) (baseStart_5636659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636659 prefixEnd_5636659 := by exact prefixLift 5636659
  have htrace : WordTrace (prefixWord ++ tailWord_5636659) baseStart_5636659 baseEnd_5636659 := by
    simpa [prefixWord, tailWord_5636659, baseEnd_5636659] using wordTrace_append hprefix tailTrace_5636659
  have hstable : (prefixWord ++ tailWord_5636659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636659).length < 2 ^ (prefixWord ++ tailWord_5636659).sum := by decide
  have hdescent : baseEnd_5636659 < baseStart_5636659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636672 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_5636672 : Nat := 118140960795 + 5636672 * 2 ^ 59
def prefixEnd_5636672 : Nat := 4983230072969 + 3 ^ 40 * 5636672 * 2
def baseEnd_5636672 : Nat := 964774009246625242859141

theorem tailTrace_5636672 : CollatzResearch.WordTrace tailWord_5636672 prefixEnd_5636672 964774009246625242859141 := by
  unfold tailWord_5636672
  simp only [CollatzResearch.WordTrace]
  refine ⟨102793158717653742890440135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137057544956871657187253513 102793158717653742890440135)
  ·
    refine ⟨154189738076480614335660203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102793158717653742890440135 154189738076480614335660203)
    ·
      refine ⟨231284607114720921503490305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154189738076480614335660203 231284607114720921503490305)
      ·
        refine ⟨173463455336040691127617729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231284607114720921503490305 173463455336040691127617729)
        ·
          refine ⟨130097591502030518345713297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173463455336040691127617729 130097591502030518345713297)
          ·
            refine ⟨97573193626522888759284973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130097591502030518345713297 97573193626522888759284973)
            ·
              refine ⟨36589947609946083284731865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97573193626522888759284973 36589947609946083284731865)
              ·
                refine ⟨27442460707459562463548899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36589947609946083284731865 27442460707459562463548899)
                ·
                  refine ⟨41163691061189343695323349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27442460707459562463548899 41163691061189343695323349)
                  ·
                    refine ⟨964774009246625242859141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41163691061189343695323349 964774009246625242859141)
                    ·
                      rfl

theorem cell23_5636672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_5636672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636672 prefixEnd_5636672 := by exact prefixLift 5636672
  have htrace : WordTrace (prefixWord ++ tailWord_5636672) baseStart_5636672 baseEnd_5636672 := by
    simpa [prefixWord, tailWord_5636672, baseEnd_5636672] using wordTrace_append hprefix tailTrace_5636672
  have hstable : (prefixWord ++ tailWord_5636672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636672).length < 2 ^ (prefixWord ++ tailWord_5636672).sum := by decide
  have hdescent : baseEnd_5636672 < baseStart_5636672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636752 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_5636752 : Nat := 118140960795 + 5636752 * 2 ^ 59
def prefixEnd_5636752 : Nat := 4983230072969 + 3 ^ 40 * 5636752 * 2
def baseEnd_5636752 : Nat := 2894363106192235415577055

theorem tailTrace_5636752 : CollatzResearch.WordTrace tailWord_5636752 prefixEnd_5636752 2894363106192235415577055 := by
  unfold tailWord_5636752
  simp only [CollatzResearch.WordTrace]
  refine ⟨102794617637508829721896255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137059490183345106295861673 102794617637508829721896255)
  ·
    refine ⟨154191926456263244582844383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102794617637508829721896255 154191926456263244582844383)
    ·
      refine ⟨231287889684394866874266575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154191926456263244582844383 231287889684394866874266575)
      ·
        refine ⟨346931834526592300311399863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231287889684394866874266575 346931834526592300311399863)
        ·
          refine ⟨520397751789888450467099795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346931834526592300311399863 520397751789888450467099795)
          ·
            refine ⟨780596627684832675700649693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520397751789888450467099795 780596627684832675700649693)
            ·
              refine ⟨292723735381812253387743635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780596627684832675700649693 292723735381812253387743635)
              ·
                refine ⟨439085603072718380081615453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292723735381812253387743635 439085603072718380081615453)
                ·
                  refine ⟨164657101152269392530605795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439085603072718380081615453 164657101152269392530605795)
                  ·
                    refine ⟨246985651728404088795908693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164657101152269392530605795 246985651728404088795908693)
                    ·
                      refine ⟨2894363106192235415577055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 246985651728404088795908693 2894363106192235415577055)
                      ·
                        rfl

theorem cell23_5636752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_5636752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636752 prefixEnd_5636752 := by exact prefixLift 5636752
  have htrace : WordTrace (prefixWord ++ tailWord_5636752) baseStart_5636752 baseEnd_5636752 := by
    simpa [prefixWord, tailWord_5636752, baseEnd_5636752] using wordTrace_append hprefix tailTrace_5636752
  have hstable : (prefixWord ++ tailWord_5636752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636752).length < 2 ^ (prefixWord ++ tailWord_5636752).sum := by decide
  have hdescent : baseEnd_5636752 < baseStart_5636752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636786 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_5636786 : Nat := 118140960795 + 5636786 * 2 ^ 59
def prefixEnd_5636786 : Nat := 4983230072969 + 3 ^ 40 * 5636786 * 2
def baseEnd_5636786 : Nat := 2894380564534488282551899

theorem tailTrace_5636786 : CollatzResearch.WordTrace tailWord_5636786 prefixEnd_5636786 2894380564534488282551899 := by
  unfold tailWord_5636786
  simp only [CollatzResearch.WordTrace]
  refine ⟨51397618839223620812632553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137060316904596322167020141 51397618839223620812632553)
  ·
    refine ⟨38548214129417715609474415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51397618839223620812632553 38548214129417715609474415)
    ·
      refine ⟨57822321194126573414211623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38548214129417715609474415 57822321194126573414211623)
      ·
        refine ⟨86733481791189860121317435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57822321194126573414211623 86733481791189860121317435)
        ·
          refine ⟨130100222686784790181976153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86733481791189860121317435 130100222686784790181976153)
          ·
            refine ⟨97575167015088592636482115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130100222686784790181976153 97575167015088592636482115)
            ·
              refine ⟨146362750522632888954723173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97575167015088592636482115 146362750522632888954723173)
              ·
                refine ⟨27443015722993666679010595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146362750522632888954723173 27443015722993666679010595)
                ·
                  refine ⟨41164523584490500018515893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27443015722993666679010595 41164523584490500018515893)
                  ·
                    refine ⟨3859174086045984376735865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41164523584490500018515893 3859174086045984376735865)
                    ·
                      refine ⟨2894380564534488282551899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859174086045984376735865 2894380564534488282551899)
                      ·
                        rfl

theorem cell23_5636786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_5636786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636786 prefixEnd_5636786 := by exact prefixLift 5636786
  have htrace : WordTrace (prefixWord ++ tailWord_5636786) baseStart_5636786 baseEnd_5636786 := by
    simpa [prefixWord, tailWord_5636786, baseEnd_5636786] using wordTrace_append hprefix tailTrace_5636786
  have hstable : (prefixWord ++ tailWord_5636786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636786).length < 2 ^ (prefixWord ++ tailWord_5636786).sum := by decide
  have hdescent : baseEnd_5636786 < baseStart_5636786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636796 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_5636796 : Nat := 118140960795 + 5636796 * 2 ^ 59
def prefixEnd_5636796 : Nat := 4983230072969 + 3 ^ 40 * 5636796 * 2
def baseEnd_5636796 : Nat := 964795233113677747808951

theorem tailTrace_5636796 : CollatzResearch.WordTrace tailWord_5636796 prefixEnd_5636796 964795233113677747808951 := by
  unfold tailWord_5636796
  simp only [CollatzResearch.WordTrace]
  refine ⟨102795420043429127479197121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137060560057905503305596161 102795420043429127479197121)
  ·
    refine ⟨77096565032571845609397841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102795420043429127479197121 77096565032571845609397841)
    ·
      refine ⟨57822423774428884207048381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77096565032571845609397841 57822423774428884207048381)
      ·
        refine ⟨21683408915410831577643143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57822423774428884207048381 21683408915410831577643143)
        ·
          refine ⟨32525113373116247366464715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21683408915410831577643143 32525113373116247366464715)
          ·
            refine ⟨48787670059674371049697073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32525113373116247366464715 48787670059674371049697073)
            ·
              refine ⟨36590752544755778287272805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48787670059674371049697073 36590752544755778287272805)
              ·
                refine ⟨6860766102141708428863651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36590752544755778287272805 6860766102141708428863651)
                ·
                  refine ⟨10291149153212562643295477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6860766102141708428863651 10291149153212562643295477)
                  ·
                    refine ⟨964795233113677747808951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10291149153212562643295477 964795233113677747808951)
                    ·
                      rfl

theorem cell23_5636796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_5636796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636796 prefixEnd_5636796 := by exact prefixLift 5636796
  have htrace : WordTrace (prefixWord ++ tailWord_5636796) baseStart_5636796 baseEnd_5636796 := by
    simpa [prefixWord, tailWord_5636796, baseEnd_5636796] using wordTrace_append hprefix tailTrace_5636796
  have hstable : (prefixWord ++ tailWord_5636796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636796).length < 2 ^ (prefixWord ++ tailWord_5636796).sum := by decide
  have hdescent : baseEnd_5636796 < baseStart_5636796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636810 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_5636810 : Nat := 118140960795 + 5636810 * 2 ^ 59
def prefixEnd_5636810 : Nat := 4983230072969 + 3 ^ 40 * 5636810 * 2
def baseEnd_5636810 : Nat := 2894392888070196188651789

theorem tailTrace_5636810 : CollatzResearch.WordTrace tailWord_5636810 prefixEnd_5636810 2894392888070196188651789 := by
  unfold tailWord_5636810
  simp only [CollatzResearch.WordTrace]
  refine ⟨51397837677201883837350971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137060900472538356899602589 51397837677201883837350971)
  ·
    refine ⟨77096756515802825756026457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51397837677201883837350971 77096756515802825756026457)
    ·
      refine ⟨57822567386852119317019843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77096756515802825756026457 57822567386852119317019843)
      ·
        refine ⟨86733851080278178975529765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57822567386852119317019843 86733851080278178975529765)
        ·
          refine ⟨16262597077552158557911831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86733851080278178975529765 16262597077552158557911831)
          ·
            refine ⟨24393895616328237836867747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16262597077552158557911831 24393895616328237836867747)
            ·
              refine ⟨36590843424492356755301621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24393895616328237836867747 36590843424492356755301621)
              ·
                refine ⟨3430391571046158445809527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36590843424492356755301621 3430391571046158445809527)
                ·
                  refine ⟨5145587356569237668714291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430391571046158445809527 5145587356569237668714291)
                  ·
                    refine ⟨7718381034853856503071437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145587356569237668714291 7718381034853856503071437)
                    ·
                      refine ⟨2894392888070196188651789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7718381034853856503071437 2894392888070196188651789)
                      ·
                        rfl

theorem cell23_5636810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_5636810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636810 prefixEnd_5636810 := by exact prefixLift 5636810
  have htrace : WordTrace (prefixWord ++ tailWord_5636810) baseStart_5636810 baseEnd_5636810 := by
    simpa [prefixWord, tailWord_5636810, baseEnd_5636810] using wordTrace_append hprefix tailTrace_5636810
  have hstable : (prefixWord ++ tailWord_5636810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636810).length < 2 ^ (prefixWord ++ tailWord_5636810).sum := by decide
  have hdescent : baseEnd_5636810 < baseStart_5636810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636826 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_5636826 : Nat := 118140960795 + 5636826 * 2 ^ 59
def prefixEnd_5636826 : Nat := 4983230072969 + 3 ^ 40 * 5636826 * 2
def baseEnd_5636826 : Nat := 964800367920222708683905

theorem tailTrace_5636826 : CollatzResearch.WordTrace tailWord_5636826 prefixEnd_5636826 964800367920222708683905 := by
  unfold tailWord_5636826
  simp only [CollatzResearch.WordTrace]
  refine ⟨51397983569187392520496583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137061289517833046721324221 51397983569187392520496583)
  ·
    refine ⟨77096975353781088780744875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51397983569187392520496583 77096975353781088780744875)
    ·
      refine ⟨115645463030671633171117313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77096975353781088780744875 115645463030671633171117313)
      ·
        refine ⟨86734097273003724878337985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115645463030671633171117313 86734097273003724878337985)
        ·
          refine ⟨65050572954752793658753489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86734097273003724878337985 65050572954752793658753489)
          ·
            refine ⟨48787929716064595244065117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65050572954752793658753489 48787929716064595244065117)
            ·
              refine ⟨18295473643524223216524419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48787929716064595244065117 18295473643524223216524419)
              ·
                refine ⟨27443210465286334824786629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18295473643524223216524419 27443210465286334824786629)
                ·
                  refine ⟨5145601962241187779647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27443210465286334824786629 5145601962241187779647493)
                  ·
                    refine ⟨964800367920222708683905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145601962241187779647493 964800367920222708683905)
                    ·
                      rfl

theorem cell23_5636826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_5636826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636826 prefixEnd_5636826 := by exact prefixLift 5636826
  have htrace : WordTrace (prefixWord ++ tailWord_5636826) baseStart_5636826 baseEnd_5636826 := by
    simpa [prefixWord, tailWord_5636826, baseEnd_5636826] using wordTrace_append hprefix tailTrace_5636826
  have hstable : (prefixWord ++ tailWord_5636826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636826).length < 2 ^ (prefixWord ++ tailWord_5636826).sum := by decide
  have hdescent : baseEnd_5636826 < baseStart_5636826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636836 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_5636836 : Nat := 118140960795 + 5636836 * 2 ^ 59
def prefixEnd_5636836 : Nat := 4983230072969 + 3 ^ 40 * 5636836 * 2
def baseEnd_5636836 : Nat := 2894406238567213086926669

theorem tailTrace_5636836 : CollatzResearch.WordTrace tailWord_5636836 prefixEnd_5636836 2894406238567213086926669 := by
  unfold tailWord_5636836
  simp only [CollatzResearch.WordTrace]
  refine ⟨102796149503356670894925181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137061532671142227859900241 102796149503356670894925181)
  ·
    refine ⟨38548556063758751585596943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102796149503356670894925181 38548556063758751585596943)
    ·
      refine ⟨57822834095638127378395415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38548556063758751585596943 57822834095638127378395415)
      ·
        refine ⟨86734251143457191067593123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57822834095638127378395415 86734251143457191067593123)
        ·
          refine ⟨130101376715185786601389685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86734251143457191067593123 130101376715185786601389685)
          ·
            refine ⟨12197004067048667493880283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130101376715185786601389685 12197004067048667493880283)
            ·
              refine ⟨18295506100573001240820425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12197004067048667493880283 18295506100573001240820425)
              ·
                refine ⟨13721629575429750930615319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18295506100573001240820425 13721629575429750930615319)
                ·
                  refine ⟨20582444363144626395922979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13721629575429750930615319 20582444363144626395922979)
                  ·
                    refine ⟨30873666544716939593884469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20582444363144626395922979 30873666544716939593884469)
                    ·
                      refine ⟨2894406238567213086926669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30873666544716939593884469 2894406238567213086926669)
                      ·
                        rfl

theorem cell23_5636836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_5636836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636836 prefixEnd_5636836 := by exact prefixLift 5636836
  have htrace : WordTrace (prefixWord ++ tailWord_5636836) baseStart_5636836 baseEnd_5636836 := by
    simpa [prefixWord, tailWord_5636836, baseEnd_5636836] using wordTrace_append hprefix tailTrace_5636836
  have hstable : (prefixWord ++ tailWord_5636836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636836).length < 2 ^ (prefixWord ++ tailWord_5636836).sum := by decide
  have hdescent : baseEnd_5636836 < baseStart_5636836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636846 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_5636846 : Nat := 118140960795 + 5636846 * 2 ^ 59
def prefixEnd_5636846 : Nat := 4983230072969 + 3 ^ 40 * 5636846 * 2
def baseEnd_5636846 : Nat := 2894411373373758047801623

theorem tailTrace_5636846 : CollatzResearch.WordTrace tailWord_5636846 prefixEnd_5636846 2894411373373758047801623 := by
  unfold tailWord_5636846
  simp only [CollatzResearch.WordTrace]
  refine ⟨25699082967084639187214299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137061775824451408998476261 25699082967084639187214299)
  ·
    refine ⟨38548624450626958780821449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25699082967084639187214299 38548624450626958780821449)
    ·
      refine ⟨28911468337970219085616087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38548624450626958780821449 28911468337970219085616087)
      ·
        refine ⟨43367202506955328628424131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28911468337970219085616087 43367202506955328628424131)
        ·
          refine ⟨65050803760432992942636197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43367202506955328628424131 65050803760432992942636197)
          ·
            refine ⟨12197025705081186176744287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65050803760432992942636197 12197025705081186176744287)
            ·
              refine ⟨18295538557621779265116431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12197025705081186176744287 18295538557621779265116431)
              ·
                refine ⟨27443307836432668897674647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18295538557621779265116431 27443307836432668897674647)
                ·
                  refine ⟨41164961754649003346511971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27443307836432668897674647 41164961754649003346511971)
                  ·
                    refine ⟨61747442631973505019767957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41164961754649003346511971 61747442631973505019767957)
                    ·
                      refine ⟨2894411373373758047801623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61747442631973505019767957 2894411373373758047801623)
                      ·
                        rfl

theorem cell23_5636846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_5636846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636846 prefixEnd_5636846 := by exact prefixLift 5636846
  have htrace : WordTrace (prefixWord ++ tailWord_5636846) baseStart_5636846 baseEnd_5636846 := by
    simpa [prefixWord, tailWord_5636846, baseEnd_5636846] using wordTrace_append hprefix tailTrace_5636846
  have hstable : (prefixWord ++ tailWord_5636846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636846).length < 2 ^ (prefixWord ++ tailWord_5636846).sum := by decide
  have hdescent : baseEnd_5636846 < baseStart_5636846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636850 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_5636850 : Nat := 118140960795 + 5636850 * 2 ^ 59
def prefixEnd_5636850 : Nat := 4983230072969 + 3 ^ 40 * 5636850 * 2
def baseEnd_5636850 : Nat := 2894413427296376032151605

theorem tailTrace_5636850 : CollatzResearch.WordTrace tailWord_5636850 prefixEnd_5636850 2894413427296376032151605 := by
  unfold tailWord_5636850
  simp only [CollatzResearch.WordTrace]
  refine ⟨51398202407165655545215001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137061873085775081453906669 51398202407165655545215001)
  ·
    refine ⟨38548651805374241658911251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51398202407165655545215001 38548651805374241658911251)
    ·
      refine ⟨57822977708061362488366877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38548651805374241658911251 57822977708061362488366877)
      ·
        refine ⟨21683616640523010933137579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57822977708061362488366877 21683616640523010933137579)
        ·
          refine ⟨32525424960784516399706369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21683616640523010933137579 32525424960784516399706369)
          ·
            refine ⟨24394068720588387299779777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32525424960784516399706369 24394068720588387299779777)
            ·
              refine ⟨18295551540441290474834833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24394068720588387299779777 18295551540441290474834833)
              ·
                refine ⟨13721663655330967856126125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18295551540441290474834833 13721663655330967856126125)
                ·
                  refine ⟨5145623870749112946047297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13721663655330967856126125 5145623870749112946047297)
                  ·
                    refine ⟨3859217903061834709535473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5145623870749112946047297 3859217903061834709535473)
                    ·
                      refine ⟨2894413427296376032151605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859217903061834709535473 2894413427296376032151605)
                      ·
                        rfl

theorem cell23_5636850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_5636850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636850 prefixEnd_5636850 := by exact prefixLift 5636850
  have htrace : WordTrace (prefixWord ++ tailWord_5636850) baseStart_5636850 baseEnd_5636850 := by
    simpa [prefixWord, tailWord_5636850, baseEnd_5636850] using wordTrace_append hprefix tailTrace_5636850
  have hstable : (prefixWord ++ tailWord_5636850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636850).length < 2 ^ (prefixWord ++ tailWord_5636850).sum := by decide
  have hdescent : baseEnd_5636850 < baseStart_5636850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636879 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_5636879 : Nat := 118140960795 + 5636879 * 2 ^ 59
def prefixEnd_5636879 : Nat := 4983230072969 + 3 ^ 40 * 5636879 * 2
def baseEnd_5636879 : Nat := 2894428318235356418688971

theorem tailTrace_5636879 : CollatzResearch.WordTrace tailWord_5636879 prefixEnd_5636879 2894428318235356418688971 := by
  unfold tailWord_5636879
  simp only [CollatzResearch.WordTrace]
  refine ⟨205593867345557560133665691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137062578230371706755777127 205593867345557560133665691)
  ·
    refine ⟨308390801018336340200498537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205593867345557560133665691 308390801018336340200498537)
    ·
      refine ⟨231293100763752255150373903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308390801018336340200498537 231293100763752255150373903)
      ·
        refine ⟨346939651145628382725560855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231293100763752255150373903 346939651145628382725560855)
        ·
          refine ⟨520409476718442574088341283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346939651145628382725560855 520409476718442574088341283)
          ·
            refine ⟨780614215077663861132511925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520409476718442574088341283 780614215077663861132511925)
            ·
              refine ⟨73182582663530986981172993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 780614215077663861132511925 73182582663530986981172993)
              ·
                refine ⟨54886936997648240235879745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73182582663530986981172993 54886936997648240235879745)
                ·
                  refine ⟨41165202748236180176909809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54886936997648240235879745 41165202748236180176909809)
                  ·
                    refine ⟨30873902061177135132682357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41165202748236180176909809 30873902061177135132682357)
                    ·
                      refine ⟨2894428318235356418688971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30873902061177135132682357 2894428318235356418688971)
                      ·
                        rfl

theorem cell23_5636879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_5636879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636879 prefixEnd_5636879 := by exact prefixLift 5636879
  have htrace : WordTrace (prefixWord ++ tailWord_5636879) baseStart_5636879 baseEnd_5636879 := by
    simpa [prefixWord, tailWord_5636879, baseEnd_5636879] using wordTrace_append hprefix tailTrace_5636879
  have hstable : (prefixWord ++ tailWord_5636879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636879).length < 2 ^ (prefixWord ++ tailWord_5636879).sum := by decide
  have hdescent : baseEnd_5636879 < baseStart_5636879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636883 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 3]
def baseStart_5636883 : Nat := 118140960795 + 5636883 * 2 ^ 59
def prefixEnd_5636883 : Nat := 4983230072969 + 3 ^ 40 * 5636883 * 2
def baseEnd_5636883 : Nat := 2894430372157974403038953

theorem tailTrace_5636883 : CollatzResearch.WordTrace tailWord_5636883 prefixEnd_5636883 2894430372157974403038953 := by
  unfold tailWord_5636883
  simp only [CollatzResearch.WordTrace]
  refine ⟨205594013237543068816811303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137062675491695379211207535 205594013237543068816811303)
  ·
    refine ⟨308391019856314603225216955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205594013237543068816811303 308391019856314603225216955)
    ·
      refine ⟨462586529784471904837825433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308391019856314603225216955 462586529784471904837825433)
      ·
        refine ⟨346939897338353928628369075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462586529784471904837825433 346939897338353928628369075)
        ·
          refine ⟨520409846007530892942553613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346939897338353928628369075 520409846007530892942553613)
          ·
            refine ⟨195153692252824084853457605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 520409846007530892942553613 195153692252824084853457605)
            ·
              refine ⟨36591317297404515910023301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195153692252824084853457605 36591317297404515910023301)
              ·
                refine ⟨6860871993263346733129369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36591317297404515910023301 6860871993263346733129369)
                ·
                  refine ⟨5145653994947510049847027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6860871993263346733129369 5145653994947510049847027)
                  ·
                    refine ⟨7718480992421265074770541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145653994947510049847027 7718480992421265074770541)
                    ·
                      refine ⟨2894430372157974403038953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7718480992421265074770541 2894430372157974403038953)
                      ·
                        rfl

theorem cell23_5636883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_5636883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636883 prefixEnd_5636883 := by exact prefixLift 5636883
  have htrace : WordTrace (prefixWord ++ tailWord_5636883) baseStart_5636883 baseEnd_5636883 := by
    simpa [prefixWord, tailWord_5636883, baseEnd_5636883] using wordTrace_append hprefix tailTrace_5636883
  have hstable : (prefixWord ++ tailWord_5636883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636883).length < 2 ^ (prefixWord ++ tailWord_5636883).sum := by decide
  have hdescent : baseEnd_5636883 < baseStart_5636883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636899 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 8]
def baseStart_5636899 : Nat := 118140960795 + 5636899 * 2 ^ 59
def prefixEnd_5636899 : Nat := 4983230072969 + 3 ^ 40 * 5636899 * 2
def baseEnd_5636899 : Nat := 964812862616148780146293

theorem tailTrace_5636899 : CollatzResearch.WordTrace tailWord_5636899 prefixEnd_5636899 964812862616148780146293 := by
  unfold tailWord_5636899
  simp only [CollatzResearch.WordTrace]
  refine ⟨205594596805485103549393751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137063064536990069032929167 205594596805485103549393751)
  ·
    refine ⟨308391895208227655324090627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205594596805485103549393751 308391895208227655324090627)
    ·
      refine ⟨462587842812341482986135941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308391895208227655324090627 462587842812341482986135941)
      ·
        refine ⟨86735220527314028059900489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 462587842812341482986135941 86735220527314028059900489)
        ·
          refine ⟨65051415395485521044925367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86735220527314028059900489 65051415395485521044925367)
          ·
            refine ⟨97577123093228281567388051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65051415395485521044925367 97577123093228281567388051)
            ·
              refine ⟨146365684639842422351082077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97577123093228281567388051 146365684639842422351082077)
              ·
                refine ⟨54887131739940908381655779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146365684639842422351082077 54887131739940908381655779)
                ·
                  refine ⟨82330697609911362572483669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54887131739940908381655779 82330697609911362572483669)
                  ·
                    refine ⟨964812862616148780146293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82330697609911362572483669 964812862616148780146293)
                    ·
                      rfl

theorem cell23_5636899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_5636899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636899 prefixEnd_5636899 := by exact prefixLift 5636899
  have htrace : WordTrace (prefixWord ++ tailWord_5636899) baseStart_5636899 baseEnd_5636899 := by
    simpa [prefixWord, tailWord_5636899, baseEnd_5636899] using wordTrace_append hprefix tailTrace_5636899
  have hstable : (prefixWord ++ tailWord_5636899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636899).length < 2 ^ (prefixWord ++ tailWord_5636899).sum := by decide
  have hdescent : baseEnd_5636899 < baseStart_5636899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636927 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 1, 3, 2]
def baseStart_5636927 : Nat := 118140960795 + 5636927 * 2 ^ 59
def prefixEnd_5636927 : Nat := 4983230072969 + 3 ^ 40 * 5636927 * 2
def baseEnd_5636927 : Nat := 2894452965306772230888751

theorem tailTrace_5636927 : CollatzResearch.WordTrace tailWord_5636927 prefixEnd_5636927 2894452965306772230888751 := by
  unfold tailWord_5636927
  simp only [CollatzResearch.WordTrace]
  refine ⟨205595618049383664331413035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137063745366255776220942023 205595618049383664331413035)
  ·
    refine ⟨308393427074075496497119553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205595618049383664331413035 308393427074075496497119553)
    ·
      refine ⟨231295070305556622372839665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308393427074075496497119553 231295070305556622372839665)
      ·
        refine ⟨173471302729167466779629749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231295070305556622372839665 173471302729167466779629749)
        ·
          refine ⟨16262934630859450010590289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173471302729167466779629749 16262934630859450010590289)
          ·
            refine ⟨12197200973144587507942717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16262934630859450010590289 12197200973144587507942717)
            ·
              refine ⟨4573950364929220315478519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12197200973144587507942717 4573950364929220315478519)
              ·
                refine ⟨6860925547393830473217779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573950364929220315478519 6860925547393830473217779)
                ·
                  refine ⟨10291388321090745709826669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6860925547393830473217779 10291388321090745709826669)
                  ·
                    refine ⟨3859270620409029641185001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10291388321090745709826669 3859270620409029641185001)
                    ·
                      refine ⟨2894452965306772230888751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859270620409029641185001 2894452965306772230888751)
                      ·
                        rfl

theorem cell23_5636927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_5636927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636927 prefixEnd_5636927 := by exact prefixLift 5636927
  have htrace : WordTrace (prefixWord ++ tailWord_5636927) baseStart_5636927 baseEnd_5636927 := by
    simpa [prefixWord, tailWord_5636927, baseEnd_5636927] using wordTrace_append hprefix tailTrace_5636927
  have hstable : (prefixWord ++ tailWord_5636927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636927).length < 2 ^ (prefixWord ++ tailWord_5636927).sum := by decide
  have hdescent : baseEnd_5636927 < baseStart_5636927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636936 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_5636936 : Nat := 118140960795 + 5636936 * 2 ^ 59
def prefixEnd_5636936 : Nat := 4983230072969 + 3 ^ 40 * 5636936 * 2
def baseEnd_5636936 : Nat := 2894457586632662695676209

theorem tailTrace_5636936 : CollatzResearch.WordTrace tailWord_5636936 prefixEnd_5636936 2894457586632662695676209 := by
  unfold tailWord_5636936
  simp only [CollatzResearch.WordTrace]
  refine ⟨102797973153175529434245331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137063964204234039245660441 102797973153175529434245331)
  ·
    refine ⟨154196959729763294151367997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102797973153175529434245331 154196959729763294151367997)
    ·
      refine ⟨57823859898661235306762999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154196959729763294151367997 57823859898661235306762999)
      ·
        refine ⟨86735789847991852960144499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57823859898661235306762999 86735789847991852960144499)
        ·
          refine ⟨130103684771987779440216749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86735789847991852960144499 130103684771987779440216749)
          ·
            refine ⟨48788881789495417290081281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130103684771987779440216749 48788881789495417290081281)
            ·
              refine ⟨36591661342121562967560961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48788881789495417290081281 36591661342121562967560961)
              ·
                refine ⟨27443746006591172225670721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36591661342121562967560961 27443746006591172225670721)
                ·
                  refine ⟨20582809504943379169253041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27443746006591172225670721 20582809504943379169253041)
                  ·
                    refine ⟨15437107128707534376939781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20582809504943379169253041 15437107128707534376939781)
                    ·
                      refine ⟨2894457586632662695676209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15437107128707534376939781 2894457586632662695676209)
                      ·
                        rfl

theorem cell23_5636936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_5636936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636936 prefixEnd_5636936 := by exact prefixLift 5636936
  have htrace : WordTrace (prefixWord ++ tailWord_5636936) baseStart_5636936 baseEnd_5636936 := by
    simpa [prefixWord, tailWord_5636936, baseEnd_5636936] using wordTrace_append hprefix tailTrace_5636936
  have hstable : (prefixWord ++ tailWord_5636936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636936).length < 2 ^ (prefixWord ++ tailWord_5636936).sum := by decide
  have hdescent : baseEnd_5636936 < baseStart_5636936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5636946 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_5636946 : Nat := 118140960795 + 5636946 * 2 ^ 59
def prefixEnd_5636946 : Nat := 4983230072969 + 3 ^ 40 * 5636946 * 2
def baseEnd_5636946 : Nat := 321606969048800850727907

theorem tailTrace_5636946 : CollatzResearch.WordTrace tailWord_5636946 prefixEnd_5636946 321606969048800850727907 := by
  unfold tailWord_5636946
  simp only [CollatzResearch.WordTrace]
  refine ⟨51399077759078707644088673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137064207357543220384236461 51399077759078707644088673)
  ·
    refine ⟨38549308319309030733066505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51399077759078707644088673 38549308319309030733066505)
    ·
      refine ⟨28911981239481773049799879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38549308319309030733066505 28911981239481773049799879)
      ·
        refine ⟨43367971859222659574699819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28911981239481773049799879 43367971859222659574699819)
        ·
          refine ⟨65051957788833989362049729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43367971859222659574699819 65051957788833989362049729)
          ·
            refine ⟨48788968341625492021537297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65051957788833989362049729 48788968341625492021537297)
            ·
              refine ⟨36591726256219119016152973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48788968341625492021537297 36591726256219119016152973)
              ·
                refine ⟨13721897346082169631057365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36591726256219119016152973 13721897346082169631057365)
                ·
                  refine ⟨321606969048800850727907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13721897346082169631057365 321606969048800850727907)
                  ·
                    rfl

theorem cell23_5636946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_5636946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5636946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5636946 prefixEnd_5636946 := by exact prefixLift 5636946
  have htrace : WordTrace (prefixWord ++ tailWord_5636946) baseStart_5636946 baseEnd_5636946 := by
    simpa [prefixWord, tailWord_5636946, baseEnd_5636946] using wordTrace_append hprefix tailTrace_5636946
  have hstable : (prefixWord ++ tailWord_5636946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5636946).length < 2 ^ (prefixWord ++ tailWord_5636946).sum := by decide
  have hdescent : baseEnd_5636946 < baseStart_5636946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5636946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637033 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_5637033 : Nat := 118140960795 + 5637033 * 2 ^ 59
def prefixEnd_5637033 : Nat := 4983230072969 + 3 ^ 40 * 5637033 * 2
def baseEnd_5637033 : Nat := 2894507394256148816163263

theorem tailTrace_5637033 : CollatzResearch.WordTrace tailWord_5637033 prefixEnd_5637033 2894507394256148816163263 := by
  unfold tailWord_5637033
  simp only [CollatzResearch.WordTrace]
  refine ⟨205599484186999644434771753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137066322791333096289847835 205599484186999644434771753)
  ·
    refine ⟨154199613140249733326078815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205599484186999644434771753 154199613140249733326078815)
    ·
      refine ⟨231299419710374599989118223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154199613140249733326078815 231299419710374599989118223)
      ·
        refine ⟨346949129565561899983677335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231299419710374599989118223 346949129565561899983677335)
        ·
          refine ⟨520423694348342849975516003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346949129565561899983677335 520423694348342849975516003)
          ·
            refine ⟨780635541522514274963274005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520423694348342849975516003 780635541522514274963274005)
            ·
              refine ⟨36592291008867856638903469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 780635541522514274963274005 36592291008867856638903469)
              ·
                refine ⟨13722109128325446239588801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36592291008867856638903469 13722109128325446239588801)
                ·
                  refine ⟨10291581846244084679691601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13722109128325446239588801 10291581846244084679691601)
                  ·
                    refine ⟨7718686384683063509768701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10291581846244084679691601 7718686384683063509768701)
                    ·
                      refine ⟨2894507394256148816163263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7718686384683063509768701 2894507394256148816163263)
                      ·
                        rfl

theorem cell23_5637033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_5637033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637033 prefixEnd_5637033 := by exact prefixLift 5637033
  have htrace : WordTrace (prefixWord ++ tailWord_5637033) baseStart_5637033 baseEnd_5637033 := by
    simpa [prefixWord, tailWord_5637033, baseEnd_5637033] using wordTrace_append hprefix tailTrace_5637033
  have hstable : (prefixWord ++ tailWord_5637033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637033).length < 2 ^ (prefixWord ++ tailWord_5637033).sum := by decide
  have hdescent : baseEnd_5637033 < baseStart_5637033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637066 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_5637066 : Nat := 118140960795 + 5637066 * 2 ^ 59
def prefixEnd_5637066 : Nat := 4983230072969 + 3 ^ 40 * 5637066 * 2
def baseEnd_5637066 : Nat := 964841446372582395683537

theorem tailTrace_5637066 : CollatzResearch.WordTrace tailWord_5637066 prefixEnd_5637066 964841446372582395683537 := by
  unfold tailWord_5637066
  simp only [CollatzResearch.WordTrace]
  refine ⟨51400171948970022767680763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137067125197253394047148701 51400171948970022767680763)
  ·
    refine ⟨77100257923455034151521145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51400171948970022767680763 77100257923455034151521145)
    ·
      refine ⟨57825193442591275613640859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77100257923455034151521145 57825193442591275613640859)
      ·
        refine ⟨86737790163886913420461289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57825193442591275613640859 86737790163886913420461289)
        ·
          refine ⟨65053342622915185065345967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86737790163886913420461289 65053342622915185065345967)
          ·
            refine ⟨97580013934372777598018951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65053342622915185065345967 97580013934372777598018951)
            ·
              refine ⟨146370020901559166397028427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97580013934372777598018951 146370020901559166397028427)
              ·
                refine ⟨219555031352338749595542641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146370020901559166397028427 219555031352338749595542641)
                ·
                  refine ⟨164666273514254062196656981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219555031352338749595542641 164666273514254062196656981)
                  ·
                    refine ⟨964841446372582395683537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 164666273514254062196656981 964841446372582395683537)
                    ·
                      rfl

theorem cell23_5637066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_5637066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637066 prefixEnd_5637066 := by exact prefixLift 5637066
  have htrace : WordTrace (prefixWord ++ tailWord_5637066) baseStart_5637066 baseEnd_5637066 := by
    simpa [prefixWord, tailWord_5637066, baseEnd_5637066] using wordTrace_append hprefix tailTrace_5637066
  have hstable : (prefixWord ++ tailWord_5637066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637066).length < 2 ^ (prefixWord ++ tailWord_5637066).sum := by decide
  have hdescent : baseEnd_5637066 < baseStart_5637066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637070 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_5637070 : Nat := 118140960795 + 5637070 * 2 ^ 59
def prefixEnd_5637070 : Nat := 4983230072969 + 3 ^ 40 * 5637070 * 2
def baseEnd_5637070 : Nat := 321614043671151685711177

theorem tailTrace_5637070 : CollatzResearch.WordTrace tailWord_5637070 prefixEnd_5637070 321614043671151685711177 := by
  unfold tailWord_5637070
  simp only [CollatzResearch.WordTrace]
  refine ⟨25700104210983199969233583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137067222458577066502579109 25700104210983199969233583)
  ·
    refine ⟨38550156316474799953850375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25700104210983199969233583 38550156316474799953850375)
    ·
      refine ⟨57825234474712199930775563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38550156316474799953850375 57825234474712199930775563)
      ·
        refine ⟨86737851712068299896163345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57825234474712199930775563 86737851712068299896163345)
        ·
          refine ⟨65053388784051224922122509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86737851712068299896163345 65053388784051224922122509)
          ·
            refine ⟨24395020794019209345795941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65053388784051224922122509 24395020794019209345795941)
            ·
              refine ⟨4574066398878601752336739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24395020794019209345795941 4574066398878601752336739)
              ·
                refine ⟨6861099598317902628505109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574066398878601752336739 6861099598317902628505109)
                ·
                  refine ⟨321614043671151685711177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6861099598317902628505109 321614043671151685711177)
                  ·
                    rfl

theorem cell23_5637070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_5637070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637070 prefixEnd_5637070 := by exact prefixLift 5637070
  have htrace : WordTrace (prefixWord ++ tailWord_5637070) baseStart_5637070 baseEnd_5637070 := by
    simpa [prefixWord, tailWord_5637070, baseEnd_5637070] using wordTrace_append hprefix tailTrace_5637070
  have hstable : (prefixWord ++ tailWord_5637070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637070).length < 2 ^ (prefixWord ++ tailWord_5637070).sum := by decide
  have hdescent : baseEnd_5637070 < baseStart_5637070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637130 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_5637130 : Nat := 118140960795 + 5637130 * 2 ^ 59
def prefixEnd_5637130 : Nat := 4983230072969 + 3 ^ 40 * 5637130 * 2
def baseEnd_5637130 : Nat := 964852400626544978883439

theorem tailTrace_5637130 : CollatzResearch.WordTrace tailWord_5637130 prefixEnd_5637130 964852400626544978883439 := by
  unfold tailWord_5637130
  simp only [CollatzResearch.WordTrace]
  refine ⟨51400755516912057500263211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137068681378432153334035229 51400755516912057500263211)
  ·
    refine ⟨77101133275368086250394817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51400755516912057500263211 77101133275368086250394817)
    ·
      refine ⟨57825849956526064687796113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77101133275368086250394817 57825849956526064687796113)
      ·
        refine ⟨43369387467394548515847085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57825849956526064687796113 43369387467394548515847085)
        ·
          refine ⟨16263520300272955693442657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43369387467394548515847085 16263520300272955693442657)
          ·
            refine ⟨12197640225204716770081993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16263520300272955693442657 12197640225204716770081993)
            ·
              refine ⟨9148230168903537577561495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12197640225204716770081993 9148230168903537577561495)
              ·
                refine ⟨13722345253355306366342243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9148230168903537577561495 13722345253355306366342243)
                ·
                  refine ⟨20583517880032959549513365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13722345253355306366342243 20583517880032959549513365)
                  ·
                    refine ⟨964852400626544978883439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20583517880032959549513365 964852400626544978883439)
                    ·
                      rfl

theorem cell23_5637130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_5637130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637130 prefixEnd_5637130 := by exact prefixLift 5637130
  have htrace : WordTrace (prefixWord ++ tailWord_5637130) baseStart_5637130 baseEnd_5637130 := by
    simpa [prefixWord, tailWord_5637130, baseEnd_5637130] using wordTrace_append hprefix tailTrace_5637130
  have hstable : (prefixWord ++ tailWord_5637130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637130).length < 2 ^ (prefixWord ++ tailWord_5637130).sum := by decide
  have hdescent : baseEnd_5637130 < baseStart_5637130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637154 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_5637154 : Nat := 118140960795 + 5637154 * 2 ^ 59
def prefixEnd_5637154 : Nat := 4983230072969 + 3 ^ 40 * 5637154 * 2
def baseEnd_5637154 : Nat := 2894569525415342842750207

theorem tailTrace_5637154 : CollatzResearch.WordTrace tailWord_5637154 prefixEnd_5637154 2894569525415342842750207 := by
  unfold tailWord_5637154
  simp only [CollatzResearch.WordTrace]
  refine ⟨51400974354890320524981629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137069264946374188066617677 51400974354890320524981629)
  ·
    refine ⟨19275365383083870196868111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51400974354890320524981629 19275365383083870196868111)
    ·
      refine ⟨28913048074625805295302167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19275365383083870196868111 28913048074625805295302167)
      ·
        refine ⟨43369572111938707942953251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28913048074625805295302167 43369572111938707942953251)
        ·
          refine ⟨65054358167908061914429877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43369572111938707942953251 65054358167908061914429877)
          ·
            refine ⟨6098846078241380804477801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65054358167908061914429877 6098846078241380804477801)
            ·
              refine ⟨4574134558681035603358351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6098846078241380804477801 4574134558681035603358351)
              ·
                refine ⟨6861201838021553405037527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574134558681035603358351 6861201838021553405037527)
                ·
                  refine ⟨10291802757032330107556291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6861201838021553405037527 10291802757032330107556291)
                  ·
                    refine ⟨15437704135548495161334437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10291802757032330107556291 15437704135548495161334437)
                    ·
                      refine ⟨2894569525415342842750207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15437704135548495161334437 2894569525415342842750207)
                      ·
                        rfl

theorem cell23_5637154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_5637154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637154 prefixEnd_5637154 := by exact prefixLift 5637154
  have htrace : WordTrace (prefixWord ++ tailWord_5637154) baseStart_5637154 baseEnd_5637154 := by
    simpa [prefixWord, tailWord_5637154, baseEnd_5637154] using wordTrace_append hprefix tailTrace_5637154
  have hstable : (prefixWord ++ tailWord_5637154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637154).length < 2 ^ (prefixWord ++ tailWord_5637154).sum := by decide
  have hdescent : baseEnd_5637154 < baseStart_5637154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637233 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 7]
def baseStart_5637233 : Nat := 118140960795 + 5637233 * 2 ^ 59
def prefixEnd_5637233 : Nat := 4983230072969 + 3 ^ 40 * 5637233 * 2
def baseEnd_5637233 : Nat := 321623343376338670406927

theorem tailTrace_5637233 : CollatzResearch.WordTrace tailWord_5637233 prefixEnd_5637233 321623343376338670406927 := by
  unfold tailWord_5637233
  simp only [CollatzResearch.WordTrace]
  refine ⟨205606778786275078592052353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137071185857516719061368235 205606778786275078592052353)
  ·
    refine ⟨154205084089706308944039265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205606778786275078592052353 154205084089706308944039265)
    ·
      refine ⟨115653813067279731708029449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154205084089706308944039265 115653813067279731708029449)
      ·
        refine ⟨86740359800459798781022087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115653813067279731708029449 86740359800459798781022087)
        ·
          refine ⟨130110539700689698171533131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86740359800459798781022087 130110539700689698171533131)
          ·
            refine ⟨195165809551034547257299697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130110539700689698171533131 195165809551034547257299697)
            ·
              refine ⟨146374357163275910442974773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195165809551034547257299697 146374357163275910442974773)
              ·
                refine ⟨13722595984057116604028885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146374357163275910442974773 13722595984057116604028885)
                ·
                  refine ⟨321623343376338670406927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13722595984057116604028885 321623343376338670406927)
                  ·
                    rfl

theorem cell23_5637233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_5637233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637233 prefixEnd_5637233 := by exact prefixLift 5637233
  have htrace : WordTrace (prefixWord ++ tailWord_5637233) baseStart_5637233 baseEnd_5637233 := by
    simpa [prefixWord, tailWord_5637233, baseEnd_5637233] using wordTrace_append hprefix tailTrace_5637233
  have hstable : (prefixWord ++ tailWord_5637233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637233).length < 2 ^ (prefixWord ++ tailWord_5637233).sum := by decide
  have hdescent : baseEnd_5637233 < baseStart_5637233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637244 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_5637244 : Nat := 118140960795 + 5637244 * 2 ^ 59
def prefixEnd_5637244 : Nat := 4983230072969 + 3 ^ 40 * 5637244 * 2
def baseEnd_5637244 : Nat := 2894615738674247490624793

theorem tailTrace_5637244 : CollatzResearch.WordTrace tailWord_5637244 prefixEnd_5637244 2894615738674247490624793 := by
  unfold tailWord_5637244
  simp only [CollatzResearch.WordTrace]
  refine ⟨102803589994617613735351393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137071453326156818313801857 102803589994617613735351393)
  ·
    refine ⟨77102692495963210301513545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102803589994617613735351393 77102692495963210301513545)
    ·
      refine ⟨57827019371972407726135159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77102692495963210301513545 57827019371972407726135159)
      ·
        refine ⟨86740529057958611589202739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57827019371972407726135159 86740529057958611589202739)
        ·
          refine ⟨130110793586937917383804109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86740529057958611589202739 130110793586937917383804109)
          ·
            refine ⟨48791547595101719018926541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130110793586937917383804109 48791547595101719018926541)
            ·
              refine ⟨18296830348163144632097453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48791547595101719018926541 18296830348163144632097453)
              ·
                refine ⟨6861311380561179237036545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18296830348163144632097453 6861311380561179237036545)
                ·
                  refine ⟨5145983535420884427777409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6861311380561179237036545 5145983535420884427777409)
                  ·
                    refine ⟨3859487651565663320833057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5145983535420884427777409 3859487651565663320833057)
                    ·
                      refine ⟨2894615738674247490624793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859487651565663320833057 2894615738674247490624793)
                      ·
                        rfl

theorem cell23_5637244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_5637244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637244 prefixEnd_5637244 := by exact prefixLift 5637244
  have htrace : WordTrace (prefixWord ++ tailWord_5637244) baseStart_5637244 baseEnd_5637244 := by
    simpa [prefixWord, tailWord_5637244, baseEnd_5637244] using wordTrace_append hprefix tailTrace_5637244
  have hstable : (prefixWord ++ tailWord_5637244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637244).length < 2 ^ (prefixWord ++ tailWord_5637244).sum := by decide
  have hdescent : baseEnd_5637244 < baseStart_5637244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637278 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_5637278 : Nat := 118140960795 + 5637278 * 2 ^ 59
def prefixEnd_5637278 : Nat := 4983230072969 + 3 ^ 40 * 5637278 * 2
def baseEnd_5637278 : Nat := 2894633197016500357599637

theorem tailTrace_5637278 : CollatzResearch.WordTrace tailWord_5637278 prefixEnd_5637278 2894633197016500357599637 := by
  unfold tailWord_5637278
  simp only [CollatzResearch.WordTrace]
  refine ⟨25701052508889006409680061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137072280047408034184960325 25701052508889006409680061)
  ·
    refine ⟨9637894690833377403630023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25701052508889006409680061 9637894690833377403630023)
    ·
      refine ⟨14456842036250066105445035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9637894690833377403630023 14456842036250066105445035)
      ·
        refine ⟨21685263054375099158167553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14456842036250066105445035 21685263054375099158167553)
        ·
          refine ⟨16263947290781324368625665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21685263054375099158167553 16263947290781324368625665)
          ·
            refine ⟨12197960468085993276469249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16263947290781324368625665 12197960468085993276469249)
            ·
              refine ⟨9148470351064494957351937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12197960468085993276469249 9148470351064494957351937)
              ·
                refine ⟨6861352763298371218013953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148470351064494957351937 6861352763298371218013953)
                ·
                  refine ⟨5146014572473778413510465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6861352763298371218013953 5146014572473778413510465)
                  ·
                    refine ⟨3859510929355333810132849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146014572473778413510465 3859510929355333810132849)
                    ·
                      refine ⟨2894633197016500357599637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859510929355333810132849 2894633197016500357599637)
                      ·
                        rfl

theorem cell23_5637278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_5637278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637278 prefixEnd_5637278 := by exact prefixLift 5637278
  have htrace : WordTrace (prefixWord ++ tailWord_5637278) baseStart_5637278 baseEnd_5637278 := by
    simpa [prefixWord, tailWord_5637278, baseEnd_5637278] using wordTrace_append hprefix tailTrace_5637278
  have hstable : (prefixWord ++ tailWord_5637278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637278).length < 2 ^ (prefixWord ++ tailWord_5637278).sum := by decide
  have hdescent : baseEnd_5637278 < baseStart_5637278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637280 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_5637280 : Nat := 118140960795 + 5637280 * 2 ^ 59
def prefixEnd_5637280 : Nat := 4983230072969 + 3 ^ 40 * 5637280 * 2
def baseEnd_5637280 : Nat := 964878074659269783258209

theorem tailTrace_5637280 : CollatzResearch.WordTrace tailWord_5637280 prefixEnd_5637280 964878074659269783258209 := by
  unfold tailWord_5637280
  simp only [CollatzResearch.WordTrace]
  refine ⟨102804246508552402809506647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137072328678069870412675529 102804246508552402809506647)
  ·
    refine ⟨154206369762828604214259971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102804246508552402809506647 154206369762828604214259971)
    ·
      refine ⟨231309554644242906321389957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154206369762828604214259971 231309554644242906321389957)
      ·
        refine ⟨43370541495795544935260617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231309554644242906321389957 43370541495795544935260617)
        ·
          refine ⟨32527906121846658701445463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43370541495795544935260617 32527906121846658701445463)
          ·
            refine ⟨48791859182769988052168195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32527906121846658701445463 48791859182769988052168195)
            ·
              refine ⟨73187788774154982078252293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48791859182769988052168195 73187788774154982078252293)
              ·
                refine ⟨13722710395154059139672305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73187788774154982078252293 13722710395154059139672305)
                ·
                  refine ⟨10292032796365544354754229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13722710395154059139672305 10292032796365544354754229)
                  ·
                    refine ⟨964878074659269783258209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10292032796365544354754229 964878074659269783258209)
                    ·
                      rfl

theorem cell23_5637280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_5637280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637280 prefixEnd_5637280 := by exact prefixLift 5637280
  have htrace : WordTrace (prefixWord ++ tailWord_5637280) baseStart_5637280 baseEnd_5637280 := by
    simpa [prefixWord, tailWord_5637280, baseEnd_5637280] using wordTrace_append hprefix tailTrace_5637280
  have hstable : (prefixWord ++ tailWord_5637280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637280).length < 2 ^ (prefixWord ++ tailWord_5637280).sum := by decide
  have hdescent : baseEnd_5637280 < baseStart_5637280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637284 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 5]
def baseStart_5637284 : Nat := 118140960795 + 5637284 * 2 ^ 59
def prefixEnd_5637284 : Nat := 4983230072969 + 3 ^ 40 * 5637284 * 2
def baseEnd_5637284 : Nat := 321626253100047481569401

theorem tailTrace_5637284 : CollatzResearch.WordTrace tailWord_5637284 prefixEnd_5637284 321626253100047481569401 := by
  unfold tailWord_5637284
  simp only [CollatzResearch.WordTrace]
  refine ⟨102804319454545157151079453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137072425939393542868105937 102804319454545157151079453)
  ·
    refine ⟨38551619795454433931654795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102804319454545157151079453 38551619795454433931654795)
    ·
      refine ⟨57827429693181650897482193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38551619795454433931654795 57827429693181650897482193)
      ·
        refine ⟨43370572269886238173111645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57827429693181650897482193 43370572269886238173111645)
        ·
          refine ⟨16263964601207339314916867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43370572269886238173111645 16263964601207339314916867)
          ·
            refine ⟨24395946901811008972375301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16263964601207339314916867 24395946901811008972375301)
            ·
              refine ⟨4574240044089564182320369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24395946901811008972375301 4574240044089564182320369)
              ·
                refine ⟨3430680033067173136740277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4574240044089564182320369 3430680033067173136740277)
                ·
                  refine ⟨321626253100047481569401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3430680033067173136740277 321626253100047481569401)
                  ·
                    rfl

theorem cell23_5637284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_5637284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637284 prefixEnd_5637284 := by exact prefixLift 5637284
  have htrace : WordTrace (prefixWord ++ tailWord_5637284) baseStart_5637284 baseEnd_5637284 := by
    simpa [prefixWord, tailWord_5637284, baseEnd_5637284] using wordTrace_append hprefix tailTrace_5637284
  have hstable : (prefixWord ++ tailWord_5637284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637284).length < 2 ^ (prefixWord ++ tailWord_5637284).sum := by decide
  have hdescent : baseEnd_5637284 < baseStart_5637284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637330 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5637330 : Nat := 118140960795 + 5637330 * 2 ^ 59
def prefixEnd_5637330 : Nat := 4983230072969 + 3 ^ 40 * 5637330 * 2
def baseEnd_5637330 : Nat := 2894659898010534154149397

theorem tailTrace_5637330 : CollatzResearch.WordTrace tailWord_5637330 prefixEnd_5637330 2894659898010534154149397 := by
  unfold tailWord_5637330
  simp only [CollatzResearch.WordTrace]
  refine ⟨51402579166730916039583361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137073544444615776105555629 51402579166730916039583361)
  ·
    refine ⟨38551934375048187029687521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51402579166730916039583361 38551934375048187029687521)
    ·
      refine ⟨28913950781286140272265641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38551934375048187029687521 28913950781286140272265641)
      ·
        refine ⟨21685463085964605204199231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28913950781286140272265641 21685463085964605204199231)
        ·
          refine ⟨32528194628946907806298847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21685463085964605204199231 32528194628946907806298847)
          ·
            refine ⟨48792291943420361709448271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32528194628946907806298847 48792291943420361709448271)
            ·
              refine ⟨73188437915130542564172407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48792291943420361709448271 73188437915130542564172407)
              ·
                refine ⟨109782656872695813846258611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73188437915130542564172407 109782656872695813846258611)
                ·
                  refine ⟨164673985309043720769387917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109782656872695813846258611 164673985309043720769387917)
                  ·
                    refine ⟨61752744490891395288520469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164673985309043720769387917 61752744490891395288520469)
                    ·
                      refine ⟨2894659898010534154149397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61752744490891395288520469 2894659898010534154149397)
                      ·
                        rfl

theorem cell23_5637330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5637330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637330 prefixEnd_5637330 := by exact prefixLift 5637330
  have htrace : WordTrace (prefixWord ++ tailWord_5637330) baseStart_5637330 baseEnd_5637330 := by
    simpa [prefixWord, tailWord_5637330, baseEnd_5637330] using wordTrace_append hprefix tailTrace_5637330
  have hstable : (prefixWord ++ tailWord_5637330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637330).length < 2 ^ (prefixWord ++ tailWord_5637330).sum := by decide
  have hdescent : baseEnd_5637330 < baseStart_5637330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637344 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 1, 4]
def baseStart_5637344 : Nat := 118140960795 + 5637344 * 2 ^ 59
def prefixEnd_5637344 : Nat := 4983230072969 + 3 ^ 40 * 5637344 * 2
def baseEnd_5637344 : Nat := 964889028913232366458111

theorem tailTrace_5637344 : CollatzResearch.WordTrace tailWord_5637344 prefixEnd_5637344 964889028913232366458111 := by
  unfold tailWord_5637344
  simp only [CollatzResearch.WordTrace]
  refine ⟨102805413644436472274671543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137073884859248629699562057 102805413644436472274671543)
  ·
    refine ⟨154208120466654708412007315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102805413644436472274671543 154208120466654708412007315)
    ·
      refine ⟨231312180699982062618010973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154208120466654708412007315 231312180699982062618010973)
      ·
        refine ⟨86742067762493273481754115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231312180699982062618010973 86742067762493273481754115)
        ·
          refine ⟨130113101643739910222631173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86742067762493273481754115 130113101643739910222631173)
          ·
            refine ⟨24396206558201233166743345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130113101643739910222631173 24396206558201233166743345)
            ·
              refine ⟨18297154918650924875057509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24396206558201233166743345 18297154918650924875057509)
              ·
                refine ⟨3430716547247048414073283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18297154918650924875057509 3430716547247048414073283)
                ·
                  refine ⟨5146074820870572621109925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430716547247048414073283 5146074820870572621109925)
                  ·
                    refine ⟨964889028913232366458111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5146074820870572621109925 964889028913232366458111)
                    ·
                      rfl

theorem cell23_5637344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 4].length) (baseStart_5637344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637344 prefixEnd_5637344 := by exact prefixLift 5637344
  have htrace : WordTrace (prefixWord ++ tailWord_5637344) baseStart_5637344 baseEnd_5637344 := by
    simpa [prefixWord, tailWord_5637344, baseEnd_5637344] using wordTrace_append hprefix tailTrace_5637344
  have hstable : (prefixWord ++ tailWord_5637344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637344).length < 2 ^ (prefixWord ++ tailWord_5637344).sum := by decide
  have hdescent : baseEnd_5637344 < baseStart_5637344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637387 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 1, 5]
def baseStart_5637387 : Nat := 118140960795 + 5637387 * 2 ^ 59
def prefixEnd_5637387 : Nat := 4983230072969 + 3 ^ 40 * 5637387 * 2
def baseEnd_5637387 : Nat := 964896388802613477045545

theorem tailTrace_5637387 : CollatzResearch.WordTrace tailWord_5637387 prefixEnd_5637387 964896388802613477045545 := by
  unfold tailWord_5637387
  simp only [CollatzResearch.WordTrace]
  refine ⟨205612395627717162893158415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137074930418478108595438943 205612395627717162893158415)
  ·
    refine ⟨308418593441575744339737623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205612395627717162893158415 308418593441575744339737623)
    ·
      refine ⟨462627890162363616509606435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308418593441575744339737623 462627890162363616509606435)
      ·
        refine ⟨693941835243545424764409653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462627890162363616509606435 693941835243545424764409653)
        ·
          refine ⟨65057047054082383571663405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 693941835243545424764409653 65057047054082383571663405)
          ·
            refine ⟨24396392645280893839373777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65057047054082383571663405 24396392645280893839373777)
            ·
              refine ⟨18297294483960670379530333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24396392645280893839373777 18297294483960670379530333)
              ·
                refine ⟨6861485431485251392323875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18297294483960670379530333 6861485431485251392323875)
                ·
                  refine ⟨10292228147227877088485813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6861485431485251392323875 10292228147227877088485813)
                  ·
                    refine ⟨964896388802613477045545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10292228147227877088485813 964896388802613477045545)
                    ·
                      rfl

theorem cell23_5637387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 5].length) (baseStart_5637387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637387 prefixEnd_5637387 := by exact prefixLift 5637387
  have htrace : WordTrace (prefixWord ++ tailWord_5637387) baseStart_5637387 baseEnd_5637387 := by
    simpa [prefixWord, tailWord_5637387, baseEnd_5637387] using wordTrace_append hprefix tailTrace_5637387
  have hstable : (prefixWord ++ tailWord_5637387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637387).length < 2 ^ (prefixWord ++ tailWord_5637387).sum := by decide
  have hdescent : baseEnd_5637387 < baseStart_5637387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637421 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5637421 : Nat := 118140960795 + 5637421 * 2 ^ 59
def prefixEnd_5637421 : Nat := 4983230072969 + 3 ^ 40 * 5637421 * 2
def baseEnd_5637421 : Nat := 964902208250031099370493

theorem tailTrace_5637421 : CollatzResearch.WordTrace tailWord_5637421 prefixEnd_5637421 964902208250031099370493 := by
  unfold tailWord_5637421
  simp only [CollatzResearch.WordTrace]
  refine ⟨205613635709593986699896117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137075757139729324466597411 205613635709593986699896117)
  ·
    refine ⟨19276278347774436253115261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205613635709593986699896117 19276278347774436253115261)
    ·
      refine ⟨7228604380415413594918223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19276278347774436253115261 7228604380415413594918223)
      ·
        refine ⟨10842906570623120392377335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7228604380415413594918223 10842906570623120392377335)
        ·
          refine ⟨16264359855934680588566003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10842906570623120392377335 16264359855934680588566003)
          ·
            refine ⟨24396539783902020882849005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16264359855934680588566003 24396539783902020882849005)
            ·
              refine ⟨9148702418963257831068377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24396539783902020882849005 9148702418963257831068377)
              ·
                refine ⟨6861526814222443373301283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148702418963257831068377 6861526814222443373301283)
                ·
                  refine ⟨10292290221333665059951925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6861526814222443373301283 10292290221333665059951925)
                  ·
                    refine ⟨964902208250031099370493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10292290221333665059951925 964902208250031099370493)
                    ·
                      rfl

theorem cell23_5637421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5637421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637421 prefixEnd_5637421 := by exact prefixLift 5637421
  have htrace : WordTrace (prefixWord ++ tailWord_5637421) baseStart_5637421 baseEnd_5637421 := by
    simpa [prefixWord, tailWord_5637421, baseEnd_5637421] using wordTrace_append hprefix tailTrace_5637421
  have hstable : (prefixWord ++ tailWord_5637421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637421).length < 2 ^ (prefixWord ++ tailWord_5637421).sum := by decide
  have hdescent : baseEnd_5637421 < baseStart_5637421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637424 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 5, 2, 2]
def baseStart_5637424 : Nat := 118140960795 + 5637424 * 2 ^ 59
def prefixEnd_5637424 : Nat := 4983230072969 + 3 ^ 40 * 5637424 * 2
def baseEnd_5637424 : Nat := 2894708165192056786373965

theorem tailTrace_5637424 : CollatzResearch.WordTrace tailWord_5637424 prefixEnd_5637424 2894708165192056786373965 := by
  unfold tailWord_5637424
  simp only [CollatzResearch.WordTrace]
  refine ⟨102806872564291559106127663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137075830085722078808170217 102806872564291559106127663)
  ·
    refine ⟨154210308846437338659191495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102806872564291559106127663 154210308846437338659191495)
    ·
      refine ⟨231315463269656007988787243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154210308846437338659191495 231315463269656007988787243)
      ·
        refine ⟨346973194904484011983180865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231315463269656007988787243 346973194904484011983180865)
        ·
          refine ⟨260229896178363008987385649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346973194904484011983180865 260229896178363008987385649)
          ·
            refine ⟨195172422133772256740539237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260229896178363008987385649 195172422133772256740539237)
            ·
              refine ⟨36594829150082298138851107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195172422133772256740539237 36594829150082298138851107)
              ·
                refine ⟨54892243725123447208276661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36594829150082298138851107 54892243725123447208276661)
                ·
                  refine ⟨5146147849230323175775937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54892243725123447208276661 5146147849230323175775937)
                  ·
                    refine ⟨3859610886922742381831953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146147849230323175775937 3859610886922742381831953)
                    ·
                      refine ⟨2894708165192056786373965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859610886922742381831953 2894708165192056786373965)
                      ·
                        rfl

theorem cell23_5637424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 2, 2].length) (baseStart_5637424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637424 prefixEnd_5637424 := by exact prefixLift 5637424
  have htrace : WordTrace (prefixWord ++ tailWord_5637424) baseStart_5637424 baseEnd_5637424 := by
    simpa [prefixWord, tailWord_5637424, baseEnd_5637424] using wordTrace_append hprefix tailTrace_5637424
  have hstable : (prefixWord ++ tailWord_5637424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637424).length < 2 ^ (prefixWord ++ tailWord_5637424).sum := by decide
  have hdescent : baseEnd_5637424 < baseStart_5637424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637457 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_5637457 : Nat := 118140960795 + 5637457 * 2 ^ 59
def prefixEnd_5637457 : Nat := 4983230072969 + 3 ^ 40 * 5637457 * 2
def baseEnd_5637457 : Nat := 2894725110053655157261313

theorem tailTrace_5637457 : CollatzResearch.WordTrace tailWord_5637457 prefixEnd_5637457 2894725110053655157261313 := by
  unfold tailWord_5637457
  simp only [CollatzResearch.WordTrace]
  refine ⟨205614948737463564848206625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137076632491642376565471083 205614948737463564848206625)
  ·
    refine ⟨154211211553097673636154969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205614948737463564848206625 154211211553097673636154969)
    ·
      refine ⟨115658408664823255227116227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154211211553097673636154969 115658408664823255227116227)
      ·
        refine ⟨173487612997234882840674341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115658408664823255227116227 173487612997234882840674341)
        ·
          refine ⟨32528927436981540532626439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173487612997234882840674341 32528927436981540532626439)
          ·
            refine ⟨48793391155472310798939659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32528927436981540532626439 48793391155472310798939659)
            ·
              refine ⟨73190086733208466198409489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48793391155472310798939659 73190086733208466198409489)
              ·
                refine ⟨54892565049906349648807117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73190086733208466198409489 54892565049906349648807117)
                ·
                  refine ⟨20584711893714881118302669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54892565049906349648807117 20584711893714881118302669)
                  ·
                    refine ⟨7719266960143080419363501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20584711893714881118302669 7719266960143080419363501)
                    ·
                      refine ⟨2894725110053655157261313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7719266960143080419363501 2894725110053655157261313)
                      ·
                        rfl

theorem cell23_5637457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_5637457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637457 prefixEnd_5637457 := by exact prefixLift 5637457
  have htrace : WordTrace (prefixWord ++ tailWord_5637457) baseStart_5637457 baseEnd_5637457 := by
    simpa [prefixWord, tailWord_5637457, baseEnd_5637457] using wordTrace_append hprefix tailTrace_5637457
  have hstable : (prefixWord ++ tailWord_5637457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637457).length < 2 ^ (prefixWord ++ tailWord_5637457).sum := by decide
  have hdescent : baseEnd_5637457 < baseStart_5637457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637501 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_5637501 : Nat := 118140960795 + 5637501 * 2 ^ 59
def prefixEnd_5637501 : Nat := 4983230072969 + 3 ^ 40 * 5637501 * 2
def baseEnd_5637501 : Nat := 2894747703202452985111111

theorem tailTrace_5637501 : CollatzResearch.WordTrace tailWord_5637501 prefixEnd_5637501 2894747703202452985111111 := by
  unfold tailWord_5637501
  simp only [CollatzResearch.WordTrace]
  refine ⟨205616553549304160362808357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137077702366202773575205571 205616553549304160362808357)
  ·
    refine ⟨38553103790494530068026567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205616553549304160362808357 38553103790494530068026567)
    ·
      refine ⟨57829655685741795102039851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38553103790494530068026567 57829655685741795102039851)
      ·
        refine ⟨86744483528612692653059777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57829655685741795102039851 86744483528612692653059777)
        ·
          refine ⟨65058362646459519489794833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86744483528612692653059777 65058362646459519489794833)
          ·
            refine ⟨48793771984844639617346125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65058362646459519489794833 48793771984844639617346125)
            ·
              refine ⟨18297664494316739856504797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48793771984844639617346125 18297664494316739856504797)
              ·
                refine ⟨6861624185368777446189299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18297664494316739856504797 6861624185368777446189299)
                ·
                  refine ⟨10292436278053166169283949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6861624185368777446189299 10292436278053166169283949)
                  ·
                    refine ⟨3859663604269937313481481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10292436278053166169283949 3859663604269937313481481)
                    ·
                      refine ⟨2894747703202452985111111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859663604269937313481481 2894747703202452985111111)
                      ·
                        rfl

theorem cell23_5637501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_5637501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637501 prefixEnd_5637501 := by exact prefixLift 5637501
  have htrace : WordTrace (prefixWord ++ tailWord_5637501) baseStart_5637501 baseEnd_5637501 := by
    simpa [prefixWord, tailWord_5637501, baseEnd_5637501] using wordTrace_append hprefix tailTrace_5637501
  have hstable : (prefixWord ++ tailWord_5637501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637501).length < 2 ^ (prefixWord ++ tailWord_5637501).sum := by decide
  have hdescent : baseEnd_5637501 < baseStart_5637501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637502 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5637502 : Nat := 118140960795 + 5637502 * 2 ^ 59
def prefixEnd_5637502 : Nat := 4983230072969 + 3 ^ 40 * 5637502 * 2
def baseEnd_5637502 : Nat := 964916072227702493732869

theorem tailTrace_5637502 : CollatzResearch.WordTrace tailWord_5637502 prefixEnd_5637502 964916072227702493732869 := by
  unfold tailWord_5637502
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702073752787567191699345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137077726681533691689063173 25702073752787567191699345)
  ·
    refine ⟨19276555314590675393774509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25702073752787567191699345 19276555314590675393774509)
    ·
      refine ⟨7228708242971503272665441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19276555314590675393774509 7228708242971503272665441)
      ·
        refine ⟨5421531182228627454499081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7228708242971503272665441 5421531182228627454499081)
        ·
          refine ⟨4066148386671470590874311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5421531182228627454499081 4066148386671470590874311)
          ·
            refine ⟨6099222580007205886311467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066148386671470590874311 6099222580007205886311467)
            ·
              refine ⟨9148833870010808829467201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099222580007205886311467 9148833870010808829467201)
              ·
                refine ⟨6861625402508106622100401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148833870010808829467201 6861625402508106622100401)
                ·
                  refine ⟨5146219051881079966575301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6861625402508106622100401 5146219051881079966575301)
                  ·
                    refine ⟨964916072227702493732869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5146219051881079966575301 964916072227702493732869)
                    ·
                      rfl

theorem cell23_5637502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5637502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637502 prefixEnd_5637502 := by exact prefixLift 5637502
  have htrace : WordTrace (prefixWord ++ tailWord_5637502) baseStart_5637502 baseEnd_5637502 := by
    simpa [prefixWord, tailWord_5637502, baseEnd_5637502] using wordTrace_append hprefix tailTrace_5637502
  have hstable : (prefixWord ++ tailWord_5637502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637502).length < 2 ^ (prefixWord ++ tailWord_5637502).sum := by decide
  have hdescent : baseEnd_5637502 < baseStart_5637502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637507 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 2, 6]
def baseStart_5637507 : Nat := 118140960795 + 5637507 * 2 ^ 59
def prefixEnd_5637507 : Nat := 4983230072969 + 3 ^ 40 * 5637507 * 2
def baseEnd_5637507 : Nat := 964916928028793320545361

theorem tailTrace_5637507 : CollatzResearch.WordTrace tailWord_5637507 prefixEnd_5637507 964916928028793320545361 := by
  unfold tailWord_5637507
  simp only [CollatzResearch.WordTrace]
  refine ⟨205616772387282423387526775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137077848258188282258351183 205616772387282423387526775)
  ·
    refine ⟨308425158580923635081290163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205616772387282423387526775 308425158580923635081290163)
    ·
      refine ⟨462637737871385452621935245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308425158580923635081290163 462637737871385452621935245)
      ·
        refine ⟨173489151701769544733225717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462637737871385452621935245 173489151701769544733225717)
        ·
          refine ⟨16264607972040894818739911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173489151701769544733225717 16264607972040894818739911)
          ·
            refine ⟨24396911958061342228109867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16264607972040894818739911 24396911958061342228109867)
            ·
              refine ⟨36595367937092013342164801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24396911958061342228109867 36595367937092013342164801)
              ·
                refine ⟨27446525952819010006623601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36595367937092013342164801 27446525952819010006623601)
                ·
                  refine ⟨20584894464614257504967701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27446525952819010006623601 20584894464614257504967701)
                  ·
                    refine ⟨964916928028793320545361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20584894464614257504967701 964916928028793320545361)
                    ·
                      rfl

theorem cell23_5637507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 6].length) (baseStart_5637507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637507 prefixEnd_5637507 := by exact prefixLift 5637507
  have htrace : WordTrace (prefixWord ++ tailWord_5637507) baseStart_5637507 baseEnd_5637507 := by
    simpa [prefixWord, tailWord_5637507, baseEnd_5637507] using wordTrace_append hprefix tailTrace_5637507
  have hstable : (prefixWord ++ tailWord_5637507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637507).length < 2 ^ (prefixWord ++ tailWord_5637507).sum := by decide
  have hdescent : baseEnd_5637507 < baseStart_5637507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637508 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_5637508 : Nat := 118140960795 + 5637508 * 2 ^ 59
def prefixEnd_5637508 : Nat := 4983230072969 + 3 ^ 40 * 5637508 * 2
def baseEnd_5637508 : Nat := 2894751297567034457723579

theorem tailTrace_5637508 : CollatzResearch.WordTrace tailWord_5637508 prefixEnd_5637508 2894751297567034457723579 := by
  unfold tailWord_5637508
  simp only [CollatzResearch.WordTrace]
  refine ⟨102808404430139400279156589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137077872573519200372208785 102808404430139400279156589)
  ·
    refine ⟨38553151661302275104683721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102808404430139400279156589 38553151661302275104683721)
    ·
      refine ⟨28914863745976706328512791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38553151661302275104683721 28914863745976706328512791)
      ·
        refine ⟨43372295618965059492769187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28914863745976706328512791 43372295618965059492769187)
        ·
          refine ⟨65058443428447589239153781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43372295618965059492769187 65058443428447589239153781)
          ·
            refine ⟨6099229071416961491170667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65058443428447589239153781 6099229071416961491170667)
            ·
              refine ⟨9148843607125442236756001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099229071416961491170667 9148843607125442236756001)
              ·
                refine ⟨6861632705344081677567001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148843607125442236756001 6861632705344081677567001)
                ·
                  refine ⟨5146224529008061258175251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6861632705344081677567001 5146224529008061258175251)
                  ·
                    refine ⟨7719336793512091887262877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5146224529008061258175251 7719336793512091887262877)
                    ·
                      refine ⟨2894751297567034457723579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7719336793512091887262877 2894751297567034457723579)
                      ·
                        rfl

theorem cell23_5637508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_5637508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637508 prefixEnd_5637508 := by exact prefixLift 5637508
  have htrace : WordTrace (prefixWord ++ tailWord_5637508) baseStart_5637508 baseEnd_5637508 := by
    simpa [prefixWord, tailWord_5637508, baseEnd_5637508] using wordTrace_append hprefix tailTrace_5637508
  have hstable : (prefixWord ++ tailWord_5637508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637508).length < 2 ^ (prefixWord ++ tailWord_5637508).sum := by decide
  have hdescent : baseEnd_5637508 < baseStart_5637508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637524 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_5637524 : Nat := 118140960795 + 5637524 * 2 ^ 59
def prefixEnd_5637524 : Nat := 4983230072969 + 3 ^ 40 * 5637524 * 2
def baseEnd_5637524 : Nat := 964919837752502131707835

theorem tailTrace_5637524 : CollatzResearch.WordTrace tailWord_5637524 prefixEnd_5637524 964919837752502131707835 := by
  unfold tailWord_5637524
  simp only [CollatzResearch.WordTrace]
  refine ⟨102808696214110417645447813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137078261618813890193930417 102808696214110417645447813)
  ·
    refine ⟨19276630540145703308521465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102808696214110417645447813 19276630540145703308521465)
    ·
      refine ⟨14457472905109277481391099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19276630540145703308521465 14457472905109277481391099)
      ·
        refine ⟨21686209357663916222086649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14457472905109277481391099 21686209357663916222086649)
        ·
          refine ⟨16264657018247937166564987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21686209357663916222086649 16264657018247937166564987)
          ·
            refine ⟨24396985527371905749847481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16264657018247937166564987 24396985527371905749847481)
            ·
              refine ⟨18297739145528929312385611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24396985527371905749847481 18297739145528929312385611)
              ·
                refine ⟨27446608718293393968578417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18297739145528929312385611 27446608718293393968578417)
                ·
                  refine ⟨20584956538720045476433813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27446608718293393968578417 20584956538720045476433813)
                  ·
                    refine ⟨964919837752502131707835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20584956538720045476433813 964919837752502131707835)
                    ·
                      rfl

theorem cell23_5637524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_5637524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637524 prefixEnd_5637524 := by exact prefixLift 5637524
  have htrace : WordTrace (prefixWord ++ tailWord_5637524) baseStart_5637524 baseEnd_5637524 := by
    simpa [prefixWord, tailWord_5637524, baseEnd_5637524] using wordTrace_append hprefix tailTrace_5637524
  have hstable : (prefixWord ++ tailWord_5637524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637524).length < 2 ^ (prefixWord ++ tailWord_5637524).sum := by decide
  have hdescent : baseEnd_5637524 < baseStart_5637524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637554 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_5637554 : Nat := 118140960795 + 5637554 * 2 ^ 59
def prefixEnd_5637554 : Nat := 4983230072969 + 3 ^ 40 * 5637554 * 2
def baseEnd_5637554 : Nat := 321641657519682364194263

theorem tailTrace_5637554 : CollatzResearch.WordTrace tailWord_5637554 prefixEnd_5637554 321641657519682364194263 := by
  unfold tailWord_5637554
  simp only [CollatzResearch.WordTrace]
  refine ⟨51404621654528037603621929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137078991078741433609658477 51404621654528037603621929)
  ·
    refine ⟨38553466240896028202716447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51404621654528037603621929 38553466240896028202716447)
    ·
      refine ⟨57830199361344042304074671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38553466240896028202716447 57830199361344042304074671)
      ·
        refine ⟨86745299042016063456112007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57830199361344042304074671 86745299042016063456112007)
        ·
          refine ⟨130117948563024095184168011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86745299042016063456112007 130117948563024095184168011)
          ·
            refine ⟨195176922844536142776252017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130117948563024095184168011 195176922844536142776252017)
            ·
              refine ⟨146382692133402107082189013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195176922844536142776252017 146382692133402107082189013)
              ·
                refine ⟨3430844346876611884738805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146382692133402107082189013 3430844346876611884738805)
                ·
                  refine ⟨321641657519682364194263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3430844346876611884738805 321641657519682364194263)
                  ·
                    rfl

theorem cell23_5637554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_5637554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637554 prefixEnd_5637554 := by exact prefixLift 5637554
  have htrace : WordTrace (prefixWord ++ tailWord_5637554) baseStart_5637554 baseEnd_5637554 := by
    simpa [prefixWord, tailWord_5637554, baseEnd_5637554] using wordTrace_append hprefix tailTrace_5637554
  have hstable : (prefixWord ++ tailWord_5637554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637554).length < 2 ^ (prefixWord ++ tailWord_5637554).sum := by decide
  have hdescent : baseEnd_5637554 < baseStart_5637554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637678 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_5637678 : Nat := 118140960795 + 5637678 * 2 ^ 59
def prefixEnd_5637678 : Nat := 4983230072969 + 3 ^ 40 * 5637678 * 2
def baseEnd_5637678 : Nat := 321648732142033199177533

theorem tailTrace_5637678 : CollatzResearch.WordTrace tailWord_5637678 prefixEnd_5637678 321648732142033199177533 := by
  unfold tailWord_5637678
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702876158707864949000211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137082006179775279728001125 25702876158707864949000211)
  ·
    refine ⟨38554314238061797423500317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25702876158707864949000211 38554314238061797423500317)
    ·
      refine ⟨14457867839273174033812619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38554314238061797423500317 14457867839273174033812619)
      ·
        refine ⟨21686801758909761050718929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14457867839273174033812619 21686801758909761050718929)
        ·
          refine ⟨16265101319182320788039197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21686801758909761050718929 16265101319182320788039197)
          ·
            refine ⟨6099412994693370295514699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16265101319182320788039197 6099412994693370295514699)
            ·
              refine ⟨9149119492040055443272049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099412994693370295514699 9149119492040055443272049)
              ·
                refine ⟨6861839619030041582454037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9149119492040055443272049 6861839619030041582454037)
                ·
                  refine ⟨321648732142033199177533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6861839619030041582454037 321648732142033199177533)
                  ·
                    rfl

theorem cell23_5637678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_5637678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637678 prefixEnd_5637678 := by exact prefixLift 5637678
  have htrace : WordTrace (prefixWord ++ tailWord_5637678) baseStart_5637678 baseEnd_5637678 := by
    simpa [prefixWord, tailWord_5637678, baseEnd_5637678] using wordTrace_append hprefix tailTrace_5637678
  have hstable : (prefixWord ++ tailWord_5637678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637678).length < 2 ^ (prefixWord ++ tailWord_5637678).sum := by decide
  have hdescent : baseEnd_5637678 < baseStart_5637678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637681 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 4, 3, 2]
def baseStart_5637681 : Nat := 118140960795 + 5637681 * 2 ^ 59
def prefixEnd_5637681 : Nat := 4983230072969 + 3 ^ 40 * 5637681 * 2
def baseEnd_5637681 : Nat := 2894840129720262280860283

theorem tailTrace_5637681 : CollatzResearch.WordTrace tailWord_5637681 prefixEnd_5637681 2894840129720262280860283 := by
  unfold tailWord_5637681
  simp only [CollatzResearch.WordTrace]
  refine ⟨205623118688652051104360897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137082079125768034069573931 205623118688652051104360897)
  ·
    refine ⟨154217339016489038328270673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205623118688652051104360897 154217339016489038328270673)
    ·
      refine ⟨115663004262366778746203005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154217339016489038328270673 115663004262366778746203005)
      ·
        refine ⟨43373626598387542029826127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115663004262366778746203005 43373626598387542029826127)
        ·
          refine ⟨65060439897581313044739191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43373626598387542029826127 65060439897581313044739191)
          ·
            refine ⟨97590659846371969567108787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65060439897581313044739191 97590659846371969567108787)
            ·
              refine ⟨146385989769557954350663181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97590659846371969567108787 146385989769557954350663181)
              ·
                refine ⟨54894746163584232881498693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146385989769557954350663181 54894746163584232881498693)
                ·
                  refine ⟨10292764905672043665281005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54894746163584232881498693 10292764905672043665281005)
                  ·
                    refine ⟨3859786839627016374480377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10292764905672043665281005 3859786839627016374480377)
                    ·
                      refine ⟨2894840129720262280860283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859786839627016374480377 2894840129720262280860283)
                      ·
                        rfl

theorem cell23_5637681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_5637681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637681 prefixEnd_5637681 := by exact prefixLift 5637681
  have htrace : WordTrace (prefixWord ++ tailWord_5637681) baseStart_5637681 baseEnd_5637681 := by
    simpa [prefixWord, tailWord_5637681, baseEnd_5637681] using wordTrace_append hprefix tailTrace_5637681
  have hstable : (prefixWord ++ tailWord_5637681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637681).length < 2 ^ (prefixWord ++ tailWord_5637681).sum := by decide
  have hdescent : baseEnd_5637681 < baseStart_5637681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637688 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_5637688 : Nat := 118140960795 + 5637688 * 2 ^ 59
def prefixEnd_5637688 : Nat := 4983230072969 + 3 ^ 40 * 5637688 * 2
def baseEnd_5637688 : Nat := 2894843724084843753472751

theorem tailTrace_5637688 : CollatzResearch.WordTrace tailWord_5637688 prefixEnd_5637688 2894843724084843753472751 := by
  unfold tailWord_5637688
  simp only [CollatzResearch.WordTrace]
  refine ⟨102811686999813345649932859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137082249333084460866577145 102811686999813345649932859)
  ·
    refine ⟨154217530499720018474899289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102811686999813345649932859 154217530499720018474899289)
    ·
      refine ⟨115663147874790013856174467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154217530499720018474899289 115663147874790013856174467)
      ·
        refine ⟨173494721812185020784261701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115663147874790013856174467 173494721812185020784261701)
        ·
          refine ⟨32530260339784691397049069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173494721812185020784261701 32530260339784691397049069)
          ·
            refine ⟨12198847627419259273893401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32530260339784691397049069 12198847627419259273893401)
            ·
              refine ⟨9149135720564444455420051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12198847627419259273893401 9149135720564444455420051)
              ·
                refine ⟨13723703580846666683130077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9149135720564444455420051 13723703580846666683130077)
                ·
                  refine ⟨5146388842817500006173779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13723703580846666683130077 5146388842817500006173779)
                  ·
                    refine ⟨7719583264226250009260669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5146388842817500006173779 7719583264226250009260669)
                    ·
                      refine ⟨2894843724084843753472751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7719583264226250009260669 2894843724084843753472751)
                      ·
                        rfl

theorem cell23_5637688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_5637688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637688 prefixEnd_5637688 := by exact prefixLift 5637688
  have htrace : WordTrace (prefixWord ++ tailWord_5637688) baseStart_5637688 baseEnd_5637688 := by
    simpa [prefixWord, tailWord_5637688, baseEnd_5637688] using wordTrace_append hprefix tailTrace_5637688
  have hstable : (prefixWord ++ tailWord_5637688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637688).length < 2 ^ (prefixWord ++ tailWord_5637688).sum := by decide
  have hdescent : baseEnd_5637688 < baseStart_5637688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637731 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 5]
def baseStart_5637731 : Nat := 118140960795 + 5637731 * 2 ^ 59
def prefixEnd_5637731 : Nat := 4983230072969 + 3 ^ 40 * 5637731 * 2
def baseEnd_5637731 : Nat := 2894865803752987085235053

theorem tailTrace_5637731 : CollatzResearch.WordTrace tailWord_5637731 prefixEnd_5637731 2894865803752987085235053 := by
  unfold tailWord_5637731
  simp only [CollatzResearch.WordTrace]
  refine ⟨205624942338470909643681047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137083294892313939762454031 205624942338470909643681047)
  ·
    refine ⟨308437413507706364465521571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205624942338470909643681047 308437413507706364465521571)
    ·
      refine ⟨462656120261559546698282357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308437413507706364465521571 462656120261559546698282357)
      ·
        refine ⟨43374011274521207502963971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 462656120261559546698282357 43374011274521207502963971)
        ·
          refine ⟨65061016911781811254445957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43374011274521207502963971 65061016911781811254445957)
          ·
            refine ⟨12198940670959089610208617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65061016911781811254445957 12198940670959089610208617)
            ·
              refine ⟨9149205503219317207656463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12198940670959089610208617 9149205503219317207656463)
              ·
                refine ⟨13723808254828975811484695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9149205503219317207656463 13723808254828975811484695)
                ·
                  refine ⟨20585712382243463717227043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13723808254828975811484695 20585712382243463717227043)
                  ·
                    refine ⟨30878568573365195575840565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20585712382243463717227043 30878568573365195575840565)
                    ·
                      refine ⟨2894865803752987085235053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30878568573365195575840565 2894865803752987085235053)
                      ·
                        rfl

theorem cell23_5637731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_5637731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637731 prefixEnd_5637731 := by exact prefixLift 5637731
  have htrace : WordTrace (prefixWord ++ tailWord_5637731) baseStart_5637731 baseEnd_5637731 := by
    simpa [prefixWord, tailWord_5637731, baseEnd_5637731] using wordTrace_append hprefix tailTrace_5637731
  have hstable : (prefixWord ++ tailWord_5637731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637731).length < 2 ^ (prefixWord ++ tailWord_5637731).sum := by decide
  have hdescent : baseEnd_5637731 < baseStart_5637731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637745 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 1, 2, 2]
def baseStart_5637745 : Nat := 118140960795 + 5637745 * 2 ^ 59
def prefixEnd_5637745 : Nat := 4983230072969 + 3 ^ 40 * 5637745 * 2
def baseEnd_5637745 : Nat := 2894872992482150030459989

theorem tailTrace_5637745 : CollatzResearch.WordTrace tailWord_5637745 prefixEnd_5637745 2894872992482150030459989 := by
  unfold tailWord_5637745
  simp only [CollatzResearch.WordTrace]
  refine ⟨205625452960420190034690689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137083635306946793356460459 205625452960420190034690689)
  ·
    refine ⟨154219089720315142526018017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205625452960420190034690689 154219089720315142526018017)
    ·
      refine ⟨115664317290236356894513513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154219089720315142526018017 115664317290236356894513513)
      ·
        refine ⟨86748237967677267670885135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115664317290236356894513513 86748237967677267670885135)
        ·
          refine ⟨130122356951515901506327703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86748237967677267670885135 130122356951515901506327703)
          ·
            refine ⟨195183535427273852259491555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130122356951515901506327703 195183535427273852259491555)
            ·
              refine ⟨292775303140910778389237333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195183535427273852259491555 292775303140910778389237333)
              ·
                refine ⟨3430960583682548184248875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 292775303140910778389237333 3430960583682548184248875)
                ·
                  refine ⟨5146440875523822276373313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430960583682548184248875 5146440875523822276373313)
                  ·
                    refine ⟨3859830656642866707279985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146440875523822276373313 3859830656642866707279985)
                    ·
                      refine ⟨2894872992482150030459989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859830656642866707279985 2894872992482150030459989)
                      ·
                        rfl

theorem cell23_5637745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_5637745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637745 prefixEnd_5637745 := by exact prefixLift 5637745
  have htrace : WordTrace (prefixWord ++ tailWord_5637745) baseStart_5637745 baseEnd_5637745 := by
    simpa [prefixWord, tailWord_5637745, baseEnd_5637745] using wordTrace_append hprefix tailTrace_5637745
  have hstable : (prefixWord ++ tailWord_5637745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637745).length < 2 ^ (prefixWord ++ tailWord_5637745).sum := by decide
  have hdescent : baseEnd_5637745 < baseStart_5637745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637818 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2]
def baseStart_5637818 : Nat := 118140960795 + 5637818 * 2 ^ 59
def prefixEnd_5637818 : Nat := 4983230072969 + 3 ^ 40 * 5637818 * 2
def baseEnd_5637818 : Nat := 2894910476569928244847153

theorem tailTrace_5637818 : CollatzResearch.WordTrace tailWord_5637818 prefixEnd_5637818 2894910476569928244847153 := by
  unfold tailWord_5637818
  simp only [CollatzResearch.WordTrace]
  refine ⟨51407028872288930875524527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137085410326103815668065405 51407028872288930875524527)
  ·
    refine ⟨77110543308433396313286791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51407028872288930875524527 77110543308433396313286791)
    ·
      refine ⟨115665814962650094469930187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77110543308433396313286791 115665814962650094469930187)
      ·
        refine ⟨173498722443975141704895281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115665814962650094469930187 173498722443975141704895281)
        ·
          refine ⟨130124041832981356278671461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173498722443975141704895281 130124041832981356278671461)
          ·
            refine ⟨24398257843684004302250899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130124041832981356278671461 24398257843684004302250899)
            ·
              refine ⟨36597386765526006453376349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24398257843684004302250899 36597386765526006453376349)
              ·
                refine ⟨13724020037072252420016131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36597386765526006453376349 13724020037072252420016131)
                ·
                  refine ⟨20586030055608378630024197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13724020037072252420016131 20586030055608378630024197)
                  ·
                    refine ⟨3859880635426570993129537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20586030055608378630024197 3859880635426570993129537)
                    ·
                      refine ⟨2894910476569928244847153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859880635426570993129537 2894910476569928244847153)
                      ·
                        rfl

theorem cell23_5637818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_5637818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637818 prefixEnd_5637818 := by exact prefixLift 5637818
  have htrace : WordTrace (prefixWord ++ tailWord_5637818) baseStart_5637818 baseEnd_5637818 := by
    simpa [prefixWord, tailWord_5637818, baseEnd_5637818] using wordTrace_append hprefix tailTrace_5637818
  have hstable : (prefixWord ++ tailWord_5637818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637818).length < 2 ^ (prefixWord ++ tailWord_5637818).sum := by decide
  have hdescent : baseEnd_5637818 < baseStart_5637818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637821 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_5637821 : Nat := 118140960795 + 5637821 * 2 ^ 59
def prefixEnd_5637821 : Nat := 4983230072969 + 3 ^ 40 * 5637821 * 2
def baseEnd_5637821 : Nat := 2894912017011891733109639

theorem tailTrace_5637821 : CollatzResearch.WordTrace tailWord_5637821 prefixEnd_5637821 2894912017011891733109639 := by
  unfold tailWord_5637821
  simp only [CollatzResearch.WordTrace]
  refine ⟨205628224908144855014457317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137085483272096570009638211 205628224908144855014457317)
  ·
    refine ⟨38555292170277160315210747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205628224908144855014457317 38555292170277160315210747)
    ·
      refine ⟨57832938255415740472816121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38555292170277160315210747 57832938255415740472816121)
      ·
        refine ⟨43374703691561805354612091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57832938255415740472816121 43374703691561805354612091)
        ·
          refine ⟨65062055537342708031918137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43374703691561805354612091 65062055537342708031918137)
          ·
            refine ⟨48796541653007031023938603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65062055537342708031918137 48796541653007031023938603)
            ·
              refine ⟨73194812479510546535907905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48796541653007031023938603 73194812479510546535907905)
              ·
                refine ⟨54896109359632909901930929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73194812479510546535907905 54896109359632909901930929)
                ·
                  refine ⟨41172082019724682426448197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54896109359632909901930929 41172082019724682426448197)
                  ·
                    refine ⟨7719765378698377954959037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41172082019724682426448197 7719765378698377954959037)
                    ·
                      refine ⟨2894912017011891733109639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7719765378698377954959037 2894912017011891733109639)
                      ·
                        rfl

theorem cell23_5637821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_5637821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637821 prefixEnd_5637821 := by exact prefixLift 5637821
  have htrace : WordTrace (prefixWord ++ tailWord_5637821) baseStart_5637821 baseEnd_5637821 := by
    simpa [prefixWord, tailWord_5637821, baseEnd_5637821] using wordTrace_append hprefix tailTrace_5637821
  have hstable : (prefixWord ++ tailWord_5637821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637821).length < 2 ^ (prefixWord ++ tailWord_5637821).sum := by decide
  have hdescent : baseEnd_5637821 < baseStart_5637821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637846 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5637846 : Nat := 118140960795 + 5637846 * 2 ^ 59
def prefixEnd_5637846 : Nat := 4983230072969 + 3 ^ 40 * 5637846 * 2
def baseEnd_5637846 : Nat := 2894924854028254135297025

theorem tailTrace_5637846 : CollatzResearch.WordTrace tailWord_5637846 prefixEnd_5637846 2894924854028254135297025 := by
  unfold tailWord_5637846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12851821045815892767757337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137086091155369522856078261 12851821045815892767757337)
  ·
    refine ⟨9638865784361919575818003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12851821045815892767757337 9638865784361919575818003)
    ·
      refine ⟨14458298676542879363727005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9638865784361919575818003 14458298676542879363727005)
      ·
        refine ⟨5421862003703579761397627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14458298676542879363727005 5421862003703579761397627)
        ·
          refine ⟨8132793005555369642096441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5421862003703579761397627 8132793005555369642096441)
          ·
            refine ⟨6099594754166527231572331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8132793005555369642096441 6099594754166527231572331)
            ·
              refine ⟨9149392131249790847358497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099594754166527231572331 9149392131249790847358497)
              ·
                refine ⟨6862044098437343135518873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9149392131249790847358497 6862044098437343135518873)
                ·
                  refine ⟨5146533073828007351639155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6862044098437343135518873 5146533073828007351639155)
                  ·
                    refine ⟨7719799610742011027458733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5146533073828007351639155 7719799610742011027458733)
                    ·
                      refine ⟨2894924854028254135297025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7719799610742011027458733 2894924854028254135297025)
                      ·
                        rfl

theorem cell23_5637846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5637846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637846 prefixEnd_5637846 := by exact prefixLift 5637846
  have htrace : WordTrace (prefixWord ++ tailWord_5637846) baseStart_5637846 baseEnd_5637846 := by
    simpa [prefixWord, tailWord_5637846, baseEnd_5637846] using wordTrace_append hprefix tailTrace_5637846
  have hstable : (prefixWord ++ tailWord_5637846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637846).length < 2 ^ (prefixWord ++ tailWord_5637846).sum := by decide
  have hdescent : baseEnd_5637846 < baseStart_5637846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637869 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5637869 : Nat := 118140960795 + 5637869 * 2 ^ 59
def prefixEnd_5637869 : Nat := 4983230072969 + 3 ^ 40 * 5637869 * 2
def baseEnd_5637869 : Nat := 2894936664083307545309419

theorem tailTrace_5637869 : CollatzResearch.WordTrace tailWord_5637869 prefixEnd_5637869 2894936664083307545309419 := by
  unfold tailWord_5637869
  simp only [CollatzResearch.WordTrace]
  refine ⟨205629975611970959212204661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137086650407980639474803107 205629975611970959212204661)
  ·
    refine ⟨19277810213622277426144187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205629975611970959212204661 19277810213622277426144187)
    ·
      refine ⟨28916715320433416139216281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19277810213622277426144187 28916715320433416139216281)
      ·
        refine ⟨21687536490325062104412211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28916715320433416139216281 21687536490325062104412211)
        ·
          refine ⟨32531304735487593156618317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21687536490325062104412211 32531304735487593156618317)
          ·
            refine ⟨12199239275807847433731869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32531304735487593156618317 12199239275807847433731869)
            ·
              refine ⟨4574714728427942787649451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12199239275807847433731869 4574714728427942787649451)
              ·
                refine ⟨6862072092641914181474177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574714728427942787649451 6862072092641914181474177)
                ·
                  refine ⟨5146554069481435636105633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6862072092641914181474177 5146554069481435636105633)
                  ·
                    refine ⟨3859915552111076727079225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146554069481435636105633 3859915552111076727079225)
                    ·
                      refine ⟨2894936664083307545309419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859915552111076727079225 2894936664083307545309419)
                      ·
                        rfl

theorem cell23_5637869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5637869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637869 prefixEnd_5637869 := by exact prefixLift 5637869
  have htrace : WordTrace (prefixWord ++ tailWord_5637869) baseStart_5637869 baseEnd_5637869 := by
    simpa [prefixWord, tailWord_5637869, baseEnd_5637869] using wordTrace_append hprefix tailTrace_5637869
  have hstable : (prefixWord ++ tailWord_5637869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637869).length < 2 ^ (prefixWord ++ tailWord_5637869).sum := by decide
  have hdescent : baseEnd_5637869 < baseStart_5637869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637891 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4]
def baseStart_5637891 : Nat := 118140960795 + 5637891 * 2 ^ 59
def prefixEnd_5637891 : Nat := 4983230072969 + 3 ^ 40 * 5637891 * 2
def baseEnd_5637891 : Nat := 2894947960657706459234317

theorem tailTrace_5637891 : CollatzResearch.WordTrace tailWord_5637891 prefixEnd_5637891 2894947960657706459234317 := by
  unfold tailWord_5637891
  simp only [CollatzResearch.WordTrace]
  refine ⟨205630778017891256969505527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137087185345260837979670351 205630778017891256969505527)
  ·
    refine ⟨308446167026836885454258291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205630778017891256969505527 308446167026836885454258291)
    ·
      refine ⟨462669250540255328181387437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308446167026836885454258291 462669250540255328181387437)
      ·
        refine ⟨173500968952595748068020289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462669250540255328181387437 173500968952595748068020289)
        ·
          refine ⟨130125726714446811051015217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173500968952595748068020289 130125726714446811051015217)
          ·
            refine ⟨97594295035835108288261413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130125726714446811051015217 97594295035835108288261413)
            ·
              refine ⟨18298930319219082804049015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97594295035835108288261413 18298930319219082804049015)
              ·
                refine ⟨27448395478828624206073523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18298930319219082804049015 27448395478828624206073523)
                ·
                  refine ⟨41172593218242936309110285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27448395478828624206073523 41172593218242936309110285)
                  ·
                    refine ⟨15439722456841101115916357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41172593218242936309110285 15439722456841101115916357)
                    ·
                      refine ⟨2894947960657706459234317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15439722456841101115916357 2894947960657706459234317)
                      ·
                        rfl

theorem cell23_5637891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_5637891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637891 prefixEnd_5637891 := by exact prefixLift 5637891
  have htrace : WordTrace (prefixWord ++ tailWord_5637891) baseStart_5637891 baseEnd_5637891 := by
    simpa [prefixWord, tailWord_5637891, baseEnd_5637891] using wordTrace_append hprefix tailTrace_5637891
  have hstable : (prefixWord ++ tailWord_5637891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637891).length < 2 ^ (prefixWord ++ tailWord_5637891).sum := by decide
  have hdescent : baseEnd_5637891 < baseStart_5637891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637942 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5637942 : Nat := 118140960795 + 5637942 * 2 ^ 59
def prefixEnd_5637942 : Nat := 4983230072969 + 3 ^ 40 * 5637942 * 2
def baseEnd_5637942 : Nat := 2894974148171085759696583

theorem tailTrace_5637942 : CollatzResearch.WordTrace tailWord_5637942 prefixEnd_5637942 2894974148171085759696583 := by
  unfold tailWord_5637942
  simp only [CollatzResearch.WordTrace]
  refine ⟨12852039883794155792475755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137088425427137661786408053 12852039883794155792475755)
  ·
    refine ⟨19278059825691233688713633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12852039883794155792475755 19278059825691233688713633)
    ·
      refine ⟨14458544869268425266535225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19278059825691233688713633 14458544869268425266535225)
      ·
        refine ⟨10843908651951318949901419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14458544869268425266535225 10843908651951318949901419)
        ·
          refine ⟨16265862977926978424852129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10843908651951318949901419 16265862977926978424852129)
          ·
            refine ⟨12199397233445233818639097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16265862977926978424852129 12199397233445233818639097)
            ·
              refine ⟨9149547925083925363979323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12199397233445233818639097 9149547925083925363979323)
              ·
                refine ⟨13724321887625888045968985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9149547925083925363979323 13724321887625888045968985)
                ·
                  refine ⟨10293241415719416034476739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13724321887625888045968985 10293241415719416034476739)
                  ·
                    refine ⟨15439862123579124051715109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10293241415719416034476739 15439862123579124051715109)
                    ·
                      refine ⟨2894974148171085759696583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15439862123579124051715109 2894974148171085759696583)
                      ·
                        rfl

theorem cell23_5637942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5637942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637942 prefixEnd_5637942 := by exact prefixLift 5637942
  have htrace : WordTrace (prefixWord ++ tailWord_5637942) baseStart_5637942 baseEnd_5637942 := by
    simpa [prefixWord, tailWord_5637942, baseEnd_5637942] using wordTrace_append hprefix tailTrace_5637942
  have hstable : (prefixWord ++ tailWord_5637942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637942).length < 2 ^ (prefixWord ++ tailWord_5637942).sum := by decide
  have hdescent : baseEnd_5637942 < baseStart_5637942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637965 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5637965 : Nat := 118140960795 + 5637965 * 2 ^ 59
def prefixEnd_5637965 : Nat := 4983230072969 + 3 ^ 40 * 5637965 * 2
def baseEnd_5637965 : Nat := 321665106469571018856553

theorem tailTrace_5637965 : CollatzResearch.WordTrace tailWord_5637965 prefixEnd_5637965 321665106469571018856553 := by
  unfold tailWord_5637965
  simp only [CollatzResearch.WordTrace]
  refine ⟨205633477019623167607699349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137088984679748778405132899 205633477019623167607699349)
  ·
    refine ⟨9639069235294835981610907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205633477019623167607699349 9639069235294835981610907)
    ·
      refine ⟨14458603852942253972416361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9639069235294835981610907 14458603852942253972416361)
      ·
        refine ⟨10843952889706690479312271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14458603852942253972416361 10843952889706690479312271)
        ·
          refine ⟨16265929334560035718968407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10843952889706690479312271 16265929334560035718968407)
          ·
            refine ⟨24398894001840053578452611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265929334560035718968407 24398894001840053578452611)
            ·
              refine ⟨36598341002760080367678917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24398894001840053578452611 36598341002760080367678917)
              ·
                refine ⟨6862188938017515068939797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36598341002760080367678917 6862188938017515068939797)
                ·
                  refine ⟨321665106469571018856553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6862188938017515068939797 321665106469571018856553)
                  ·
                    rfl

theorem cell23_5637965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5637965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637965 prefixEnd_5637965 := by exact prefixLift 5637965
  have htrace : WordTrace (prefixWord ++ tailWord_5637965) baseStart_5637965 baseEnd_5637965 := by
    simpa [prefixWord, tailWord_5637965, baseEnd_5637965] using wordTrace_append hprefix tailTrace_5637965
  have hstable : (prefixWord ++ tailWord_5637965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637965).length < 2 ^ (prefixWord ++ tailWord_5637965).sum := by decide
  have hdescent : baseEnd_5637965 < baseStart_5637965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637968 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 3, 5, 2]
def baseStart_5637968 : Nat := 118140960795 + 5637968 * 2 ^ 59
def prefixEnd_5637968 : Nat := 4983230072969 + 3 ^ 40 * 5637968 * 2
def baseEnd_5637968 : Nat := 2894987498668102657971463

theorem tailTrace_5637968 : CollatzResearch.WordTrace tailWord_5637968 prefixEnd_5637968 2894987498668102657971463 := by
  unfold tailWord_5637968
  simp only [CollatzResearch.WordTrace]
  refine ⟨102816793219306149560029279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137089057625741532746705705 102816793219306149560029279)
  ·
    refine ⟨154225189828959224340043919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102816793219306149560029279 154225189828959224340043919)
    ·
      refine ⟨231337784743438836510065879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154225189828959224340043919 231337784743438836510065879)
      ·
        refine ⟨347006677115158254765098819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231337784743438836510065879 347006677115158254765098819)
        ·
          refine ⟨520510015672737382147648229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347006677115158254765098819 520510015672737382147648229)
          ·
            refine ⟨97595627938638259152684043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 520510015672737382147648229 97595627938638259152684043)
            ·
              refine ⟨146393441907957388729026065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97595627938638259152684043 146393441907957388729026065)
              ·
                refine ⟨109795081430968041546769549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146393441907957388729026065 109795081430968041546769549)
                ·
                  refine ⟨41173155536613015580038581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109795081430968041546769549 41173155536613015580038581)
                  ·
                    refine ⟨3859983331557470210628617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41173155536613015580038581 3859983331557470210628617)
                    ·
                      refine ⟨2894987498668102657971463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3859983331557470210628617 2894987498668102657971463)
                      ·
                        rfl

theorem cell23_5637968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 5, 2].length) (baseStart_5637968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637968 prefixEnd_5637968 := by exact prefixLift 5637968
  have htrace : WordTrace (prefixWord ++ tailWord_5637968) baseStart_5637968 baseEnd_5637968 := by
    simpa [prefixWord, tailWord_5637968, baseEnd_5637968] using wordTrace_append hprefix tailTrace_5637968
  have hstable : (prefixWord ++ tailWord_5637968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637968).length < 2 ^ (prefixWord ++ tailWord_5637968).sum := by decide
  have hdescent : baseEnd_5637968 < baseStart_5637968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5637969 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 1, 4]
def baseStart_5637969 : Nat := 118140960795 + 5637969 * 2 ^ 59
def prefixEnd_5637969 : Nat := 4983230072969 + 3 ^ 40 * 5637969 * 2
def baseEnd_5637969 : Nat := 964996004049585718019653

theorem tailTrace_5637969 : CollatzResearch.WordTrace tailWord_5637969 prefixEnd_5637969 964996004049585718019653 := by
  unfold tailWord_5637969
  simp only [CollatzResearch.WordTrace]
  refine ⟨205633622911608676290844961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137089081941072450860563307 205633622911608676290844961)
  ·
    refine ⟨154225217183706507218133721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205633622911608676290844961 154225217183706507218133721)
    ·
      refine ⟨115668912887779880413600291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154225217183706507218133721 115668912887779880413600291)
      ·
        refine ⟨173503369331669820620400437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115668912887779880413600291 173503369331669820620400437)
        ·
          refine ⟨16265940874844045683162541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173503369331669820620400437 16265940874844045683162541)
          ·
            refine ⟨6099727828066517131185953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16265940874844045683162541 6099727828066517131185953)
            ·
              refine ⟨4574795871049887848389465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6099727828066517131185953 4574795871049887848389465)
              ·
                refine ⟨3431096903287415886292099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4574795871049887848389465 3431096903287415886292099)
                ·
                  refine ⟨5146645354931123829438149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431096903287415886292099 5146645354931123829438149)
                  ·
                    refine ⟨964996004049585718019653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5146645354931123829438149 964996004049585718019653)
                    ·
                      rfl

theorem cell23_5637969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_5637969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5637969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5637969 prefixEnd_5637969 := by exact prefixLift 5637969
  have htrace : WordTrace (prefixWord ++ tailWord_5637969) baseStart_5637969 baseEnd_5637969 := by
    simpa [prefixWord, tailWord_5637969, baseEnd_5637969] using wordTrace_append hprefix tailTrace_5637969
  have hstable : (prefixWord ++ tailWord_5637969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5637969).length < 2 ^ (prefixWord ++ tailWord_5637969).sum := by decide
  have hdescent : baseEnd_5637969 < baseStart_5637969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5637969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638011 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_5638011 : Nat := 118140960795 + 5638011 * 2 ^ 59
def prefixEnd_5638011 : Nat := 4983230072969 + 3 ^ 40 * 5638011 * 2
def baseEnd_5638011 : Nat := 2895009578336245989733765

theorem tailTrace_5638011 : CollatzResearch.WordTrace tailWord_5638011 prefixEnd_5638011 2895009578336245989733765 := by
  unfold tailWord_5638011
  simp only [CollatzResearch.WordTrace]
  refine ⟨205635154777456517463873887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137090103184971011642582591 205635154777456517463873887)
  ·
    refine ⟨308452732166184776195810831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205635154777456517463873887 308452732166184776195810831)
    ·
      refine ⟨462679098249277164293716247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308452732166184776195810831 462679098249277164293716247)
      ·
        refine ⟨694018647373915746440574371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462679098249277164293716247 694018647373915746440574371)
        ·
          refine ⟨1041027971060873619660861557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694018647373915746440574371 1041027971060873619660861557)
          ·
            refine ⟨97596372286956901843205771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1041027971060873619660861557 97596372286956901843205771)
            ·
              refine ⟨146394558430435352764808657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97596372286956901843205771 146394558430435352764808657)
              ·
                refine ⟨109795918822826514573606493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146394558430435352764808657 109795918822826514573606493)
                ·
                  refine ⟨41173469558559942965102435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109795918822826514573606493 41173469558559942965102435)
                  ·
                    refine ⟨61760204337839914447653653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41173469558559942965102435 61760204337839914447653653)
                    ·
                      refine ⟨2895009578336245989733765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61760204337839914447653653 2895009578336245989733765)
                      ·
                        rfl

theorem cell23_5638011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_5638011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638011 prefixEnd_5638011 := by exact prefixLift 5638011
  have htrace : WordTrace (prefixWord ++ tailWord_5638011) baseStart_5638011 baseEnd_5638011 := by
    simpa [prefixWord, tailWord_5638011, baseEnd_5638011] using wordTrace_append hprefix tailTrace_5638011
  have hstable : (prefixWord ++ tailWord_5638011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638011).length < 2 ^ (prefixWord ++ tailWord_5638011).sum := by decide
  have hdescent : baseEnd_5638011 < baseStart_5638011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638015 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 7, 2, 2]
def baseStart_5638015 : Nat := 118140960795 + 5638015 * 2 ^ 59
def prefixEnd_5638015 : Nat := 4983230072969 + 3 ^ 40 * 5638015 * 2
def baseEnd_5638015 : Nat := 2895011632258863974083747

theorem tailTrace_5638015 : CollatzResearch.WordTrace tailWord_5638015 prefixEnd_5638015 2895011632258863974083747 := by
  unfold tailWord_5638015
  simp only [CollatzResearch.WordTrace]
  refine ⟨205635300669442026147019499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137090200446294684098012999 205635300669442026147019499)
  ·
    refine ⟨308452951004163039220529249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205635300669442026147019499 308452951004163039220529249)
    ·
      refine ⟨231339713253122279415396937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308452951004163039220529249 231339713253122279415396937)
      ·
        refine ⟨173504784939841709561547703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231339713253122279415396937 173504784939841709561547703)
        ·
          refine ⟨260257177409762564342321555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173504784939841709561547703 260257177409762564342321555)
          ·
            refine ⟨390385766114643846513482333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260257177409762564342321555 390385766114643846513482333)
            ·
              refine ⟨146394662292991442442555875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390385766114643846513482333 146394662292991442442555875)
              ·
                refine ⟨219591993439487163663833813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146394662292991442442555875 219591993439487163663833813)
                ·
                  refine ⟨5146687346237980398371105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 219591993439487163663833813 5146687346237980398371105)
                  ·
                    refine ⟨3860015509678485298778329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146687346237980398371105 3860015509678485298778329)
                    ·
                      refine ⟨2895011632258863974083747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860015509678485298778329 2895011632258863974083747)
                      ·
                        rfl

theorem cell23_5638015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_5638015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638015 prefixEnd_5638015 := by exact prefixLift 5638015
  have htrace : WordTrace (prefixWord ++ tailWord_5638015) baseStart_5638015 baseEnd_5638015 := by
    simpa [prefixWord, tailWord_5638015, baseEnd_5638015] using wordTrace_append hprefix tailTrace_5638015
  have hstable : (prefixWord ++ tailWord_5638015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638015).length < 2 ^ (prefixWord ++ tailWord_5638015).sum := by decide
  have hdescent : baseEnd_5638015 < baseStart_5638015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638021 : List Nat := [1, 3, 1, 1, 3, 2, 12]
def baseStart_5638021 : Nat := 118140960795 + 5638021 * 2 ^ 59
def prefixEnd_5638021 : Nat := 4983230072969 + 3 ^ 40 * 5638021 * 2
def baseEnd_5638021 : Nat := 35740922384478900624799

theorem tailTrace_5638021 : CollatzResearch.WordTrace tailWord_5638021 prefixEnd_5638021 35740922384478900624799 := by
  unfold tailWord_5638021
  simp only [CollatzResearch.WordTrace]
  refine ⟨205635519507420289171737917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137090346338280192781158611 205635519507420289171737917)
  ·
    refine ⟨77113319815282608439401719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205635519507420289171737917 77113319815282608439401719)
    ·
      refine ⟨115669979722923912659102579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77113319815282608439401719 115669979722923912659102579)
      ·
        refine ⟨173504969584385868988653869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115669979722923912659102579 173504969584385868988653869)
        ·
          refine ⟨65064363594144700870745201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173504969584385868988653869 65064363594144700870745201)
          ·
            refine ⟨48798272695608525653058901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65064363594144700870745201 48798272695608525653058901)
            ·
              refine ⟨35740922384478900624799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 48798272695608525653058901 35740922384478900624799)
              ·
                rfl

theorem cell23_5638021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 12].length) (baseStart_5638021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638021 prefixEnd_5638021 := by exact prefixLift 5638021
  have htrace : WordTrace (prefixWord ++ tailWord_5638021) baseStart_5638021 baseEnd_5638021 := by
    simpa [prefixWord, tailWord_5638021, baseEnd_5638021] using wordTrace_append hprefix tailTrace_5638021
  have hstable : (prefixWord ++ tailWord_5638021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638021).length < 2 ^ (prefixWord ++ tailWord_5638021).sum := by decide
  have hdescent : baseEnd_5638021 < baseStart_5638021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638045 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_5638045 : Nat := 118140960795 + 5638045 * 2 ^ 59
def prefixEnd_5638045 : Nat := 4983230072969 + 3 ^ 40 * 5638045 * 2
def baseEnd_5638045 : Nat := 2895027036678498856708609

theorem tailTrace_5638045 : CollatzResearch.WordTrace tailWord_5638045 prefixEnd_5638045 2895027036678498856708609 := by
  unfold tailWord_5638045
  simp only [CollatzResearch.WordTrace]
  refine ⟨205636394859333341270611589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137090929906222227513741059 205636394859333341270611589)
  ·
    refine ⟨38556824036125001488239673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205636394859333341270611589 38556824036125001488239673)
    ·
      refine ⟨28917618027093751116179755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38556824036125001488239673 28917618027093751116179755)
      ·
        refine ⟨43376427040640626674269633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28917618027093751116179755 43376427040640626674269633)
        ·
          refine ⟨32532320280480470005702225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43376427040640626674269633 32532320280480470005702225)
          ·
            refine ⟨24399240210360352504276669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32532320280480470005702225 24399240210360352504276669)
            ·
              refine ⟨9149715078885132189103751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24399240210360352504276669 9149715078885132189103751)
              ·
                refine ⟨13724572618327698283655627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9149715078885132189103751 13724572618327698283655627)
                ·
                  refine ⟨20586858927491547425483441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13724572618327698283655627 20586858927491547425483441)
                  ·
                    refine ⟨15440144195618660569112581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20586858927491547425483441 15440144195618660569112581)
                    ·
                      refine ⟨2895027036678498856708609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15440144195618660569112581 2895027036678498856708609)
                      ·
                        rfl

theorem cell23_5638045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_5638045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638045 prefixEnd_5638045 := by exact prefixLift 5638045
  have htrace : WordTrace (prefixWord ++ tailWord_5638045) baseStart_5638045 baseEnd_5638045 := by
    simpa [prefixWord, tailWord_5638045, baseEnd_5638045] using wordTrace_append hprefix tailTrace_5638045
  have hstable : (prefixWord ++ tailWord_5638045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638045).length < 2 ^ (prefixWord ++ tailWord_5638045).sum := by decide
  have hdescent : baseEnd_5638045 < baseStart_5638045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638052 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_5638052 : Nat := 118140960795 + 5638052 * 2 ^ 59
def prefixEnd_5638052 : Nat := 4983230072969 + 3 ^ 40 * 5638052 * 2
def baseEnd_5638052 : Nat := 2895030631043080329321077

theorem tailTrace_5638052 : CollatzResearch.WordTrace tailWord_5638052 prefixEnd_5638052 2895030631043080329321077 := by
  unfold tailWord_5638052
  simp only [CollatzResearch.WordTrace]
  refine ⟨102818325085153990733058205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137091100113538654310744273 102818325085153990733058205)
  ·
    refine ⟨38556871906932746524896827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102818325085153990733058205 38556871906932746524896827)
    ·
      refine ⟨57835307860399119787345241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38556871906932746524896827 57835307860399119787345241)
      ·
        refine ⟨43376480895299339840508931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57835307860399119787345241 43376480895299339840508931)
        ·
          refine ⟨65064721342949009760763397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43376480895299339840508931 65064721342949009760763397)
          ·
            refine ⟨12199635251802939330143137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65064721342949009760763397 12199635251802939330143137)
            ·
              refine ⟨9149726438852204497607353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12199635251802939330143137 9149726438852204497607353)
              ·
                refine ⟨6862294829139153373205515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9149726438852204497607353 6862294829139153373205515)
                ·
                  refine ⟨10293442243708730059808273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862294829139153373205515 10293442243708730059808273)
                  ·
                    refine ⟨7720081682781547544856205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10293442243708730059808273 7720081682781547544856205)
                    ·
                      refine ⟨2895030631043080329321077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720081682781547544856205 2895030631043080329321077)
                      ·
                        rfl

theorem cell23_5638052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_5638052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638052 prefixEnd_5638052 := by exact prefixLift 5638052
  have htrace : WordTrace (prefixWord ++ tailWord_5638052) baseStart_5638052 baseEnd_5638052 := by
    simpa [prefixWord, tailWord_5638052, baseEnd_5638052] using wordTrace_append hprefix tailTrace_5638052
  have hstable : (prefixWord ++ tailWord_5638052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638052).length < 2 ^ (prefixWord ++ tailWord_5638052).sum := by decide
  have hdescent : baseEnd_5638052 < baseStart_5638052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638055 : List Nat := [1, 1, 6, 1, 2, 1, 4, 7]
def baseStart_5638055 : Nat := 118140960795 + 5638055 * 2 ^ 59
def prefixEnd_5638055 : Nat := 4983230072969 + 3 ^ 40 * 5638055 * 2
def baseEnd_5638055 : Nat := 107223413758705326577169

theorem tailTrace_5638055 : CollatzResearch.WordTrace tailWord_5638055 prefixEnd_5638055 107223413758705326577169 := by
  unfold tailWord_5638055
  simp only [CollatzResearch.WordTrace]
  refine ⟨205636759589297112978475619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137091173059531408652317079 205636759589297112978475619)
  ·
    refine ⟨308455139383945669467713429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205636759589297112978475619 308455139383945669467713429)
    ·
      refine ⟨14458834658622453256299067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 308455139383945669467713429 14458834658622453256299067)
      ·
        refine ⟨21688251987933679884448601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14458834658622453256299067 21688251987933679884448601)
        ·
          refine ⟨16266188990950259913336451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21688251987933679884448601 16266188990950259913336451)
          ·
            refine ⟨24399283486425389870004677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16266188990950259913336451 24399283486425389870004677)
            ·
              refine ⟨4574865653704760600625877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24399283486425389870004677 4574865653704760600625877)
              ·
                refine ⟨107223413758705326577169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4574865653704760600625877 107223413758705326577169)
                ·
                  rfl

theorem cell23_5638055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 7].length) (baseStart_5638055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638055 prefixEnd_5638055 := by exact prefixLift 5638055
  have htrace : WordTrace (prefixWord ++ tailWord_5638055) baseStart_5638055 baseEnd_5638055 := by
    simpa [prefixWord, tailWord_5638055, baseEnd_5638055] using wordTrace_append hprefix tailTrace_5638055
  have hstable : (prefixWord ++ tailWord_5638055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638055).length < 2 ^ (prefixWord ++ tailWord_5638055).sum := by decide
  have hdescent : baseEnd_5638055 < baseStart_5638055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638109 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_5638109 : Nat := 118140960795 + 5638109 * 2 ^ 59
def prefixEnd_5638109 : Nat := 4983230072969 + 3 ^ 40 * 5638109 * 2
def baseEnd_5638109 : Nat := 2895059899440386606308315

theorem tailTrace_5638109 : CollatzResearch.WordTrace tailWord_5638109 prefixEnd_5638109 2895059899440386606308315 := by
  unfold tailWord_5638109
  simp only [CollatzResearch.WordTrace]
  refine ⟨205638729131101480200941381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137092486087400986800627587 205638729131101480200941381)
  ·
    refine ⟨38557261712081527537676509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205638729131101480200941381 38557261712081527537676509)
    ·
      refine ⟨14458973142030572826628691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38557261712081527537676509 14458973142030572826628691)
      ·
        refine ⟨21688459713045859239943037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14458973142030572826628691 21688459713045859239943037)
        ·
          refine ⟨8133172392392197214978639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21688459713045859239943037 8133172392392197214978639)
          ·
            refine ⟨12199758588588295822467959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133172392392197214978639 12199758588588295822467959)
            ·
              refine ⟨18299637882882443733701939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12199758588588295822467959 18299637882882443733701939)
              ·
                refine ⟨27449456824323665600552909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18299637882882443733701939 27449456824323665600552909)
                ·
                  refine ⟨10293546309121374600207341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27449456824323665600552909 10293546309121374600207341)
                  ·
                    refine ⟨3860079865920515475077753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10293546309121374600207341 3860079865920515475077753)
                    ·
                      refine ⟨2895059899440386606308315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860079865920515475077753 2895059899440386606308315)
                      ·
                        rfl

theorem cell23_5638109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_5638109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638109 prefixEnd_5638109 := by exact prefixLift 5638109
  have htrace : WordTrace (prefixWord ++ tailWord_5638109) baseStart_5638109 baseEnd_5638109 := by
    simpa [prefixWord, tailWord_5638109, baseEnd_5638109] using wordTrace_append hprefix tailTrace_5638109
  have hstable : (prefixWord ++ tailWord_5638109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638109).length < 2 ^ (prefixWord ++ tailWord_5638109).sum := by decide
  have hdescent : baseEnd_5638109 < baseStart_5638109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638122 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_5638122 : Nat := 118140960795 + 5638122 * 2 ^ 59
def prefixEnd_5638122 : Nat := 4983230072969 + 3 ^ 40 * 5638122 * 2
def baseEnd_5638122 : Nat := 2895066574688895055445755

theorem tailTrace_5638122 : CollatzResearch.WordTrace tailWord_5638122 prefixEnd_5638122 2895066574688895055445755 := by
  unfold tailWord_5638122
  simp only [CollatzResearch.WordTrace]
  refine ⟨51409800820013595855291155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137092802186702922280776413 51409800820013595855291155)
  ·
    refine ⟨77114701230020393782936733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51409800820013595855291155 77114701230020393782936733)
    ·
      refine ⟨28918012961257647668601275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77114701230020393782936733 28918012961257647668601275)
      ·
        refine ⟨43377019441886471502901913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28918012961257647668601275 43377019441886471502901913)
        ·
          refine ⟨32532764581414853627176435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43377019441886471502901913 32532764581414853627176435)
          ·
            refine ⟨48799146872122280440764653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32532764581414853627176435 48799146872122280440764653)
            ·
              refine ⟨18299680077045855165286745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48799146872122280440764653 18299680077045855165286745)
              ·
                refine ⟨13724760057784391373965059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18299680077045855165286745 13724760057784391373965059)
                ·
                  refine ⟨20587140086676587060947589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13724760057784391373965059 20587140086676587060947589)
                  ·
                    refine ⟨3860088766251860073927673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20587140086676587060947589 3860088766251860073927673)
                    ·
                      refine ⟨2895066574688895055445755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860088766251860073927673 2895066574688895055445755)
                      ·
                        rfl

theorem cell23_5638122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_5638122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638122 prefixEnd_5638122 := by exact prefixLift 5638122
  have htrace : WordTrace (prefixWord ++ tailWord_5638122) baseStart_5638122 baseEnd_5638122 := by
    simpa [prefixWord, tailWord_5638122, baseEnd_5638122] using wordTrace_append hprefix tailTrace_5638122
  have hstable : (prefixWord ++ tailWord_5638122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638122).length < 2 ^ (prefixWord ++ tailWord_5638122).sum := by decide
  have hdescent : baseEnd_5638122 < baseStart_5638122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638126 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_5638126 : Nat := 118140960795 + 5638126 * 2 ^ 59
def prefixEnd_5638126 : Nat := 4983230072969 + 3 ^ 40 * 5638126 * 2
def baseEnd_5638126 : Nat := 2895068628611513039795737

theorem tailTrace_5638126 : CollatzResearch.WordTrace tailWord_5638126 prefixEnd_5638126 2895068628611513039795737 := by
  unfold tailWord_5638126
  simp only [CollatzResearch.WordTrace]
  refine ⟨25704918646504986513038779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137092899448026594736206821 25704918646504986513038779)
  ·
    refine ⟨38557377969757479769558169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25704918646504986513038779 38557377969757479769558169)
    ·
      refine ⟨28918033477318109827168627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38557377969757479769558169 28918033477318109827168627)
      ·
        refine ⟨43377050215977164740752941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28918033477318109827168627 43377050215977164740752941)
        ·
          refine ⟨16266393830991436777782353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43377050215977164740752941 16266393830991436777782353)
          ·
            refine ⟨12199795373243577583336765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16266393830991436777782353 12199795373243577583336765)
            ·
              refine ⟨4574923264966341593751287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12199795373243577583336765 4574923264966341593751287)
              ·
                refine ⟨6862384897449512390626931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574923264966341593751287 6862384897449512390626931)
                ·
                  refine ⟨10293577346174268585940397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862384897449512390626931 10293577346174268585940397)
                  ·
                    refine ⟨3860091504815350719727649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10293577346174268585940397 3860091504815350719727649)
                    ·
                      refine ⟨2895068628611513039795737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860091504815350719727649 2895068628611513039795737)
                      ·
                        rfl

theorem cell23_5638126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_5638126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638126 prefixEnd_5638126 := by exact prefixLift 5638126
  have htrace : WordTrace (prefixWord ++ tailWord_5638126) baseStart_5638126 baseEnd_5638126 := by
    simpa [prefixWord, tailWord_5638126, baseEnd_5638126] using wordTrace_append hprefix tailTrace_5638126
  have hstable : (prefixWord ++ tailWord_5638126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638126).length < 2 ^ (prefixWord ++ tailWord_5638126).sum := by decide
  have hdescent : baseEnd_5638126 < baseStart_5638126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638142 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5638142 : Nat := 118140960795 + 5638142 * 2 ^ 59
def prefixEnd_5638142 : Nat := 4983230072969 + 3 ^ 40 * 5638142 * 2
def baseEnd_5638142 : Nat := 2895076844301984977195663

theorem tailTrace_5638142 : CollatzResearch.WordTrace tailWord_5638142 prefixEnd_5638142 2895076844301984977195663 := by
  unfold tailWord_5638142
  simp only [CollatzResearch.WordTrace]
  refine ⟨25704991592497740854611585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137093288493321284557928453 25704991592497740854611585)
  ·
    refine ⟨19278743694373305640958689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25704991592497740854611585 19278743694373305640958689)
    ·
      refine ⟨14459057770779979230719017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19278743694373305640958689 14459057770779979230719017)
      ·
        refine ⟨10844293328084984423039263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14459057770779979230719017 10844293328084984423039263)
        ·
          refine ⟨16266439992127476634558895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844293328084984423039263 16266439992127476634558895)
          ·
            refine ⟨24399659988191214951838343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16266439992127476634558895 24399659988191214951838343)
            ·
              refine ⟨36599489982286822427757515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24399659988191214951838343 36599489982286822427757515)
              ·
                refine ⟨54899234973430233641636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36599489982286822427757515 54899234973430233641636273)
                ·
                  refine ⟨41174426230072675231227205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54899234973430233641636273 41174426230072675231227205)
                  ·
                    refine ⟨7720204918138626605855101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41174426230072675231227205 7720204918138626605855101)
                    ·
                      refine ⟨2895076844301984977195663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720204918138626605855101 2895076844301984977195663)
                      ·
                        rfl

theorem cell23_5638142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5638142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638142 prefixEnd_5638142 := by exact prefixLift 5638142
  have htrace : WordTrace (prefixWord ++ tailWord_5638142) baseStart_5638142 baseEnd_5638142 := by
    simpa [prefixWord, tailWord_5638142, baseEnd_5638142] using wordTrace_append hprefix tailTrace_5638142
  have hstable : (prefixWord ++ tailWord_5638142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638142).length < 2 ^ (prefixWord ++ tailWord_5638142).sum := by decide
  have hdescent : baseEnd_5638142 < baseStart_5638142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638155 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 3]
def baseStart_5638155 : Nat := 118140960795 + 5638155 * 2 ^ 59
def prefixEnd_5638155 : Nat := 4983230072969 + 3 ^ 40 * 5638155 * 2
def baseEnd_5638155 : Nat := 2895083519550493426333103

theorem tailTrace_5638155 : CollatzResearch.WordTrace tailWord_5638155 prefixEnd_5638155 2895083519550493426333103 := by
  unfold tailWord_5638155
  simp only [CollatzResearch.WordTrace]
  refine ⟨205640406888934830057115919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137093604592623220038077279 205640406888934830057115919)
  ·
    refine ⟨308460610333402245085673879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205640406888934830057115919 308460610333402245085673879)
    ·
      refine ⟨462690915500103367628510819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308460610333402245085673879 462690915500103367628510819)
      ·
        refine ⟨694036373250155051442766229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462690915500103367628510819 694036373250155051442766229)
        ·
          refine ⟨32532954996101018036379667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 694036373250155051442766229 32532954996101018036379667)
          ·
            refine ⟨48799432494151527054569501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32532954996101018036379667 48799432494151527054569501)
            ·
              refine ⟨18299787185306822645463563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48799432494151527054569501 18299787185306822645463563)
              ·
                refine ⟨27449680777960233968195345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18299787185306822645463563 27449680777960233968195345)
                ·
                  refine ⟨20587260583470175476146509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27449680777960233968195345 20587260583470175476146509)
                  ·
                    refine ⟨7720222718801315803554941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20587260583470175476146509 7720222718801315803554941)
                    ·
                      refine ⟨2895083519550493426333103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720222718801315803554941 2895083519550493426333103)
                      ·
                        rfl

theorem cell23_5638155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 3].length) (baseStart_5638155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638155 prefixEnd_5638155 := by exact prefixLift 5638155
  have htrace : WordTrace (prefixWord ++ tailWord_5638155) baseStart_5638155 baseEnd_5638155 := by
    simpa [prefixWord, tailWord_5638155, baseEnd_5638155] using wordTrace_append hprefix tailTrace_5638155
  have hstable : (prefixWord ++ tailWord_5638155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638155).length < 2 ^ (prefixWord ++ tailWord_5638155).sum := by decide
  have hdescent : baseEnd_5638155 < baseStart_5638155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638195 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 4]
def baseStart_5638195 : Nat := 118140960795 + 5638195 * 2 ^ 59
def prefixEnd_5638195 : Nat := 4983230072969 + 3 ^ 40 * 5638195 * 2
def baseEnd_5638195 : Nat := 2895104058776673269832919

theorem tailTrace_5638195 : CollatzResearch.WordTrace tailWord_5638195 prefixEnd_5638195 2895104058776673269832919 := by
  unfold tailWord_5638195
  simp only [CollatzResearch.WordTrace]
  refine ⟨205641865808789916888572039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137094577205859944592381359 205641865808789916888572039)
  ·
    refine ⟨308462798713184875332858059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205641865808789916888572039 308462798713184875332858059)
    ·
      refine ⟨462694198069777312999287089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308462798713184875332858059 462694198069777312999287089)
      ·
        refine ⟨347020648552332984749465317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462694198069777312999287089 347020648552332984749465317)
        ·
          refine ⟨65066371603562434640524747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347020648552332984749465317 65066371603562434640524747)
          ·
            refine ⟨97599557405343651960787121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65066371603562434640524747 97599557405343651960787121)
            ·
              refine ⟨73199668054007738970590341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97599557405343651960787121 73199668054007738970590341)
              ·
                refine ⟨13724937760126451056985689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73199668054007738970590341 13724937760126451056985689)
                ·
                  refine ⟨10293703320094838292739267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13724937760126451056985689 10293703320094838292739267)
                  ·
                    refine ⟨15440554980142257439108901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10293703320094838292739267 15440554980142257439108901)
                    ·
                      refine ⟨2895104058776673269832919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15440554980142257439108901 2895104058776673269832919)
                      ·
                        rfl

theorem cell23_5638195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_5638195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638195 prefixEnd_5638195 := by exact prefixLift 5638195
  have htrace : WordTrace (prefixWord ++ tailWord_5638195) baseStart_5638195 baseEnd_5638195 := by
    simpa [prefixWord, tailWord_5638195, baseEnd_5638195] using wordTrace_append hprefix tailTrace_5638195
  have hstable : (prefixWord ++ tailWord_5638195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638195).length < 2 ^ (prefixWord ++ tailWord_5638195).sum := by decide
  have hdescent : baseEnd_5638195 < baseStart_5638195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638215 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_5638215 : Nat := 118140960795 + 5638215 * 2 ^ 59
def prefixEnd_5638215 : Nat := 4983230072969 + 3 ^ 40 * 5638215 * 2
def baseEnd_5638215 : Nat := 2895114328389763191582827

theorem tailTrace_5638215 : CollatzResearch.WordTrace tailWord_5638215 prefixEnd_5638215 2895114328389763191582827 := by
  unfold tailWord_5638215
  simp only [CollatzResearch.WordTrace]
  refine ⟨205642595268717460304300099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137095063512478306869533399 205642595268717460304300099)
  ·
    refine ⟨308463892903076190456450149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205642595268717460304300099 308463892903076190456450149)
    ·
      refine ⟨57836979919326785710584403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308463892903076190456450149 57836979919326785710584403)
      ·
        refine ⟨86755469878990178565876605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57836979919326785710584403 86755469878990178565876605)
        ·
          refine ⟨32533301204621316962203727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86755469878990178565876605 32533301204621316962203727)
          ·
            refine ⟨48799951806931975443305591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32533301204621316962203727 48799951806931975443305591)
            ·
              refine ⟨73199927710397963164958387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48799951806931975443305591 73199927710397963164958387)
              ·
                refine ⟨109799891565596944747437581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73199927710397963164958387 109799891565596944747437581)
                ·
                  refine ⟨41174959337098854280289093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109799891565596944747437581 41174959337098854280289093)
                  ·
                    refine ⟨7720304875706035177554205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41174959337098854280289093 7720304875706035177554205)
                    ·
                      refine ⟨2895114328389763191582827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720304875706035177554205 2895114328389763191582827)
                      ·
                        rfl

theorem cell23_5638215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_5638215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638215 prefixEnd_5638215 := by exact prefixLift 5638215
  have htrace : WordTrace (prefixWord ++ tailWord_5638215) baseStart_5638215 baseEnd_5638215 := by
    simpa [prefixWord, tailWord_5638215, baseEnd_5638215] using wordTrace_append hprefix tailTrace_5638215
  have hstable : (prefixWord ++ tailWord_5638215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638215).length < 2 ^ (prefixWord ++ tailWord_5638215).sum := by decide
  have hdescent : baseEnd_5638215 < baseStart_5638215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638222 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_5638222 : Nat := 118140960795 + 5638222 * 2 ^ 59
def prefixEnd_5638222 : Nat := 4983230072969 + 3 ^ 40 * 5638222 * 2
def baseEnd_5638222 : Nat := 965039307584781554731765

theorem tailTrace_5638222 : CollatzResearch.WordTrace tailWord_5638222 prefixEnd_5638222 965039307584781554731765 := by
  unfold tailWord_5638222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25705356322461512562475615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137095233719794733666536613 25705356322461512562475615)
  ·
    refine ⟨38558034483692268843713423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25705356322461512562475615 38558034483692268843713423)
    ·
      refine ⟨57837051725538403265570135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38558034483692268843713423 57837051725538403265570135)
      ·
        refine ⟨86755577588307604898355203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57837051725538403265570135 86755577588307604898355203)
        ·
          refine ⟨130133366382461407347532805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86755577588307604898355203 130133366382461407347532805)
          ·
            refine ⟨24400006196711513877662401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130133366382461407347532805 24400006196711513877662401)
            ·
              refine ⟨18300004647533635408246801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24400006196711513877662401 18300004647533635408246801)
              ·
                refine ⟨13725003485650226556185101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18300004647533635408246801 13725003485650226556185101)
                ·
                  refine ⟨5146876307118834958569413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13725003485650226556185101 5146876307118834958569413)
                  ·
                    refine ⟨965039307584781554731765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5146876307118834958569413 965039307584781554731765)
                    ·
                      rfl

theorem cell23_5638222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_5638222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638222 prefixEnd_5638222 := by exact prefixLift 5638222
  have htrace : WordTrace (prefixWord ++ tailWord_5638222) baseStart_5638222 baseEnd_5638222 := by
    simpa [prefixWord, tailWord_5638222, baseEnd_5638222] using wordTrace_append hprefix tailTrace_5638222
  have hstable : (prefixWord ++ tailWord_5638222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638222).length < 2 ^ (prefixWord ++ tailWord_5638222).sum := by decide
  have hdescent : baseEnd_5638222 < baseStart_5638222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638256 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 1, 4]
def baseStart_5638256 : Nat := 118140960795 + 5638256 * 2 ^ 59
def prefixEnd_5638256 : Nat := 4983230072969 + 3 ^ 40 * 5638256 * 2
def baseEnd_5638256 : Nat := 965045127032199177056713

theorem tailTrace_5638256 : CollatzResearch.WordTrace tailWord_5638256 prefixEnd_5638256 965045127032199177056713 := by
  unfold tailWord_5638256
  simp only [CollatzResearch.WordTrace]
  refine ⟨102822045330784462153271311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137096060441045949537695081 102822045330784462153271311)
  ·
    refine ⟨154233067996176693229906967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102822045330784462153271311 154233067996176693229906967)
    ·
      refine ⟨231349601994265039844860451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154233067996176693229906967 231349601994265039844860451)
      ·
        refine ⟨347024402991397559767290677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231349601994265039844860451 347024402991397559767290677)
        ·
          refine ⟨32533537780443521228183501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 347024402991397559767290677 32533537780443521228183501)
          ·
            refine ⟨12200076667666320460568813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32533537780443521228183501 12200076667666320460568813)
            ·
              refine ⟨4575028750374870172713305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12200076667666320460568813 4575028750374870172713305)
              ·
                refine ⟨3431271562781152629534979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4575028750374870172713305 3431271562781152629534979)
                ·
                  refine ⟨5146907344171728944302469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431271562781152629534979 5146907344171728944302469)
                  ·
                    refine ⟨965045127032199177056713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5146907344171728944302469 965045127032199177056713)
                    ·
                      rfl

theorem cell23_5638256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 4].length) (baseStart_5638256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638256 prefixEnd_5638256 := by exact prefixLift 5638256
  have htrace : WordTrace (prefixWord ++ tailWord_5638256) baseStart_5638256 baseEnd_5638256 := by
    simpa [prefixWord, tailWord_5638256, baseEnd_5638256] using wordTrace_append hprefix tailTrace_5638256
  have hstable : (prefixWord ++ tailWord_5638256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638256).length < 2 ^ (prefixWord ++ tailWord_5638256).sum := by decide
  have hdescent : baseEnd_5638256 < baseStart_5638256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638269 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 6]
def baseStart_5638269 : Nat := 118140960795 + 5638269 * 2 ^ 59
def prefixEnd_5638269 : Nat := 4983230072969 + 3 ^ 40 * 5638269 * 2
def baseEnd_5638269 : Nat := 321682450705011775589731

theorem tailTrace_5638269 : CollatzResearch.WordTrace tailWord_5638269 prefixEnd_5638269 321682450705011775589731 := by
  unfold tailWord_5638269
  simp only [CollatzResearch.WordTrace]
  refine ⟨205644564810521827526765861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137096376540347885017843907 205644564810521827526765861)
  ·
    refine ⟨38558355901972842661268599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205644564810521827526765861 38558355901972842661268599)
    ·
      refine ⟨57837533852959263991902899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38558355901972842661268599 57837533852959263991902899)
      ·
        refine ⟨86756300779438895987854349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57837533852959263991902899 86756300779438895987854349)
        ·
          refine ⟨32533612792289585995445381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86756300779438895987854349 32533612792289585995445381)
          ·
            refine ⟨6100052398554297374146009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32533612792289585995445381 6100052398554297374146009)
            ·
              refine ⟨4575039298915723030609507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6100052398554297374146009 4575039298915723030609507)
              ·
                refine ⟨6862558948373584545914261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575039298915723030609507 6862558948373584545914261)
                ·
                  refine ⟨321682450705011775589731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6862558948373584545914261 321682450705011775589731)
                  ·
                    rfl

theorem cell23_5638269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_5638269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638269 prefixEnd_5638269 := by exact prefixLift 5638269
  have htrace : WordTrace (prefixWord ++ tailWord_5638269) baseStart_5638269 baseEnd_5638269 := by
    simpa [prefixWord, tailWord_5638269, baseEnd_5638269] using wordTrace_append hprefix tailTrace_5638269
  have hstable : (prefixWord ++ tailWord_5638269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638269).length < 2 ^ (prefixWord ++ tailWord_5638269).sum := by decide
  have hdescent : baseEnd_5638269 < baseStart_5638269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638272 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 6, 3, 2]
def baseStart_5638272 : Nat := 118140960795 + 5638272 * 2 ^ 59
def prefixEnd_5638272 : Nat := 4983230072969 + 3 ^ 40 * 5638272 * 2
def baseEnd_5638272 : Nat := 2895143596787069468570065

theorem tailTrace_5638272 : CollatzResearch.WordTrace tailWord_5638272 prefixEnd_5638272 2895143596787069468570065 := by
  unfold tailWord_5638272
  simp only [CollatzResearch.WordTrace]
  refine ⟨102822337114755479519562535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137096449486340639359416713 102822337114755479519562535)
  ·
    refine ⟨154233505672133219279343803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102822337114755479519562535 154233505672133219279343803)
    ·
      refine ⟨231350258508199828919015705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154233505672133219279343803 231350258508199828919015705)
      ·
        refine ⟨173512693881149871689261779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231350258508199828919015705 173512693881149871689261779)
        ·
          refine ⟨260269040821724807533892669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173512693881149871689261779 260269040821724807533892669)
          ·
            refine ⟨97600890308146802825209751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260269040821724807533892669 97600890308146802825209751)
            ·
              refine ⟨146401335462220204237814627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97600890308146802825209751 146401335462220204237814627)
              ·
                refine ⟨219602003193330306356721941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146401335462220204237814627 219602003193330306356721941)
                ·
                  refine ⟨10293843899687358110471341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219602003193330306356721941 10293843899687358110471341)
                  ·
                    refine ⟨3860191462382759291426753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10293843899687358110471341 3860191462382759291426753)
                    ·
                      refine ⟨2895143596787069468570065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860191462382759291426753 2895143596787069468570065)
                      ·
                        rfl

theorem cell23_5638272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_5638272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638272 prefixEnd_5638272 := by exact prefixLift 5638272
  have htrace : WordTrace (prefixWord ++ tailWord_5638272) baseStart_5638272 baseEnd_5638272 := by
    simpa [prefixWord, tailWord_5638272, baseEnd_5638272] using wordTrace_append hprefix tailTrace_5638272
  have hstable : (prefixWord ++ tailWord_5638272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638272).length < 2 ^ (prefixWord ++ tailWord_5638272).sum := by decide
  have hdescent : baseEnd_5638272 < baseStart_5638272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638282 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_5638282 : Nat := 118140960795 + 5638282 * 2 ^ 59
def prefixEnd_5638282 : Nat := 4983230072969 + 3 ^ 40 * 5638282 * 2
def baseEnd_5638282 : Nat := 965049577197871476481673

theorem tailTrace_5638282 : CollatzResearch.WordTrace tailWord_5638282 prefixEnd_5638282 965049577197871476481673 := by
  unfold tailWord_5638282
  simp only [CollatzResearch.WordTrace]
  refine ⟨51411259739868682686747275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137096692639649820497992733 51411259739868682686747275)
  ·
    refine ⟨77116889609803024030120913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51411259739868682686747275 77116889609803024030120913)
    ·
      refine ⟨57837667207352268022590685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77116889609803024030120913 57837667207352268022590685)
      ·
        refine ⟨21689125202757100508471507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57837667207352268022590685 21689125202757100508471507)
        ·
          refine ⟨32533687804135650762707261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21689125202757100508471507 32533687804135650762707261)
          ·
            refine ⟨12200132926550869036015223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32533687804135650762707261 12200132926550869036015223)
            ·
              refine ⟨18300199389826303554022835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12200132926550869036015223 18300199389826303554022835)
              ·
                refine ⟨27450299084739455331034253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18300199389826303554022835 27450299084739455331034253)
                ·
                  refine ⟨10293862156777295749137845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27450299084739455331034253 10293862156777295749137845)
                  ·
                    refine ⟨965049577197871476481673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10293862156777295749137845 965049577197871476481673)
                    ·
                      rfl

theorem cell23_5638282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_5638282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638282 prefixEnd_5638282 := by exact prefixLift 5638282
  have htrace : WordTrace (prefixWord ++ tailWord_5638282) baseStart_5638282 baseEnd_5638282 := by
    simpa [prefixWord, tailWord_5638282, baseEnd_5638282] using wordTrace_append hprefix tailTrace_5638282
  have hstable : (prefixWord ++ tailWord_5638282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638282).length < 2 ^ (prefixWord ++ tailWord_5638282).sum := by decide
  have hdescent : baseEnd_5638282 < baseStart_5638282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638306 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5638306 : Nat := 118140960795 + 5638306 * 2 ^ 59
def prefixEnd_5638306 : Nat := 4983230072969 + 3 ^ 40 * 5638306 * 2
def baseEnd_5638306 : Nat := 2895161055129322335544909

theorem tailTrace_5638306 : CollatzResearch.WordTrace tailWord_5638306 prefixEnd_5638306 2895161055129322335544909 := by
  unfold tailWord_5638306
  simp only [CollatzResearch.WordTrace]
  refine ⟨51411478577846945711465693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137097276207591855230575181 51411478577846945711465693)
  ·
    refine ⟨19279304466692604641799635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51411478577846945711465693 19279304466692604641799635)
    ·
      refine ⟨28918956700038906962699453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19279304466692604641799635 28918956700038906962699453)
      ·
        refine ⟨10844608762514590111012295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28918956700038906962699453 10844608762514590111012295)
        ·
          refine ⟨16266913143771885166518443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844608762514590111012295 16266913143771885166518443)
          ·
            refine ⟨24400369715657827749777665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16266913143771885166518443 24400369715657827749777665)
            ·
              refine ⟨18300277286743370812333249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24400369715657827749777665 18300277286743370812333249)
              ·
                refine ⟨13725207965057528109249937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18300277286743370812333249 13725207965057528109249937)
                ·
                  refine ⟨10293905973793146081937453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13725207965057528109249937 10293905973793146081937453)
                  ·
                    refine ⟨3860214740172429780726545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10293905973793146081937453 3860214740172429780726545)
                    ·
                      refine ⟨2895161055129322335544909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860214740172429780726545 2895161055129322335544909)
                      ·
                        rfl

theorem cell23_5638306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5638306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638306 prefixEnd_5638306 := by exact prefixLift 5638306
  have htrace : WordTrace (prefixWord ++ tailWord_5638306) baseStart_5638306 baseEnd_5638306 := by
    simpa [prefixWord, tailWord_5638306, baseEnd_5638306] using wordTrace_append hprefix tailTrace_5638306
  have hstable : (prefixWord ++ tailWord_5638306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638306).length < 2 ^ (prefixWord ++ tailWord_5638306).sum := by decide
  have hdescent : baseEnd_5638306 < baseStart_5638306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638319 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 3, 2, 2]
def baseStart_5638319 : Nat := 118140960795 + 5638319 * 2 ^ 59
def prefixEnd_5638319 : Nat := 4983230072969 + 3 ^ 40 * 5638319 * 2
def baseEnd_5638319 : Nat := 2895167730377830784682349

theorem tailTrace_5638319 : CollatzResearch.WordTrace tailWord_5638319 prefixEnd_5638319 2895167730377830784682349 := by
  unfold tailWord_5638319
  simp only [CollatzResearch.WordTrace]
  refine ⟨205646388460340686066086011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137097592306893790710724007 205646388460340686066086011)
  ·
    refine ⟨308469582690511029099129017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205646388460340686066086011 308469582690511029099129017)
    ·
      refine ⟨231352187017883271824346763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308469582690511029099129017 231352187017883271824346763)
      ·
        refine ⟨347028280526824907736520145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231352187017883271824346763 347028280526824907736520145)
        ·
          refine ⟨260271210395118680802390109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347028280526824907736520145 260271210395118680802390109)
          ·
            refine ⟨97601703898169505300896291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260271210395118680802390109 97601703898169505300896291)
            ·
              refine ⟨146402555847254257951344437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97601703898169505300896291 146402555847254257951344437)
              ·
                refine ⟨13725239610680086682938541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146402555847254257951344437 13725239610680086682938541)
                ·
                  refine ⟨5146964854005032506101953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13725239610680086682938541 5146964854005032506101953)
                  ·
                    refine ⟨3860223640503774379576465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146964854005032506101953 3860223640503774379576465)
                    ·
                      refine ⟨2895167730377830784682349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860223640503774379576465 2895167730377830784682349)
                      ·
                        rfl

theorem cell23_5638319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 2, 2].length) (baseStart_5638319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638319 prefixEnd_5638319 := by exact prefixLift 5638319
  have htrace : WordTrace (prefixWord ++ tailWord_5638319) baseStart_5638319 baseEnd_5638319 := by
    simpa [prefixWord, tailWord_5638319, baseEnd_5638319] using wordTrace_append hprefix tailTrace_5638319
  have hstable : (prefixWord ++ tailWord_5638319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638319).length < 2 ^ (prefixWord ++ tailWord_5638319).sum := by decide
  have hdescent : baseEnd_5638319 < baseStart_5638319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638322 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_5638322 : Nat := 118140960795 + 5638322 * 2 ^ 59
def prefixEnd_5638322 : Nat := 4983230072969 + 3 ^ 40 * 5638322 * 2
def baseEnd_5638322 : Nat := 2895169270819794272944835

theorem tailTrace_5638322 : CollatzResearch.WordTrace tailWord_5638322 prefixEnd_5638322 2895169270819794272944835 := by
  unfold tailWord_5638322
  simp only [CollatzResearch.WordTrace]
  refine ⟨51411624469832454394611305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137097665252886545052296813 51411624469832454394611305)
  ·
    refine ⟨38558718352374340795958479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51411624469832454394611305 38558718352374340795958479)
    ·
      refine ⟨57838077528561511193937719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38558718352374340795958479 57838077528561511193937719)
      ·
        refine ⟨86757116292842266790906579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57838077528561511193937719 86757116292842266790906579)
        ·
          refine ⟨130135674439263400186359869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86757116292842266790906579 130135674439263400186359869)
          ·
            refine ⟨48800877914723775069884951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130135674439263400186359869 48800877914723775069884951)
            ·
              refine ⟨73201316872085662604827427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48800877914723775069884951 73201316872085662604827427)
              ·
                refine ⟨109801975308128493907241141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73201316872085662604827427 109801975308128493907241141)
                ·
                  refine ⟨10293935185137046303803857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109801975308128493907241141 10293935185137046303803857)
                  ·
                    refine ⟨7720451388852784727852893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10293935185137046303803857 7720451388852784727852893)
                    ·
                      refine ⟨2895169270819794272944835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720451388852784727852893 2895169270819794272944835)
                      ·
                        rfl

theorem cell23_5638322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_5638322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638322 prefixEnd_5638322 := by exact prefixLift 5638322
  have htrace : WordTrace (prefixWord ++ tailWord_5638322) baseStart_5638322 baseEnd_5638322 := by
    simpa [prefixWord, tailWord_5638322, baseEnd_5638322] using wordTrace_append hprefix tailTrace_5638322
  have hstable : (prefixWord ++ tailWord_5638322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638322).length < 2 ^ (prefixWord ++ tailWord_5638322).sum := by decide
  have hdescent : baseEnd_5638322 < baseStart_5638322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638336 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 3, 2, 2]
def baseStart_5638336 : Nat := 118140960795 + 5638336 * 2 ^ 59
def prefixEnd_5638336 : Nat := 4983230072969 + 3 ^ 40 * 5638336 * 2
def baseEnd_5638336 : Nat := 2895176459548957218169771

theorem tailTrace_5638336 : CollatzResearch.WordTrace tailWord_5638336 prefixEnd_5638336 2895176459548957218169771 := by
  unfold tailWord_5638336
  simp only [CollatzResearch.WordTrace]
  refine ⟨102823504250639548984727431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137098005667519398646303241 102823504250639548984727431)
  ·
    refine ⟨154235256375959323477091147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102823504250639548984727431 154235256375959323477091147)
    ·
      refine ⟨231352884563938985215636721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154235256375959323477091147 231352884563938985215636721)
      ·
        refine ⟨173514663422954238911727541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231352884563938985215636721 173514663422954238911727541)
        ·
          refine ⟨16266999695901959897974457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173514663422954238911727541 16266999695901959897974457)
          ·
            refine ⟨12200249771926469923480843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16266999695901959897974457 12200249771926469923480843)
            ·
              refine ⟨18300374657889704885221265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12200249771926469923480843 18300374657889704885221265)
              ·
                refine ⟨13725280993417278663915949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18300374657889704885221265 13725280993417278663915949)
                ·
                  refine ⟨5146980372531479498968481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13725280993417278663915949 5146980372531479498968481)
                  ·
                    refine ⟨3860235279398609624226361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146980372531479498968481 3860235279398609624226361)
                    ·
                      refine ⟨2895176459548957218169771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860235279398609624226361 2895176459548957218169771)
                      ·
                        rfl

theorem cell23_5638336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_5638336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638336 prefixEnd_5638336 := by exact prefixLift 5638336
  have htrace : WordTrace (prefixWord ++ tailWord_5638336) baseStart_5638336 baseEnd_5638336 := by
    simpa [prefixWord, tailWord_5638336, baseEnd_5638336] using wordTrace_append hprefix tailTrace_5638336
  have hstable : (prefixWord ++ tailWord_5638336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638336).length < 2 ^ (prefixWord ++ tailWord_5638336).sum := by decide
  have hdescent : baseEnd_5638336 < baseStart_5638336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638369 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_5638369 : Nat := 118140960795 + 5638369 * 2 ^ 59
def prefixEnd_5638369 : Nat := 4983230072969 + 3 ^ 40 * 5638369 * 2
def baseEnd_5638369 : Nat := 2895193404410555589057119

theorem tailTrace_5638369 : CollatzResearch.WordTrace tailWord_5638369 prefixEnd_5638369 2895193404410555589057119 := by
  unfold tailWord_5638369
  simp only [CollatzResearch.WordTrace]
  refine ⟨205648212110159544605406161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137098808073439696403604107 205648212110159544605406161)
  ·
    refine ⟨154236159082619658454054621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205648212110159544605406161 154236159082619658454054621)
    ·
      refine ⟨57838559655982371920270483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154236159082619658454054621 57838559655982371920270483)
      ·
        refine ⟨86757839483973557880405725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57838559655982371920270483 86757839483973557880405725)
        ·
          refine ⟨32534189806490084205152147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86757839483973557880405725 32534189806490084205152147)
          ·
            refine ⟨48801284709735126307728221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32534189806490084205152147 48801284709735126307728221)
            ·
              refine ⟨18300481766150672365398083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48801284709735126307728221 18300481766150672365398083)
              ·
                refine ⟨27450722649226008548097125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18300481766150672365398083 27450722649226008548097125)
                ·
                  refine ⟨5147010496729876602768211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27450722649226008548097125 5147010496729876602768211)
                  ·
                    refine ⟨7720515745094814904152317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5147010496729876602768211 7720515745094814904152317)
                    ·
                      refine ⟨2895193404410555589057119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720515745094814904152317 2895193404410555589057119)
                      ·
                        rfl

theorem cell23_5638369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_5638369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638369 prefixEnd_5638369 := by exact prefixLift 5638369
  have htrace : WordTrace (prefixWord ++ tailWord_5638369) baseStart_5638369 baseEnd_5638369 := by
    simpa [prefixWord, tailWord_5638369, baseEnd_5638369] using wordTrace_append hprefix tailTrace_5638369
  have hstable : (prefixWord ++ tailWord_5638369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638369).length < 2 ^ (prefixWord ++ tailWord_5638369).sum := by decide
  have hdescent : baseEnd_5638369 < baseStart_5638369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638386 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_5638386 : Nat := 118140960795 + 5638386 * 2 ^ 59
def prefixEnd_5638386 : Nat := 4983230072969 + 3 ^ 40 * 5638386 * 2
def baseEnd_5638386 : Nat := 2895202133581682022544541

theorem tailTrace_5638386 : CollatzResearch.WordTrace tailWord_5638386 prefixEnd_5638386 2895202133581682022544541 := by
  unfold tailWord_5638386
  simp only [CollatzResearch.WordTrace]
  refine ⟨51412208037774489127193753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137099221434065304339183341 51412208037774489127193753)
  ·
    refine ⟨38559156028330866845395315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51412208037774489127193753 38559156028330866845395315)
    ·
      refine ⟨57838734042496300268092973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38559156028330866845395315 57838734042496300268092973)
      ·
        refine ⟨21689525265936112600534865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57838734042496300268092973 21689525265936112600534865)
        ·
          refine ⟨16267143949452084450401149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21689525265936112600534865 16267143949452084450401149)
          ·
            refine ⟨6100178981044531668900431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16267143949452084450401149 6100178981044531668900431)
            ·
              refine ⟨9150268471566797503350647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100178981044531668900431 9150268471566797503350647)
              ·
                refine ⟨13725402707350196255025971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150268471566797503350647 13725402707350196255025971)
                ·
                  refine ⟨20588104061025294382538957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13725402707350196255025971 20588104061025294382538957)
                  ·
                    refine ⟨7720539022884485393452109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20588104061025294382538957 7720539022884485393452109)
                    ·
                      refine ⟨2895202133581682022544541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720539022884485393452109 2895202133581682022544541)
                      ·
                        rfl

theorem cell23_5638386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_5638386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638386 prefixEnd_5638386 := by exact prefixLift 5638386
  have htrace : WordTrace (prefixWord ++ tailWord_5638386) baseStart_5638386 baseEnd_5638386 := by
    simpa [prefixWord, tailWord_5638386, baseEnd_5638386] using wordTrace_append hprefix tailTrace_5638386
  have hstable : (prefixWord ++ tailWord_5638386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638386).length < 2 ^ (prefixWord ++ tailWord_5638386).sum := by decide
  have hdescent : baseEnd_5638386 < baseStart_5638386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638395 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_5638395 : Nat := 118140960795 + 5638395 * 2 ^ 59
def prefixEnd_5638395 : Nat := 4983230072969 + 3 ^ 40 * 5638395 * 2
def baseEnd_5638395 : Nat := 2895206754907572487331999

theorem tailTrace_5638395 : CollatzResearch.WordTrace tailWord_5638395 prefixEnd_5638395 2895206754907572487331999 := by
  unfold tailWord_5638395
  simp only [CollatzResearch.WordTrace]
  refine ⟨205649160408065351045852639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137099440272043567363901759 205649160408065351045852639)
  ·
    refine ⟨308473740612098026568778959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205649160408065351045852639 308473740612098026568778959)
    ·
      refine ⟨462710610918147039853168439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308473740612098026568778959 462710610918147039853168439)
      ·
        refine ⟨694065916377220559779752659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462710610918147039853168439 694065916377220559779752659)
        ·
          refine ⟨1041098874565830839669628989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694065916377220559779752659 1041098874565830839669628989)
          ·
            refine ⟨390412077962186564876110871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1041098874565830839669628989 390412077962186564876110871)
            ·
              refine ⟨585618116943279847314166307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390412077962186564876110871 585618116943279847314166307)
              ·
                refine ⟨878427175414919770971249461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585618116943279847314166307 878427175414919770971249461)
                ·
                  refine ⟨82352547695148728528554637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 878427175414919770971249461 82352547695148728528554637)
                  ·
                    refine ⟨30882205385680773198207989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82352547695148728528554637 30882205385680773198207989)
                    ·
                      refine ⟨2895206754907572487331999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30882205385680773198207989 2895206754907572487331999)
                      ·
                        rfl

theorem cell23_5638395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_5638395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638395 prefixEnd_5638395 := by exact prefixLift 5638395
  have htrace : WordTrace (prefixWord ++ tailWord_5638395) baseStart_5638395 baseEnd_5638395 := by
    simpa [prefixWord, tailWord_5638395, baseEnd_5638395] using wordTrace_append hprefix tailTrace_5638395
  have hstable : (prefixWord ++ tailWord_5638395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638395).length < 2 ^ (prefixWord ++ tailWord_5638395).sum := by decide
  have hdescent : baseEnd_5638395 < baseStart_5638395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638396 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_5638396 : Nat := 118140960795 + 5638396 * 2 ^ 59
def prefixEnd_5638396 : Nat := 4983230072969 + 3 ^ 40 * 5638396 * 2
def baseEnd_5638396 : Nat := 2895207268388226983419495

theorem tailTrace_5638396 : CollatzResearch.WordTrace tailWord_5638396 prefixEnd_5638396 2895207268388226983419495 := by
  unfold tailWord_5638396
  simp only [CollatzResearch.WordTrace]
  refine ⟨102824598440530864108319521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137099464587374485477759361 102824598440530864108319521)
  ·
    refine ⟨77118448830398148081239641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102824598440530864108319521 77118448830398148081239641)
    ·
      refine ⟨57838836622798611060929731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77118448830398148081239641 57838836622798611060929731)
      ·
        refine ⟨86758254934197916591394597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57838836622798611060929731 86758254934197916591394597)
        ·
          refine ⟨16267172800162109360886487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86758254934197916591394597 16267172800162109360886487)
          ·
            refine ⟨24400759200243164041329731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16267172800162109360886487 24400759200243164041329731)
            ·
              refine ⟨36601138800364746061994597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24400759200243164041329731 36601138800364746061994597)
              ·
                refine ⟨6862713525068389886623987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36601138800364746061994597 6862713525068389886623987)
                ·
                  refine ⟨10294070287602584829935981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862713525068389886623987 10294070287602584829935981)
                  ·
                    refine ⟨3860276357850969311225993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10294070287602584829935981 3860276357850969311225993)
                    ·
                      refine ⟨2895207268388226983419495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860276357850969311225993 2895207268388226983419495)
                      ·
                        rfl

theorem cell23_5638396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_5638396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638396 prefixEnd_5638396 := by exact prefixLift 5638396
  have htrace : WordTrace (prefixWord ++ tailWord_5638396) baseStart_5638396 baseEnd_5638396 := by
    simpa [prefixWord, tailWord_5638396, baseEnd_5638396] using wordTrace_append hprefix tailTrace_5638396
  have hstable : (prefixWord ++ tailWord_5638396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638396).length < 2 ^ (prefixWord ++ tailWord_5638396).sum := by decide
  have hdescent : baseEnd_5638396 < baseStart_5638396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638412 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5638412 : Nat := 118140960795 + 5638412 * 2 ^ 59
def prefixEnd_5638412 : Nat := 4983230072969 + 3 ^ 40 * 5638412 * 2
def baseEnd_5638412 : Nat := 2895215484078698920819421

theorem tailTrace_5638412 : CollatzResearch.WordTrace tailWord_5638412 prefixEnd_5638412 2895215484078698920819421 := by
  unfold tailWord_5638412
  simp only [CollatzResearch.WordTrace]
  refine ⟨102824890224501881474610745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137099853632669175299480993 102824890224501881474610745)
  ·
    refine ⟨77118667668376411105958059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102824890224501881474610745 77118667668376411105958059)
    ·
      refine ⟨115678001502564616658937089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77118667668376411105958059 115678001502564616658937089)
      ·
        refine ⟨86758501126923462494202817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115678001502564616658937089 86758501126923462494202817)
        ·
          refine ⟨65068875845192596870652113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86758501126923462494202817 65068875845192596870652113)
          ·
            refine ⟨48801656883894447652989085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65068875845192596870652113 48801656883894447652989085)
            ·
              refine ⟨18300621331460417869870907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48801656883894447652989085 18300621331460417869870907)
              ·
                refine ⟨27450931997190626804806361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18300621331460417869870907 27450931997190626804806361)
                ·
                  refine ⟨20588198997892970103604771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27450931997190626804806361 20588198997892970103604771)
                  ·
                    refine ⟨30882298496839455155407157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20588198997892970103604771 30882298496839455155407157)
                    ·
                      refine ⟨2895215484078698920819421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30882298496839455155407157 2895215484078698920819421)
                      ·
                        rfl

theorem cell23_5638412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5638412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638412 prefixEnd_5638412 := by exact prefixLift 5638412
  have htrace : WordTrace (prefixWord ++ tailWord_5638412) baseStart_5638412 baseEnd_5638412 := by
    simpa [prefixWord, tailWord_5638412, baseEnd_5638412] using wordTrace_append hprefix tailTrace_5638412
  have hstable : (prefixWord ++ tailWord_5638412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638412).length < 2 ^ (prefixWord ++ tailWord_5638412).sum := by decide
  have hdescent : baseEnd_5638412 < baseStart_5638412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638415 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 9]
def baseStart_5638415 : Nat := 118140960795 + 5638415 * 2 ^ 59
def prefixEnd_5638415 : Nat := 4983230072969 + 3 ^ 40 * 5638415 * 2
def baseEnd_5638415 : Nat := 321690780502295823231323

theorem tailTrace_5638415 : CollatzResearch.WordTrace tailWord_5638415 prefixEnd_5638415 321690780502295823231323 := by
  unfold tailWord_5638415
  simp only [CollatzResearch.WordTrace]
  refine ⟨205649889867992894461580699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137099926578661929641053799 205649889867992894461580699)
  ·
    refine ⟨308474834801989341692371049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205649889867992894461580699 308474834801989341692371049)
    ·
      refine ⟨231356126101492006269278287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308474834801989341692371049 231356126101492006269278287)
      ·
        refine ⟨347034189152238009403917431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231356126101492006269278287 347034189152238009403917431)
        ·
          refine ⟨520551283728357014105876147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347034189152238009403917431 520551283728357014105876147)
          ·
            refine ⟨780826925592535521158814221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520551283728357014105876147 780826925592535521158814221)
            ·
              refine ⟨292810097097200820434555333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780826925592535521158814221 292810097097200820434555333)
              ·
                refine ⟨54901893205725153831479125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292810097097200820434555333 54901893205725153831479125)
                ·
                  refine ⟨321690780502295823231323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54901893205725153831479125 321690780502295823231323)
                  ·
                    rfl

theorem cell23_5638415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 9].length) (baseStart_5638415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638415 prefixEnd_5638415 := by exact prefixLift 5638415
  have htrace : WordTrace (prefixWord ++ tailWord_5638415) baseStart_5638415 baseEnd_5638415 := by
    simpa [prefixWord, tailWord_5638415, baseEnd_5638415] using wordTrace_append hprefix tailTrace_5638415
  have hstable : (prefixWord ++ tailWord_5638415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638415).length < 2 ^ (prefixWord ++ tailWord_5638415).sum := by decide
  have hdescent : baseEnd_5638415 < baseStart_5638415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638472 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_5638472 : Nat := 118140960795 + 5638472 * 2 ^ 59
def prefixEnd_5638472 : Nat := 4983230072969 + 3 ^ 40 * 5638472 * 2
def baseEnd_5638472 : Nat := 2895246292917968686069145

theorem tailTrace_5638472 : CollatzResearch.WordTrace tailWord_5638472 prefixEnd_5638472 2895246292917968686069145 := by
  unfold tailWord_5638472
  simp only [CollatzResearch.WordTrace]
  refine ⟨102825984414393196598202835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137101312552524262130937113 102825984414393196598202835)
  ·
    refine ⟨154238976621589794897304253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102825984414393196598202835 154238976621589794897304253)
    ·
      refine ⟨57839616233096173086489095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154238976621589794897304253 57839616233096173086489095)
      ·
        refine ⟨86759424349644259629733643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57839616233096173086489095 86759424349644259629733643)
        ·
          refine ⟨130139136524466389444600465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86759424349644259629733643 130139136524466389444600465)
          ·
            refine ⟨97604352393349792083450349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130139136524466389444600465 97604352393349792083450349)
            ·
              refine ⟨36601632147506172031293881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97604352393349792083450349 36601632147506172031293881)
              ·
                refine ⟨27451224110629629023470411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36601632147506172031293881 27451224110629629023470411)
                ·
                  refine ⟨41176836165944443535205617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27451224110629629023470411 41176836165944443535205617)
                  ·
                    refine ⟨30882627124458332651404213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41176836165944443535205617 30882627124458332651404213)
                    ·
                      refine ⟨2895246292917968686069145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30882627124458332651404213 2895246292917968686069145)
                      ·
                        rfl

theorem cell23_5638472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_5638472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638472 prefixEnd_5638472 := by exact prefixLift 5638472
  have htrace : WordTrace (prefixWord ++ tailWord_5638472) baseStart_5638472 baseEnd_5638472 := by
    simpa [prefixWord, tailWord_5638472, baseEnd_5638472] using wordTrace_append hprefix tailTrace_5638472
  have hstable : (prefixWord ++ tailWord_5638472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638472).length < 2 ^ (prefixWord ++ tailWord_5638472).sum := by decide
  have hdescent : baseEnd_5638472 < baseStart_5638472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638494 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5638494 : Nat := 118140960795 + 5638494 * 2 ^ 59
def prefixEnd_5638494 : Nat := 4983230072969 + 3 ^ 40 * 5638494 * 2
def baseEnd_5638494 : Nat := 2895257589492367599994045

theorem tailTrace_5638494 : CollatzResearch.WordTrace tailWord_5638494 prefixEnd_5638494 2895257589492367599994045 := by
  unfold tailWord_5638494
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706596404338336369213317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137101847489804460635804357 25706596404338336369213317)
  ·
    refine ⟨4819986825813438069227497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25706596404338336369213317 4819986825813438069227497)
    ·
      refine ⟨3614990119360078551920623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4819986825813438069227497 3614990119360078551920623)
      ·
        refine ⟨5422485179040117827880935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614990119360078551920623 5422485179040117827880935)
        ·
          refine ⟨8133727768560176741821403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422485179040117827880935 8133727768560176741821403)
          ·
            refine ⟨12200591652840265112732105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133727768560176741821403 12200591652840265112732105)
            ·
              refine ⟨9150443739630198834549079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12200591652840265112732105 9150443739630198834549079)
              ·
                refine ⟨13725665609445298251823619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150443739630198834549079 13725665609445298251823619)
                ·
                  refine ⟨20588498414167947377735429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13725665609445298251823619 20588498414167947377735429)
                  ·
                    refine ⟨3860343452656490133325393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20588498414167947377735429 3860343452656490133325393)
                    ·
                      refine ⟨2895257589492367599994045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860343452656490133325393 2895257589492367599994045)
                      ·
                        rfl

theorem cell23_5638494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5638494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638494 prefixEnd_5638494 := by exact prefixLift 5638494
  have htrace : WordTrace (prefixWord ++ tailWord_5638494) baseStart_5638494 baseEnd_5638494 := by
    simpa [prefixWord, tailWord_5638494, baseEnd_5638494] using wordTrace_append hprefix tailTrace_5638494
  have hstable : (prefixWord ++ tailWord_5638494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638494).length < 2 ^ (prefixWord ++ tailWord_5638494).sum := by decide
  have hdescent : baseEnd_5638494 < baseStart_5638494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638519 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_5638519 : Nat := 118140960795 + 5638519 * 2 ^ 59
def prefixEnd_5638519 : Nat := 4983230072969 + 3 ^ 40 * 5638519 * 2
def baseEnd_5638519 : Nat := 2895270426508730002181429

theorem tailTrace_5638519 : CollatzResearch.WordTrace tailWord_5638519 prefixEnd_5638519 2895270426508730002181429 := by
  unfold tailWord_5638519
  simp only [CollatzResearch.WordTrace]
  refine ⟨205653683059616120223366611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137102455373077413482244407 205653683059616120223366611)
  ·
    refine ⟨308480524589424180335049917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205653683059616120223366611 308480524589424180335049917)
    ·
      refine ⟨115680196721034067625643719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308480524589424180335049917 115680196721034067625643719)
      ·
        refine ⟨173520295081551101438465579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115680196721034067625643719 173520295081551101438465579)
        ·
          refine ⟨260280442622326652157698369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173520295081551101438465579 260280442622326652157698369)
          ·
            refine ⟨195210331966744989118273777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260280442622326652157698369 195210331966744989118273777)
            ·
              refine ⟨146407748975058741838705333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195210331966744989118273777 146407748975058741838705333)
              ·
                refine ⟨13725726466411757047378625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146407748975058741838705333 13725726466411757047378625)
                ·
                  refine ⟨10294294849808817785533969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13725726466411757047378625 10294294849808817785533969)
                  ·
                    refine ⟨7720721137356613339150477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10294294849808817785533969 7720721137356613339150477)
                    ·
                      refine ⟨2895270426508730002181429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720721137356613339150477 2895270426508730002181429)
                      ·
                        rfl

theorem cell23_5638519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_5638519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638519 prefixEnd_5638519 := by exact prefixLift 5638519
  have htrace : WordTrace (prefixWord ++ tailWord_5638519) baseStart_5638519 baseEnd_5638519 := by
    simpa [prefixWord, tailWord_5638519, baseEnd_5638519] using wordTrace_append hprefix tailTrace_5638519
  have hstable : (prefixWord ++ tailWord_5638519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638519).length < 2 ^ (prefixWord ++ tailWord_5638519).sum := by decide
  have hdescent : baseEnd_5638519 < baseStart_5638519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638529 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5638529 : Nat := 118140960795 + 5638529 * 2 ^ 59
def prefixEnd_5638529 : Nat := 4983230072969 + 3 ^ 40 * 5638529 * 2
def baseEnd_5638529 : Nat := 2895275561315274963056383

theorem tailTrace_5638529 : CollatzResearch.WordTrace tailWord_5638529 prefixEnd_5638529 2895275561315274963056383 := by
  unfold tailWord_5638529
  simp only [CollatzResearch.WordTrace]
  refine ⟨205654047789579891931230641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137102698526386594620820427 205654047789579891931230641)
  ·
    refine ⟨154240535842184918948422981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205654047789579891931230641 154240535842184918948422981)
    ·
      refine ⟨28920100470409672302829309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154240535842184918948422981 28920100470409672302829309)
      ·
        refine ⟨10845037676403627113560991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28920100470409672302829309 10845037676403627113560991)
        ·
          refine ⟨16267556514605440670341487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10845037676403627113560991 16267556514605440670341487)
          ·
            refine ⟨24401334771908161005512231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16267556514605440670341487 24401334771908161005512231)
            ·
              refine ⟨36602002157862241508268347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24401334771908161005512231 36602002157862241508268347)
              ·
                refine ⟨54903003236793362262402521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36602002157862241508268347 54903003236793362262402521)
                ·
                  refine ⟨41177252427595021696801891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54903003236793362262402521 41177252427595021696801891)
                  ·
                    refine ⟨61765878641392532545202837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41177252427595021696801891 61765878641392532545202837)
                    ·
                      refine ⟨2895275561315274963056383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61765878641392532545202837 2895275561315274963056383)
                      ·
                        rfl

theorem cell23_5638529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5638529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638529 prefixEnd_5638529 := by exact prefixLift 5638529
  have htrace : WordTrace (prefixWord ++ tailWord_5638529) baseStart_5638529 baseEnd_5638529 := by
    simpa [prefixWord, tailWord_5638529, baseEnd_5638529] using wordTrace_append hprefix tailTrace_5638529
  have hstable : (prefixWord ++ tailWord_5638529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638529).length < 2 ^ (prefixWord ++ tailWord_5638529).sum := by decide
  have hdescent : baseEnd_5638529 < baseStart_5638529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638539 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 6]
def baseStart_5638539 : Nat := 118140960795 + 5638539 * 2 ^ 59
def prefixEnd_5638539 : Nat := 4983230072969 + 3 ^ 40 * 5638539 * 2
def baseEnd_5638539 : Nat := 321697855124646658214593

theorem tailTrace_5638539 : CollatzResearch.WordTrace tailWord_5638539 prefixEnd_5638539 321697855124646658214593 := by
  unfold tailWord_5638539
  simp only [CollatzResearch.WordTrace]
  refine ⟨205654412519543663639094671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137102941679695775759396447 205654412519543663639094671)
  ·
    refine ⟨308481618779315495458642007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205654412519543663639094671 308481618779315495458642007)
    ·
      refine ⟨462722428168973243187963011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308481618779315495458642007 462722428168973243187963011)
      ·
        refine ⟨694083642253459864781944517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462722428168973243187963011 694083642253459864781944517)
        ·
          refine ⟨130140682922523724646614597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 694083642253459864781944517 130140682922523724646614597)
          ·
            refine ⟨24401378047973198371240237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130140682922523724646614597 24401378047973198371240237)
            ·
              refine ⟨9150516767989949389215089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24401378047973198371240237 9150516767989949389215089)
              ·
                refine ⟨6862887575992462041911317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150516767989949389215089 6862887575992462041911317)
                ·
                  refine ⟨321697855124646658214593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6862887575992462041911317 321697855124646658214593)
                  ·
                    rfl

theorem cell23_5638539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 6].length) (baseStart_5638539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638539 prefixEnd_5638539 := by exact prefixLift 5638539
  have htrace : WordTrace (prefixWord ++ tailWord_5638539) baseStart_5638539 baseEnd_5638539 := by
    simpa [prefixWord, tailWord_5638539, baseEnd_5638539] using wordTrace_append hprefix tailTrace_5638539
  have hstable : (prefixWord ++ tailWord_5638539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638539).length < 2 ^ (prefixWord ++ tailWord_5638539).sum := by decide
  have hdescent : baseEnd_5638539 < baseStart_5638539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638623 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 4]
def baseStart_5638623 : Nat := 118140960795 + 5638623 * 2 ^ 59
def prefixEnd_5638623 : Nat := 4983230072969 + 3 ^ 40 * 5638623 * 2
def baseEnd_5638623 : Nat := 2895323828496797595280951

theorem tailTrace_5638623 : CollatzResearch.WordTrace tailWord_5638623 prefixEnd_5638623 2895323828496797595280951 := by
  unfold tailWord_5638623
  simp only [CollatzResearch.WordTrace]
  refine ⟨205657476251239345985152523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137104984167492897323435015 205657476251239345985152523)
  ·
    refine ⟨308486214376859018977728785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205657476251239345985152523 308486214376859018977728785)
    ·
      refine ⟨231364660782644264233296589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308486214376859018977728785 231364660782644264233296589)
      ·
        refine ⟨86761747793491599087486221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231364660782644264233296589 86761747793491599087486221)
        ·
          refine ⟨32535655422559349657807333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86761747793491599087486221 32535655422559349657807333)
          ·
            refine ⟨6100435391729878060838875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32535655422559349657807333 6100435391729878060838875)
            ·
              refine ⟨9150653087594817091258313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100435391729878060838875 9150653087594817091258313)
              ·
                refine ⟨6862989815696112818443735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150653087594817091258313 6862989815696112818443735)
                ·
                  refine ⟨10294484723544169227665603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862989815696112818443735 10294484723544169227665603)
                  ·
                    refine ⟨15441727085316253841498405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10294484723544169227665603 15441727085316253841498405)
                    ·
                      refine ⟨2895323828496797595280951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15441727085316253841498405 2895323828496797595280951)
                      ·
                        rfl

theorem cell23_5638623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_5638623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638623 prefixEnd_5638623 := by exact prefixLift 5638623
  have htrace : WordTrace (prefixWord ++ tailWord_5638623) baseStart_5638623 baseEnd_5638623 := by
    simpa [prefixWord, tailWord_5638623, baseEnd_5638623] using wordTrace_append hprefix tailTrace_5638623
  have hstable : (prefixWord ++ tailWord_5638623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638623).length < 2 ^ (prefixWord ++ tailWord_5638623).sum := by decide
  have hdescent : baseEnd_5638623 < baseStart_5638623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638640 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 1, 2, 2]
def baseStart_5638640 : Nat := 118140960795 + 5638640 * 2 ^ 59
def prefixEnd_5638640 : Nat := 4983230072969 + 3 ^ 40 * 5638640 * 2
def baseEnd_5638640 : Nat := 2895332557667924028768373

theorem tailTrace_5638640 : CollatzResearch.WordTrace tailWord_5638640 prefixEnd_5638640 2895332557667924028768373 := by
  unfold tailWord_5638640
  simp only [CollatzResearch.WordTrace]
  refine ⟨102829048146088878944260687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137105397528118505259014249 102829048146088878944260687)
  ·
    refine ⟨154243572219133318416391031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102829048146088878944260687 154243572219133318416391031)
    ·
      refine ⟨231365358328699977624586547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154243572219133318416391031 231365358328699977624586547)
      ·
        refine ⟨347048037493049966436879821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231365358328699977624586547 347048037493049966436879821)
        ·
          refine ⟨130143014059893737413829933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347048037493049966436879821 130143014059893737413829933)
          ·
            refine ⟨48803630272460151530186225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130143014059893737413829933 48803630272460151530186225)
            ·
              refine ⟨36602722704345113647639669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48803630272460151530186225 36602722704345113647639669)
              ·
                refine ⟨3431505253532354404466219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36602722704345113647639669 3431505253532354404466219)
                ·
                  refine ⟨5147257880298531606699329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431505253532354404466219 5147257880298531606699329)
                  ·
                    refine ⟨3860443410223898705024497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5147257880298531606699329 3860443410223898705024497)
                    ·
                      refine ⟨2895332557667924028768373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860443410223898705024497 2895332557667924028768373)
                      ·
                        rfl

theorem cell23_5638640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 2, 2].length) (baseStart_5638640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638640 prefixEnd_5638640 := by exact prefixLift 5638640
  have htrace : WordTrace (prefixWord ++ tailWord_5638640) baseStart_5638640 baseEnd_5638640 := by
    simpa [prefixWord, tailWord_5638640, baseEnd_5638640] using wordTrace_append hprefix tailTrace_5638640
  have hstable : (prefixWord ++ tailWord_5638640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638640).length < 2 ^ (prefixWord ++ tailWord_5638640).sum := by decide
  have hdescent : baseEnd_5638640 < baseStart_5638640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638643 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 1, 2, 3]
def baseStart_5638643 : Nat := 118140960795 + 5638643 * 2 ^ 59
def prefixEnd_5638643 : Nat := 4983230072969 + 3 ^ 40 * 5638643 * 2
def baseEnd_5638643 : Nat := 2895334098109887517030859

theorem tailTrace_5638643 : CollatzResearch.WordTrace tailWord_5638643 prefixEnd_5638643 2895334098109887517030859 := by
  unfold tailWord_5638643
  simp only [CollatzResearch.WordTrace]
  refine ⟨205658205711166889400880583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137105470474111259600587055 205658205711166889400880583)
  ·
    refine ⟨308487308566750334101320875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205658205711166889400880583 308487308566750334101320875)
    ·
      refine ⟨462730962850125501151981313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308487308566750334101320875 462730962850125501151981313)
      ·
        refine ⟨347048222137594125863985985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462730962850125501151981313 347048222137594125863985985)
        ·
          refine ⟨260286166603195594397989489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347048222137594125863985985 260286166603195594397989489)
          ·
            refine ⟨195214624952396695798492117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260286166603195594397989489 195214624952396695798492117)
            ·
              refine ⟨4575342772321797557777159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 195214624952396695798492117 4575342772321797557777159)
              ·
                refine ⟨6863014158482696336665739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575342772321797557777159 6863014158482696336665739)
                ·
                  refine ⟨10294521237724044504998609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6863014158482696336665739 10294521237724044504998609)
                  ·
                    refine ⟨7720890928293033378748957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10294521237724044504998609 7720890928293033378748957)
                    ·
                      refine ⟨2895334098109887517030859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7720890928293033378748957 2895334098109887517030859)
                      ·
                        rfl

theorem cell23_5638643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 2, 3].length) (baseStart_5638643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638643 prefixEnd_5638643 := by exact prefixLift 5638643
  have htrace : WordTrace (prefixWord ++ tailWord_5638643) baseStart_5638643 baseEnd_5638643 := by
    simpa [prefixWord, tailWord_5638643, baseEnd_5638643] using wordTrace_append hprefix tailTrace_5638643
  have hstable : (prefixWord ++ tailWord_5638643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638643).length < 2 ^ (prefixWord ++ tailWord_5638643).sum := by decide
  have hdescent : baseEnd_5638643 < baseStart_5638643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638657 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_5638657 : Nat := 118140960795 + 5638657 * 2 ^ 59
def prefixEnd_5638657 : Nat := 4983230072969 + 3 ^ 40 * 5638657 * 2
def baseEnd_5638657 : Nat := 2895341286839050462255795

theorem tailTrace_5638657 : CollatzResearch.WordTrace tailWord_5638657 prefixEnd_5638657 2895341286839050462255795 := by
  unfold tailWord_5638657
  simp only [CollatzResearch.WordTrace]
  refine ⟨205658716333116169791890225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137105810888744113194593483 205658716333116169791890225)
  ·
    refine ⟨154244037249837127343917669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205658716333116169791890225 154244037249837127343917669)
    ·
      refine ⟨28920756984344461376984563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154244037249837127343917669 28920756984344461376984563)
      ·
        refine ⟨43381135476516692065476845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28920756984344461376984563 43381135476516692065476845)
        ·
          refine ⟨16267925803693759524553817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43381135476516692065476845 16267925803693759524553817)
          ·
            refine ⟨12200944352770319643415363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16267925803693759524553817 12200944352770319643415363)
            ·
              refine ⟨18301416529155479465123045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12200944352770319643415363 18301416529155479465123045)
              ·
                refine ⟨3431515599216652399710571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18301416529155479465123045 3431515599216652399710571)
                ·
                  refine ⟨5147273398824978599565857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431515599216652399710571 5147273398824978599565857)
                  ·
                    refine ⟨3860455049118733949674393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5147273398824978599565857 3860455049118733949674393)
                    ·
                      refine ⟨2895341286839050462255795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860455049118733949674393 2895341286839050462255795)
                      ·
                        rfl

theorem cell23_5638657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_5638657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638657 prefixEnd_5638657 := by exact prefixLift 5638657
  have htrace : WordTrace (prefixWord ++ tailWord_5638657) baseStart_5638657 baseEnd_5638657 := by
    simpa [prefixWord, tailWord_5638657, baseEnd_5638657] using wordTrace_append hprefix tailTrace_5638657
  have hstable : (prefixWord ++ tailWord_5638657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638657).length < 2 ^ (prefixWord ++ tailWord_5638657).sum := by decide
  have hdescent : baseEnd_5638657 < baseStart_5638657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638663 : List Nat := [1, 1, 4, 3, 4, 1, 1, 8]
def baseStart_5638663 : Nat := 118140960795 + 5638663 * 2 ^ 59
def prefixEnd_5638663 : Nat := 4983230072969 + 3 ^ 40 * 5638663 * 2
def baseEnd_5638663 : Nat := 107234976582332497732621

theorem tailTrace_5638663 : CollatzResearch.WordTrace tailWord_5638663 prefixEnd_5638663 107234976582332497732621 := by
  unfold tailWord_5638663
  simp only [CollatzResearch.WordTrace]
  refine ⟨205658935171094432816608643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137105956780729621877739095 205658935171094432816608643)
  ·
    refine ⟨308488402756641649224912965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205658935171094432816608643 308488402756641649224912965)
    ·
      refine ⟨57841575516870309229671181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308488402756641649224912965 57841575516870309229671181)
      ·
        refine ⟨21690590818826365961126693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57841575516870309229671181 21690590818826365961126693)
        ·
          refine ⟨4066985778529943617711255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21690590818826365961126693 4066985778529943617711255)
          ·
            refine ⟨6100478667794915426566883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066985778529943617711255 6100478667794915426566883)
            ·
              refine ⟨9150718001692373139850325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100478667794915426566883 9150718001692373139850325)
              ·
                refine ⟨107234976582332497732621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9150718001692373139850325 107234976582332497732621)
                ·
                  rfl

theorem cell23_5638663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 8].length) (baseStart_5638663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638663 prefixEnd_5638663 := by exact prefixLift 5638663
  have htrace : WordTrace (prefixWord ++ tailWord_5638663) baseStart_5638663 baseEnd_5638663 := by
    simpa [prefixWord, tailWord_5638663, baseEnd_5638663] using wordTrace_append hprefix tailTrace_5638663
  have hstable : (prefixWord ++ tailWord_5638663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638663).length < 2 ^ (prefixWord ++ tailWord_5638663).sum := by decide
  have hdescent : baseEnd_5638663 < baseStart_5638663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638689 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_5638689 : Nat := 118140960795 + 5638689 * 2 ^ 59
def prefixEnd_5638689 : Nat := 4983230072969 + 3 ^ 40 * 5638689 * 2
def baseEnd_5638689 : Nat := 965119239406664779018549

theorem tailTrace_5638689 : CollatzResearch.WordTrace tailWord_5638689 prefixEnd_5638689 965119239406664779018549 := by
  unfold tailWord_5638689
  simp only [CollatzResearch.WordTrace]
  refine ⟨205659883469000239257055121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137106588979333492838036747 205659883469000239257055121)
  ·
    refine ⟨154244912601750179442791341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205659883469000239257055121 154244912601750179442791341)
    ·
      refine ⟨57841842225656317291046753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154244912601750179442791341 57841842225656317291046753)
      ·
        refine ⟨43381381669242237968285065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57841842225656317291046753 43381381669242237968285065)
        ·
          refine ⟨32536036251931678476213799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43381381669242237968285065 32536036251931678476213799)
          ·
            refine ⟨48804054377897517714320699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32536036251931678476213799 48804054377897517714320699)
            ·
              refine ⟨73206081566846276571481049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48804054377897517714320699 73206081566846276571481049)
              ·
                refine ⟨54904561175134707428610787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73206081566846276571481049 54904561175134707428610787)
                ·
                  refine ⟨82356841762702061142916181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54904561175134707428610787 82356841762702061142916181)
                  ·
                    refine ⟨965119239406664779018549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82356841762702061142916181 965119239406664779018549)
                    ·
                      rfl

theorem cell23_5638689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_5638689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638689 prefixEnd_5638689 := by exact prefixLift 5638689
  have htrace : WordTrace (prefixWord ++ tailWord_5638689) baseStart_5638689 baseEnd_5638689 := by
    simpa [prefixWord, tailWord_5638689, baseEnd_5638689] using wordTrace_append hprefix tailTrace_5638689
  have hstable : (prefixWord ++ tailWord_5638689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638689).length < 2 ^ (prefixWord ++ tailWord_5638689).sum := by decide
  have hdescent : baseEnd_5638689 < baseStart_5638689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638699 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5]
def baseStart_5638699 : Nat := 118140960795 + 5638699 * 2 ^ 59
def prefixEnd_5638699 : Nat := 4983230072969 + 3 ^ 40 * 5638699 * 2
def baseEnd_5638699 : Nat := 2895362853026539297930601

theorem tailTrace_5638699 : CollatzResearch.WordTrace tailWord_5638699 prefixEnd_5638699 2895362853026539297930601 := by
  unfold tailWord_5638699
  simp only [CollatzResearch.WordTrace]
  refine ⟨205660248198964010964919151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137106832132642673976612767 205660248198964010964919151)
  ·
    refine ⟨308490372298446016447378727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205660248198964010964919151 308490372298446016447378727)
    ·
      refine ⟨462735558447669024671068091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308490372298446016447378727 462735558447669024671068091)
      ·
        refine ⟨694103337671503537006602137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462735558447669024671068091 694103337671503537006602137)
        ·
          refine ⟨520577503253627652754951603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694103337671503537006602137 520577503253627652754951603)
          ·
            refine ⟨780866254880441479132427405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520577503253627652754951603 780866254880441479132427405)
            ·
              refine ⟨292824845580165554674660277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780866254880441479132427405 292824845580165554674660277)
              ·
                refine ⟨27452329273140520750749401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292824845580165554674660277 27452329273140520750749401)
                ·
                  refine ⟨20589246954855390563062051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27452329273140520750749401 20589246954855390563062051)
                  ·
                    refine ⟨30883870432283085844593077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20589246954855390563062051 30883870432283085844593077)
                    ·
                      refine ⟨2895362853026539297930601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30883870432283085844593077 2895362853026539297930601)
                      ·
                        rfl

theorem cell23_5638699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_5638699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638699 prefixEnd_5638699 := by exact prefixLift 5638699
  have htrace : WordTrace (prefixWord ++ tailWord_5638699) baseStart_5638699 baseEnd_5638699 := by
    simpa [prefixWord, tailWord_5638699, baseEnd_5638699] using wordTrace_append hprefix tailTrace_5638699
  have hstable : (prefixWord ++ tailWord_5638699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638699).length < 2 ^ (prefixWord ++ tailWord_5638699).sum := by decide
  have hdescent : baseEnd_5638699 < baseStart_5638699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638701 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5638701 : Nat := 118140960795 + 5638701 * 2 ^ 59
def prefixEnd_5638701 : Nat := 4983230072969 + 3 ^ 40 * 5638701 * 2
def baseEnd_5638701 : Nat := 965121293329282763368531

theorem tailTrace_5638701 : CollatzResearch.WordTrace tailWord_5638701 prefixEnd_5638701 965121293329282763368531 := by
  unfold tailWord_5638701
  simp only [CollatzResearch.WordTrace]
  refine ⟨205660321144956765306491957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137106880763304510204327971 205660321144956765306491957)
  ·
    refine ⟨19280655107339696747483621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205660321144956765306491957 19280655107339696747483621)
    ·
      refine ⟨3615122832626193140153179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19280655107339696747483621 3615122832626193140153179)
      ·
        refine ⟨5422684248939289710229769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615122832626193140153179 5422684248939289710229769)
        ·
          refine ⟨4067013186704467282672327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5422684248939289710229769 4067013186704467282672327)
          ·
            refine ⟨6100519780056700924008491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067013186704467282672327 6100519780056700924008491)
            ·
              refine ⟨9150779670085051386012737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100519780056700924008491 9150779670085051386012737)
              ·
                refine ⟨6863084752563788539509553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150779670085051386012737 6863084752563788539509553)
                ·
                  refine ⟨5147313564422841404632165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6863084752563788539509553 5147313564422841404632165)
                  ·
                    refine ⟨965121293329282763368531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5147313564422841404632165 965121293329282763368531)
                    ·
                      rfl

theorem cell23_5638701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5638701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638701 prefixEnd_5638701 := by exact prefixLift 5638701
  have htrace : WordTrace (prefixWord ++ tailWord_5638701) baseStart_5638701 baseEnd_5638701 := by
    simpa [prefixWord, tailWord_5638701, baseEnd_5638701] using wordTrace_append hprefix tailTrace_5638701
  have hstable : (prefixWord ++ tailWord_5638701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638701).length < 2 ^ (prefixWord ++ tailWord_5638701).sum := by decide
  have hdescent : baseEnd_5638701 < baseStart_5638701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638724 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5638724 : Nat := 118140960795 + 5638724 * 2 ^ 59
def prefixEnd_5638724 : Nat := 4983230072969 + 3 ^ 40 * 5638724 * 2
def baseEnd_5638724 : Nat := 2895375690042901700117987

theorem tailTrace_5638724 : CollatzResearch.WordTrace tailWord_5638724 prefixEnd_5638724 2895375690042901700117987 := by
  unfold tailWord_5638724
  simp only [CollatzResearch.WordTrace]
  refine ⟨102830580011936720117289613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137107440015915626823052817 102830580011936720117289613)
  ·
    refine ⟨38561467504476270043983605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102830580011936720117289613 38561467504476270043983605)
    ·
      refine ⟨3615137578544650316623463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38561467504476270043983605 3615137578544650316623463)
      ·
        refine ⟨5422706367816975474935195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615137578544650316623463 5422706367816975474935195)
        ·
          refine ⟨8134059551725463212402793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422706367816975474935195 8134059551725463212402793)
          ·
            refine ⟨6100544663794097409302095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8134059551725463212402793 6100544663794097409302095)
            ·
              refine ⟨9150816995691146113953143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100544663794097409302095 9150816995691146113953143)
              ·
                refine ⟨13726225493536719170929715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150816995691146113953143 13726225493536719170929715)
                ·
                  refine ⟨20589338240305078756394573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13726225493536719170929715 20589338240305078756394573)
                  ·
                    refine ⟨7721001840114404533647965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20589338240305078756394573 7721001840114404533647965)
                    ·
                      refine ⟨2895375690042901700117987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7721001840114404533647965 2895375690042901700117987)
                      ·
                        rfl

theorem cell23_5638724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5638724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638724 prefixEnd_5638724 := by exact prefixLift 5638724
  have htrace : WordTrace (prefixWord ++ tailWord_5638724) baseStart_5638724 baseEnd_5638724 := by
    simpa [prefixWord, tailWord_5638724, baseEnd_5638724] using wordTrace_append hprefix tailTrace_5638724
  have hstable : (prefixWord ++ tailWord_5638724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638724).length < 2 ^ (prefixWord ++ tailWord_5638724).sum := by decide
  have hdescent : baseEnd_5638724 < baseStart_5638724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638730 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_5638730 : Nat := 118140960795 + 5638730 * 2 ^ 59
def prefixEnd_5638730 : Nat := 4983230072969 + 3 ^ 40 * 5638730 * 2
def baseEnd_5638730 : Nat := 2895378770926828676642959

theorem tailTrace_5638730 : CollatzResearch.WordTrace tailWord_5638730 prefixEnd_5638730 2895378770926828676642959 := by
  unfold tailWord_5638730
  simp only [CollatzResearch.WordTrace]
  refine ⟨51415344715462925814824411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137107585907901135506198429 51415344715462925814824411)
  ·
    refine ⟨77123017073194388722236617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51415344715462925814824411 77123017073194388722236617)
    ·
      refine ⟨57842262804895791541677463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77123017073194388722236617 57842262804895791541677463)
      ·
        refine ⟨86763394207343687312516195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57842262804895791541677463 86763394207343687312516195)
        ·
          refine ⟨130145091311015530968774293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86763394207343687312516195 130145091311015530968774293)
          ·
            refine ⟨6100551155203853014161295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130145091311015530968774293 6100551155203853014161295)
            ·
              refine ⟨9150826732805779521241943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100551155203853014161295 9150826732805779521241943)
              ·
                refine ⟨13726240099208669281862915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150826732805779521241943 13726240099208669281862915)
                ·
                  refine ⟨20589360148813003922794373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13726240099208669281862915 20589360148813003922794373)
                  ·
                    refine ⟨3860505027902438235523945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20589360148813003922794373 3860505027902438235523945)
                    ·
                      refine ⟨2895378770926828676642959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860505027902438235523945 2895378770926828676642959)
                      ·
                        rfl

theorem cell23_5638730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_5638730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638730 prefixEnd_5638730 := by exact prefixLift 5638730
  have htrace : WordTrace (prefixWord ++ tailWord_5638730) baseStart_5638730 baseEnd_5638730 := by
    simpa [prefixWord, tailWord_5638730, baseEnd_5638730] using wordTrace_append hprefix tailTrace_5638730
  have hstable : (prefixWord ++ tailWord_5638730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638730).length < 2 ^ (prefixWord ++ tailWord_5638730).sum := by decide
  have hdescent : baseEnd_5638730 < baseStart_5638730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638753 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 5]
def baseStart_5638753 : Nat := 118140960795 + 5638753 * 2 ^ 59
def prefixEnd_5638753 : Nat := 4983230072969 + 3 ^ 40 * 5638753 * 2
def baseEnd_5638753 : Nat := 321710064553542454072817

theorem tailTrace_5638753 : CollatzResearch.WordTrace tailWord_5638753 prefixEnd_5638753 321710064553542454072817 := by
  unfold tailWord_5638753
  simp only [CollatzResearch.WordTrace]
  refine ⟨205662217740768378187384913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137108145160512252124923275 205662217740768378187384913)
  ·
    refine ⟨154246663305576283640538685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205662217740768378187384913 154246663305576283640538685)
    ·
      refine ⟨57842498739591106365202007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154246663305576283640538685 57842498739591106365202007)
      ·
        refine ⟨86763748109386659547803011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57842498739591106365202007 86763748109386659547803011)
        ·
          refine ⟨130145622164079989321704517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86763748109386659547803011 130145622164079989321704517)
          ·
            refine ⟨24402304155764997997819597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130145622164079989321704517 24402304155764997997819597)
            ·
              refine ⟨9150864058411874249182349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24402304155764997997819597 9150864058411874249182349)
              ·
                refine ⟨3431574021904452843443381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9150864058411874249182349 3431574021904452843443381)
                ·
                  refine ⟨321710064553542454072817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3431574021904452843443381 321710064553542454072817)
                  ·
                    rfl

theorem cell23_5638753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 5].length) (baseStart_5638753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638753 prefixEnd_5638753 := by exact prefixLift 5638753
  have htrace : WordTrace (prefixWord ++ tailWord_5638753) baseStart_5638753 baseEnd_5638753 := by
    simpa [prefixWord, tailWord_5638753, baseEnd_5638753] using wordTrace_append hprefix tailTrace_5638753
  have hstable : (prefixWord ++ tailWord_5638753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638753).length < 2 ^ (prefixWord ++ tailWord_5638753).sum := by decide
  have hdescent : baseEnd_5638753 < baseStart_5638753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638769 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_5638769 : Nat := 118140960795 + 5638769 * 2 ^ 59
def prefixEnd_5638769 : Nat := 4983230072969 + 3 ^ 40 * 5638769 * 2
def baseEnd_5638769 : Nat := 2895398796672354024055279

theorem tailTrace_5638769 : CollatzResearch.WordTrace tailWord_5638769 prefixEnd_5638769 2895398796672354024055279 := by
  unfold tailWord_5638769
  simp only [CollatzResearch.WordTrace]
  refine ⟨205662801308710412919967361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137108534205806941946644907 205662801308710412919967361)
  ·
    refine ⟨154247100981532809689975521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205662801308710412919967361 154247100981532809689975521)
    ·
      refine ⟨115685325736149607267481641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154247100981532809689975521 115685325736149607267481641)
      ·
        refine ⟨86763994302112205450611231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115685325736149607267481641 86763994302112205450611231)
        ·
          refine ⟨130145991453168308175916847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86763994302112205450611231 130145991453168308175916847)
          ·
            refine ⟨195218987179752462263875271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130145991453168308175916847 195218987179752462263875271)
            ·
              refine ⟨292828480769628693395812907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195218987179752462263875271 292828480769628693395812907)
              ·
                refine ⟨439242721154443040093719361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292828480769628693395812907 439242721154443040093719361)
                ·
                  refine ⟨329432040865832280070289521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439242721154443040093719361 329432040865832280070289521)
                  ·
                    refine ⟨247074030649374210052717141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 329432040865832280070289521 247074030649374210052717141)
                    ·
                      refine ⟨2895398796672354024055279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 247074030649374210052717141 2895398796672354024055279)
                      ·
                        rfl

theorem cell23_5638769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_5638769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638769 prefixEnd_5638769 := by exact prefixLift 5638769
  have htrace : WordTrace (prefixWord ++ tailWord_5638769) baseStart_5638769 baseEnd_5638769 := by
    simpa [prefixWord, tailWord_5638769, baseEnd_5638769] using wordTrace_append hprefix tailTrace_5638769
  have hstable : (prefixWord ++ tailWord_5638769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638769).length < 2 ^ (prefixWord ++ tailWord_5638769).sum := by decide
  have hdescent : baseEnd_5638769 < baseStart_5638769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638770 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_5638770 : Nat := 118140960795 + 5638770 * 2 ^ 59
def prefixEnd_5638770 : Nat := 4983230072969 + 3 ^ 40 * 5638770 * 2
def baseEnd_5638770 : Nat := 321711034461445391126975

theorem tailTrace_5638770 : CollatzResearch.WordTrace tailWord_5638770 prefixEnd_5638770 321711034461445391126975 := by
  unfold tailWord_5638770
  simp only [CollatzResearch.WordTrace]
  refine ⟨51415709445426697522688441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137108558521137860060502509 51415709445426697522688441)
  ·
    refine ⟨38561782084070023142016331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51415709445426697522688441 38561782084070023142016331)
    ·
      refine ⟨57842673126105034713024497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38561782084070023142016331 57842673126105034713024497)
      ·
        refine ⟨43382004844578776034768373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57842673126105034713024497 43382004844578776034768373)
        ·
          refine ⟨4067062954179260253259535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43382004844578776034768373 4067062954179260253259535)
          ·
            refine ⟨6100594431268890379889303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067062954179260253259535 6100594431268890379889303)
            ·
              refine ⟨9150891646903335569833955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100594431268890379889303 9150891646903335569833955)
              ·
                refine ⟨13726337470355003354750933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150891646903335569833955 13726337470355003354750933)
                ·
                  refine ⟨321711034461445391126975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13726337470355003354750933 321711034461445391126975)
                  ·
                    rfl

theorem cell23_5638770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_5638770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638770 prefixEnd_5638770 := by exact prefixLift 5638770
  have htrace : WordTrace (prefixWord ++ tailWord_5638770) baseStart_5638770 baseEnd_5638770 := by
    simpa [prefixWord, tailWord_5638770, baseEnd_5638770] using wordTrace_append hprefix tailTrace_5638770
  have hstable : (prefixWord ++ tailWord_5638770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638770).length < 2 ^ (prefixWord ++ tailWord_5638770).sum := by decide
  have hdescent : baseEnd_5638770 < baseStart_5638770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638779 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 8]
def baseStart_5638779 : Nat := 118140960795 + 5638779 * 2 ^ 59
def prefixEnd_5638779 : Nat := 4983230072969 + 3 ^ 40 * 5638779 * 2
def baseEnd_5638779 : Nat := 965134643826299661643411

theorem tailTrace_5638779 : CollatzResearch.WordTrace tailWord_5638779 prefixEnd_5638779 965134643826299661643411 := by
  unfold tailWord_5638779
  simp only [CollatzResearch.WordTrace]
  refine ⟨205663166038674184627831391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137108777359116123085220927 205663166038674184627831391)
  ·
    refine ⟨308494749058011276941747087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205663166038674184627831391 308494749058011276941747087)
    ·
      refine ⟨462742123587016915412620631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308494749058011276941747087 462742123587016915412620631)
      ·
        refine ⟨694113185380525373118930947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462742123587016915412620631 694113185380525373118930947)
        ·
          refine ⟨1041169778070788059678396421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694113185380525373118930947 1041169778070788059678396421)
          ·
            refine ⟨195219333388272761189699329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1041169778070788059678396421 195219333388272761189699329)
            ·
              refine ⟨146414500041204570892274497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195219333388272761189699329 146414500041204570892274497)
              ·
                refine ⟨109810875030903428169205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146414500041204570892274497 109810875030903428169205873)
                ·
                  refine ⟨82358156273177571126904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109810875030903428169205873 82358156273177571126904405)
                  ·
                    refine ⟨965134643826299661643411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82358156273177571126904405 965134643826299661643411)
                    ·
                      rfl

theorem cell23_5638779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_5638779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638779 prefixEnd_5638779 := by exact prefixLift 5638779
  have htrace : WordTrace (prefixWord ++ tailWord_5638779) baseStart_5638779 baseEnd_5638779 := by
    simpa [prefixWord, tailWord_5638779, baseEnd_5638779] using wordTrace_append hprefix tailTrace_5638779
  have hstable : (prefixWord ++ tailWord_5638779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638779).length < 2 ^ (prefixWord ++ tailWord_5638779).sum := by decide
  have hdescent : baseEnd_5638779 < baseStart_5638779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638781 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_5638781 : Nat := 118140960795 + 5638781 * 2 ^ 59
def prefixEnd_5638781 : Nat := 4983230072969 + 3 ^ 40 * 5638781 * 2
def baseEnd_5638781 : Nat := 2895404958440207977105225

theorem tailTrace_5638781 : CollatzResearch.WordTrace tailWord_5638781 prefixEnd_5638781 2895404958440207977105225 := by
  unfold tailWord_5638781
  simp only [CollatzResearch.WordTrace]
  refine ⟨205663238984666938969404197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137108825989777959312936131 205663238984666938969404197)
  ·
    refine ⟨38561857309625051056763287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205663238984666938969404197 38561857309625051056763287)
    ·
      refine ⟨57842785964437576585144931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38561857309625051056763287 57842785964437576585144931)
      ·
        refine ⟨86764178946656364877717397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57842785964437576585144931 86764178946656364877717397)
        ·
          refine ⟨4067070888124517103643003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86764178946656364877717397 4067070888124517103643003)
          ·
            refine ⟨6100606332186775655464505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067070888124517103643003 6100606332186775655464505)
            ·
              refine ⟨4575454749140081741598379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6100606332186775655464505 4575454749140081741598379)
              ·
                refine ⟨6863182123710122612397569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575454749140081741598379 6863182123710122612397569)
                ·
                  refine ⟨5147386592782591959298177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6863182123710122612397569 5147386592782591959298177)
                  ·
                    refine ⟨3860539944586943969473633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5147386592782591959298177 3860539944586943969473633)
                    ·
                      refine ⟨2895404958440207977105225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860539944586943969473633 2895404958440207977105225)
                      ·
                        rfl

theorem cell23_5638781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_5638781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638781 prefixEnd_5638781 := by exact prefixLift 5638781
  have htrace : WordTrace (prefixWord ++ tailWord_5638781) baseStart_5638781 baseEnd_5638781 := by
    simpa [prefixWord, tailWord_5638781, baseEnd_5638781] using wordTrace_append hprefix tailTrace_5638781
  have hstable : (prefixWord ++ tailWord_5638781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638781).length < 2 ^ (prefixWord ++ tailWord_5638781).sum := by decide
  have hdescent : baseEnd_5638781 < baseStart_5638781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638873 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 1, 5]
def baseStart_5638873 : Nat := 118140960795 + 5638873 * 2 ^ 59
def prefixEnd_5638873 : Nat := 4983230072969 + 3 ^ 40 * 5638873 * 2
def baseEnd_5638873 : Nat := 965150732886807205718267

theorem tailTrace_5638873 : CollatzResearch.WordTrace tailWord_5638873 prefixEnd_5638873 965150732886807205718267 := by
  unfold tailWord_5638873
  simp only [CollatzResearch.WordTrace]
  refine ⟨205666594500333638681753273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137111063000222425787835515 205666594500333638681753273)
  ·
    refine ⟨154249945875250229011314955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205666594500333638681753273 154249945875250229011314955)
    ·
      refine ⟨231374918812875343516972433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154249945875250229011314955 231374918812875343516972433)
      ·
        refine ⟨173531189109656507637729325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231374918812875343516972433 173531189109656507637729325)
        ·
          refine ⟨65074195916121190364148497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173531189109656507637729325 65074195916121190364148497)
          ·
            refine ⟨48805646937090892773111373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65074195916121190364148497 48805646937090892773111373)
            ·
              refine ⟨18302117601409084789916765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48805646937090892773111373 18302117601409084789916765)
              ·
                refine ⟨6863294100528406796218787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18302117601409084789916765 6863294100528406796218787)
                ·
                  refine ⟨10294941150792610194328181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6863294100528406796218787 10294941150792610194328181)
                  ·
                    refine ⟨965150732886807205718267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10294941150792610194328181 965150732886807205718267)
                    ·
                      rfl

theorem cell23_5638873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_5638873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638873 prefixEnd_5638873 := by exact prefixLift 5638873
  have htrace : WordTrace (prefixWord ++ tailWord_5638873) baseStart_5638873 baseEnd_5638873 := by
    simpa [prefixWord, tailWord_5638873, baseEnd_5638873] using wordTrace_append hprefix tailTrace_5638873
  have hstable : (prefixWord ++ tailWord_5638873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638873).length < 2 ^ (prefixWord ++ tailWord_5638873).sum := by decide
  have hdescent : baseEnd_5638873 < baseStart_5638873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638944 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 3, 2, 2]
def baseStart_5638944 : Nat := 118140960795 + 5638944 * 2 ^ 59
def prefixEnd_5638944 : Nat := 4983230072969 + 3 ^ 40 * 5638944 * 2
def baseEnd_5638944 : Nat := 2895488655786890839366975

theorem tailTrace_5638944 : CollatzResearch.WordTrace tailWord_5638944 prefixEnd_5638944 2895488655786890839366975 := by
  unfold tailWord_5638944
  simp only [CollatzResearch.WordTrace]
  refine ⟨102834592041538208903793943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137112789388717611871725257 102834592041538208903793943)
  ·
    refine ⟨154251888062307313355690915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102834592041538208903793943 154251888062307313355690915)
    ·
      refine ⟨231377832093460970033536373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154251888062307313355690915 231377832093460970033536373)
      ·
        refine ⟨21691671758761965940644035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231377832093460970033536373 21691671758761965940644035)
        ·
          refine ⟨32537507638142948910966053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21691671758761965940644035 32537507638142948910966053)
          ·
            refine ⟨6100782682151802920806135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32537507638142948910966053 6100782682151802920806135)
            ·
              refine ⟨9151174023227704381209203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100782682151802920806135 9151174023227704381209203)
              ·
                refine ⟨13726761034841556571813805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9151174023227704381209203 13726761034841556571813805)
                ·
                  refine ⟨5147535388065583714430177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13726761034841556571813805 5147535388065583714430177)
                  ·
                    refine ⟨3860651541049187785822633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5147535388065583714430177 3860651541049187785822633)
                    ·
                      refine ⟨2895488655786890839366975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860651541049187785822633 2895488655786890839366975)
                      ·
                        rfl

theorem cell23_5638944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_5638944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638944 prefixEnd_5638944 := by exact prefixLift 5638944
  have htrace : WordTrace (prefixWord ++ tailWord_5638944) baseStart_5638944 baseEnd_5638944 := by
    simpa [prefixWord, tailWord_5638944, baseEnd_5638944] using wordTrace_append hprefix tailTrace_5638944
  have hstable : (prefixWord ++ tailWord_5638944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638944).length < 2 ^ (prefixWord ++ tailWord_5638944).sum := by decide
  have hdescent : baseEnd_5638944 < baseStart_5638944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638954 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_5638954 : Nat := 118140960795 + 5638954 * 2 ^ 59
def prefixEnd_5638954 : Nat := 4983230072969 + 3 ^ 40 * 5638954 * 2
def baseEnd_5638954 : Nat := 965164596864478600080643

theorem tailTrace_5638954 : CollatzResearch.WordTrace tailWord_5638954 prefixEnd_5638954 965164596864478600080643 := by
  unfold tailWord_5638954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51417387203260047378862979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137113032542026793010301277 51417387203260047378862979)
  ·
    refine ⟨77126080804890071068294469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51417387203260047378862979 77126080804890071068294469)
    ·
      refine ⟨14461140150916888325305213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77126080804890071068294469 14461140150916888325305213)
      ·
        refine ⟨5422927556593833121989455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14461140150916888325305213 5422927556593833121989455)
        ·
          refine ⟨8134391334890749682984183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422927556593833121989455 8134391334890749682984183)
          ·
            refine ⟨12201587002336124524476275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8134391334890749682984183 12201587002336124524476275)
            ·
              refine ⟨18302380503504186786714413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12201587002336124524476275 18302380503504186786714413)
              ·
                refine ⟨6863392688814070045017905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18302380503504186786714413 6863392688814070045017905)
                ·
                  refine ⟨5147544516610552533763429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6863392688814070045017905 5147544516610552533763429)
                  ·
                    refine ⟨965164596864478600080643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5147544516610552533763429 965164596864478600080643)
                    ·
                      rfl

theorem cell23_5638954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_5638954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5638954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5638954 prefixEnd_5638954 := by exact prefixLift 5638954
  have htrace : WordTrace (prefixWord ++ tailWord_5638954) baseStart_5638954 baseEnd_5638954 := by
    simpa [prefixWord, tailWord_5638954, baseEnd_5638954] using wordTrace_append hprefix tailTrace_5638954
  have hstable : (prefixWord ++ tailWord_5638954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638954).length < 2 ^ (prefixWord ++ tailWord_5638954).sum := by decide
  have hdescent : baseEnd_5638954 < baseStart_5638954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639013 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_5639013 : Nat := 118140960795 + 5639013 * 2 ^ 59
def prefixEnd_5639013 : Nat := 4983230072969 + 3 ^ 40 * 5639013 * 2
def baseEnd_5639013 : Nat := 2895524085952051069404157

theorem tailTrace_5639013 : CollatzResearch.WordTrace tailWord_5639013 prefixEnd_5639013 2895524085952051069404157 := by
  unfold tailWord_5639013
  simp only [CollatzResearch.WordTrace]
  refine ⟨205671700719826442591849693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137114467146550961727899795 205671700719826442591849693)
  ·
    refine ⟨77126887769934915971943635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205671700719826442591849693 77126887769934915971943635)
    ·
      refine ⟨115690331654902373957915453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77126887769934915971943635 115690331654902373957915453)
      ·
        refine ⟨43383874370588390234218295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115690331654902373957915453 43383874370588390234218295)
        ·
          refine ⟨65075811555882585351327443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43383874370588390234218295 65075811555882585351327443)
          ·
            refine ⟨97613717333823878026991165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65075811555882585351327443 97613717333823878026991165)
            ·
              refine ⟨36605144000183954260121687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97613717333823878026991165 36605144000183954260121687)
              ·
                refine ⟨54907716000275931390182531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36605144000183954260121687 54907716000275931390182531)
                ·
                  refine ⟨82361574000413897085273797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54907716000275931390182531 82361574000413897085273797)
                  ·
                    refine ⟨15442795125077605703488837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82361574000413897085273797 15442795125077605703488837)
                    ·
                      refine ⟨2895524085952051069404157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15442795125077605703488837 2895524085952051069404157)
                      ·
                        rfl

theorem cell23_5639013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_5639013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639013 prefixEnd_5639013 := by exact prefixLift 5639013
  have htrace : WordTrace (prefixWord ++ tailWord_5639013) baseStart_5639013 baseEnd_5639013 := by
    simpa [prefixWord, tailWord_5639013, baseEnd_5639013] using wordTrace_append hprefix tailTrace_5639013
  have hstable : (prefixWord ++ tailWord_5639013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639013).length < 2 ^ (prefixWord ++ tailWord_5639013).sum := by decide
  have hdescent : baseEnd_5639013 < baseStart_5639013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639063 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5639063 : Nat := 118140960795 + 5639063 * 2 ^ 59
def prefixEnd_5639063 : Nat := 4983230072969 + 3 ^ 40 * 5639063 * 2
def baseEnd_5639063 : Nat := 2895549759984775873778927

theorem tailTrace_5639063 : CollatzResearch.WordTrace tailWord_5639063 prefixEnd_5639063 2895549759984775873778927 := by
  unfold tailWord_5639063
  simp only [CollatzResearch.WordTrace]
  refine ⟨205673524369645301131169843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137115682913096867420779895 205673524369645301131169843)
  ·
    refine ⟨308510286554467951696754765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205673524369645301131169843 308510286554467951696754765)
    ·
      refine ⟨115691357457925481886283037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308510286554467951696754765 115691357457925481886283037)
      ·
        refine ⟨43384259046722055707356139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115691357457925481886283037 43384259046722055707356139)
        ·
          refine ⟨65076388570083083561034209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43384259046722055707356139 65076388570083083561034209)
          ·
            refine ⟨48807291427562312670775657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65076388570083083561034209 48807291427562312670775657)
            ·
              refine ⟨36605468570671734503081743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48807291427562312670775657 36605468570671734503081743)
              ·
                refine ⟨54908202856007601754622615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36605468570671734503081743 54908202856007601754622615)
                ·
                  refine ⟨82362304284011402631933923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54908202856007601754622615 82362304284011402631933923)
                  ·
                    refine ⟨123543456426017103947900885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82362304284011402631933923 123543456426017103947900885)
                    ·
                      refine ⟨2895549759984775873778927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123543456426017103947900885 2895549759984775873778927)
                      ·
                        rfl

theorem cell23_5639063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5639063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639063 prefixEnd_5639063 := by exact prefixLift 5639063
  have htrace : WordTrace (prefixWord ++ tailWord_5639063) baseStart_5639063 baseEnd_5639063 := by
    simpa [prefixWord, tailWord_5639063, baseEnd_5639063] using wordTrace_append hprefix tailTrace_5639063
  have hstable : (prefixWord ++ tailWord_5639063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639063).length < 2 ^ (prefixWord ++ tailWord_5639063).sum := by decide
  have hdescent : baseEnd_5639063 < baseStart_5639063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639068 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5639068 : Nat := 118140960795 + 5639068 * 2 ^ 59
def prefixEnd_5639068 : Nat := 4983230072969 + 3 ^ 40 * 5639068 * 2
def baseEnd_5639068 : Nat := 2895552327388048354216405

theorem tailTrace_5639068 : CollatzResearch.WordTrace tailWord_5639068 prefixEnd_5639068 2895552327388048354216405 := by
  unfold tailWord_5639068
  simp only [CollatzResearch.WordTrace]
  refine ⟨102836853367313593492550929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137115804489751457990067905 102836853367313593492550929)
  ·
    refine ⟨77127640025485195119413197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102836853367313593492550929 77127640025485195119413197)
    ·
      refine ⟨28922865009556948169779949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77127640025485195119413197 28922865009556948169779949)
      ·
        refine ⟨10846074378583855563667481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28922865009556948169779949 10846074378583855563667481)
        ·
          refine ⟨8134555783937891672750611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10846074378583855563667481 8134555783937891672750611)
          ·
            refine ⟨12201833675906837509125917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8134555783937891672750611 12201833675906837509125917)
            ·
              refine ⟨4575687628465064065922219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12201833675906837509125917 4575687628465064065922219)
              ·
                refine ⟨6863531442697596098883329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575687628465064065922219 6863531442697596098883329)
                ·
                  refine ⟨5147648582023197074162497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6863531442697596098883329 5147648582023197074162497)
                  ·
                    refine ⟨3860736436517397805621873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5147648582023197074162497 3860736436517397805621873)
                    ·
                      refine ⟨2895552327388048354216405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860736436517397805621873 2895552327388048354216405)
                      ·
                        rfl

theorem cell23_5639068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5639068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639068 prefixEnd_5639068 := by exact prefixLift 5639068
  have htrace : WordTrace (prefixWord ++ tailWord_5639068) baseStart_5639068 baseEnd_5639068 := by
    simpa [prefixWord, tailWord_5639068, baseEnd_5639068] using wordTrace_append hprefix tailTrace_5639068
  have hstable : (prefixWord ++ tailWord_5639068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639068).length < 2 ^ (prefixWord ++ tailWord_5639068).sum := by decide
  have hdescent : baseEnd_5639068 < baseStart_5639068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639103 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_5639103 : Nat := 118140960795 + 5639103 * 2 ^ 59
def prefixEnd_5639103 : Nat := 4983230072969 + 3 ^ 40 * 5639103 * 2
def baseEnd_5639103 : Nat := 2895570299210955717278743

theorem tailTrace_5639103 : CollatzResearch.WordTrace tailWord_5639103 prefixEnd_5639103 2895570299210955717278743 := by
  unfold tailWord_5639103
  simp only [CollatzResearch.WordTrace]
  refine ⟨205674983289500387962625963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137116655526333591975083975 205674983289500387962625963)
  ·
    refine ⟨308512474934250581943938945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205674983289500387962625963 308512474934250581943938945)
    ·
      refine ⟨231384356200687936457954209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308512474934250581943938945 231384356200687936457954209)
      ·
        refine ⟨173538267150515952343465657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231384356200687936457954209 173538267150515952343465657)
        ·
          refine ⟨130153700362886964257599243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173538267150515952343465657 130153700362886964257599243)
          ·
            refine ⟨195230550544330446386398865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130153700362886964257599243 195230550544330446386398865)
            ·
              refine ⟨146422912908247834789799149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195230550544330446386398865 146422912908247834789799149)
              ·
                refine ⟨54908592340592938046174681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146422912908247834789799149 54908592340592938046174681)
                ·
                  refine ⟨41181444255444703534631011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54908592340592938046174681 41181444255444703534631011)
                  ·
                    refine ⟨61772166383167055301946517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41181444255444703534631011 61772166383167055301946517)
                    ·
                      refine ⟨2895570299210955717278743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61772166383167055301946517 2895570299210955717278743)
                      ·
                        rfl

theorem cell23_5639103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_5639103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639103 prefixEnd_5639103 := by exact prefixLift 5639103
  have htrace : WordTrace (prefixWord ++ tailWord_5639103) baseStart_5639103 baseEnd_5639103 := by
    simpa [prefixWord, tailWord_5639103, baseEnd_5639103] using wordTrace_append hprefix tailTrace_5639103
  have hstable : (prefixWord ++ tailWord_5639103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639103).length < 2 ^ (prefixWord ++ tailWord_5639103).sum := by decide
  have hdescent : baseEnd_5639103 < baseStart_5639103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639201 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5639201 : Nat := 118140960795 + 5639201 * 2 ^ 59
def prefixEnd_5639201 : Nat := 4983230072969 + 3 ^ 40 * 5639201 * 2
def baseEnd_5639201 : Nat := 2895620620315096333853293

theorem tailTrace_5639201 : CollatzResearch.WordTrace tailWord_5639201 prefixEnd_5639201 2895620620315096333853293 := by
  unfold tailWord_5639201
  simp only [CollatzResearch.WordTrace]
  refine ⟨205678557643145350699693457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137119038428763567133128971 205678557643145350699693457)
  ·
    refine ⟨154258918232359013024770093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205678557643145350699693457 154258918232359013024770093)
    ·
      refine ⟨57847094337134629884288785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154258918232359013024770093 57847094337134629884288785)
      ·
        refine ⟨43385320752850972413216589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57847094337134629884288785 43385320752850972413216589)
        ·
          refine ⟨16269495282319114654956221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43385320752850972413216589 16269495282319114654956221)
          ·
            refine ⟨6101060730869667995608583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16269495282319114654956221 6101060730869667995608583)
            ·
              refine ⟨9151591096304501993412875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101060730869667995608583 9151591096304501993412875)
              ·
                refine ⟨13727386644456752990119313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9151591096304501993412875 13727386644456752990119313)
                ·
                  refine ⟨10295539983342564742589485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13727386644456752990119313 10295539983342564742589485)
                  ·
                    refine ⟨3860827493753461778471057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10295539983342564742589485 3860827493753461778471057)
                    ·
                      refine ⟨2895620620315096333853293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3860827493753461778471057 2895620620315096333853293)
                      ·
                        rfl

theorem cell23_5639201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5639201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639201 prefixEnd_5639201 := by exact prefixLift 5639201
  have htrace : WordTrace (prefixWord ++ tailWord_5639201) baseStart_5639201 baseEnd_5639201 := by
    simpa [prefixWord, tailWord_5639201, baseEnd_5639201] using wordTrace_append hprefix tailTrace_5639201
  have hstable : (prefixWord ++ tailWord_5639201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639201).length < 2 ^ (prefixWord ++ tailWord_5639201).sum := by decide
  have hdescent : baseEnd_5639201 < baseStart_5639201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639214 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_5639214 : Nat := 118140960795 + 5639214 * 2 ^ 59
def prefixEnd_5639214 : Nat := 4983230072969 + 3 ^ 40 * 5639214 * 2
def baseEnd_5639214 : Nat := 2895627295563604782990733

theorem tailTrace_5639214 : CollatzResearch.WordTrace tailWord_5639214 prefixEnd_5639214 2895627295563604782990733 := by
  unfold tailWord_5639214
  simp only [CollatzResearch.WordTrace]
  refine ⟨25709878974012281739989587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137119354528065502613277797 25709878974012281739989587)
  ·
    refine ⟨38564818461018422609984381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25709878974012281739989587 38564818461018422609984381)
    ·
      refine ⟨14461806922881908478744143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38564818461018422609984381 14461806922881908478744143)
      ·
        refine ⟨21692710384322862718116215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14461806922881908478744143 21692710384322862718116215)
        ·
          refine ⟨32539065576484294077174323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21692710384322862718116215 32539065576484294077174323)
          ·
            refine ⟨48808598364726441115761485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32539065576484294077174323 48808598364726441115761485)
            ·
              refine ⟨18303224386772415418410557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48808598364726441115761485 18303224386772415418410557)
              ·
                refine ⟨6863709145039655781903959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18303224386772415418410557 6863709145039655781903959)
                ·
                  refine ⟨10295563717559483672855939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6863709145039655781903959 10295563717559483672855939)
                  ·
                    refine ⟨15443345576339225509283909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10295563717559483672855939 15443345576339225509283909)
                    ·
                      refine ⟨2895627295563604782990733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15443345576339225509283909 2895627295563604782990733)
                      ·
                        rfl

theorem cell23_5639214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_5639214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639214 prefixEnd_5639214 := by exact prefixLift 5639214
  have htrace : WordTrace (prefixWord ++ tailWord_5639214) baseStart_5639214 baseEnd_5639214 := by
    simpa [prefixWord, tailWord_5639214, baseEnd_5639214] using wordTrace_append hprefix tailTrace_5639214
  have hstable : (prefixWord ++ tailWord_5639214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639214).length < 2 ^ (prefixWord ++ tailWord_5639214).sum := by decide
  have hdescent : baseEnd_5639214 < baseStart_5639214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639224 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 2, 4]
def baseStart_5639224 : Nat := 118140960795 + 5639224 * 2 ^ 59
def prefixEnd_5639224 : Nat := 4983230072969 + 3 ^ 40 * 5639224 * 2
def baseEnd_5639224 : Nat := 965210810123383247955229

theorem tailTrace_5639224 : CollatzResearch.WordTrace tailWord_5639224 prefixEnd_5639224 965210810123383247955229 := by
  unfold tailWord_5639224
  simp only [CollatzResearch.WordTrace]
  refine ⟨102839698261031012813890363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137119597681374683751853817 102839698261031012813890363)
  ·
    refine ⟨154259547391546519220835545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102839698261031012813890363 154259547391546519220835545)
    ·
      refine ⟨115694660543659889415626659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154259547391546519220835545 115694660543659889415626659)
      ·
        refine ⟨173541990815489834123439989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115694660543659889415626659 173541990815489834123439989)
        ·
          refine ⟨16269561638952171949072499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173541990815489834123439989 16269561638952171949072499)
          ·
            refine ⟨24404342458428257923608749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16269561638952171949072499 24404342458428257923608749)
            ·
              refine ⟨9151628421910596721353281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24404342458428257923608749 9151628421910596721353281)
              ·
                refine ⟨6863721316432947541014961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9151628421910596721353281 6863721316432947541014961)
                ·
                  refine ⟨5147790987324710655761221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6863721316432947541014961 5147790987324710655761221)
                  ·
                    refine ⟨965210810123383247955229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5147790987324710655761221 965210810123383247955229)
                    ·
                      rfl

theorem cell23_5639224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_5639224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639224 prefixEnd_5639224 := by exact prefixLift 5639224
  have htrace : WordTrace (prefixWord ++ tailWord_5639224) baseStart_5639224 baseEnd_5639224 := by
    simpa [prefixWord, tailWord_5639224, baseEnd_5639224] using wordTrace_append hprefix tailTrace_5639224
  have hstable : (prefixWord ++ tailWord_5639224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639224).length < 2 ^ (prefixWord ++ tailWord_5639224).sum := by decide
  have hdescent : baseEnd_5639224 < baseStart_5639224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639247 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 3]
def baseStart_5639247 : Nat := 118140960795 + 5639247 * 2 ^ 59
def prefixEnd_5639247 : Nat := 4983230072969 + 3 ^ 40 * 5639247 * 2
def baseEnd_5639247 : Nat := 2895644240425203153878081

theorem tailTrace_5639247 : CollatzResearch.WordTrace tailWord_5639247 prefixEnd_5639247 2895644240425203153878081 := by
  unfold tailWord_5639247
  simp only [CollatzResearch.WordTrace]
  refine ⟨205680235400978700555867995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137120156933985800370578663 205680235400978700555867995)
  ·
    refine ⟨308520353101468050833801993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205680235400978700555867995 308520353101468050833801993)
    ·
      refine ⟨231390264826101038125351495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308520353101468050833801993 231390264826101038125351495)
      ·
        refine ⟨347085397239151557188027243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231390264826101038125351495 347085397239151557188027243)
        ·
          refine ⟨520628095858727335782040865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347085397239151557188027243 520628095858727335782040865)
          ·
            refine ⟨390471071894045501836530649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520628095858727335782040865 390471071894045501836530649)
            ·
              refine ⟨292853303920534126377397987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390471071894045501836530649 292853303920534126377397987)
              ·
                refine ⟨439279955880801189566096981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292853303920534126377397987 439279955880801189566096981)
                ·
                  refine ⟨5147811982978138940227699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 439279955880801189566096981 5147811982978138940227699)
                  ·
                    refine ⟨7721717974467208410341549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5147811982978138940227699 7721717974467208410341549)
                    ·
                      refine ⟨2895644240425203153878081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7721717974467208410341549 2895644240425203153878081)
                      ·
                        rfl

theorem cell23_5639247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_5639247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639247 prefixEnd_5639247 := by exact prefixLift 5639247
  have htrace : WordTrace (prefixWord ++ tailWord_5639247) baseStart_5639247 baseEnd_5639247 := by
    simpa [prefixWord, tailWord_5639247, baseEnd_5639247] using wordTrace_append hprefix tailTrace_5639247
  have hstable : (prefixWord ++ tailWord_5639247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639247).length < 2 ^ (prefixWord ++ tailWord_5639247).sum := by decide
  have hdescent : baseEnd_5639247 < baseStart_5639247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639357 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_5639357 : Nat := 118140960795 + 5639357 * 2 ^ 59
def prefixEnd_5639357 : Nat := 4983230072969 + 3 ^ 40 * 5639357 * 2
def baseEnd_5639357 : Nat := 965233574432399241167525

theorem tailTrace_5639357 : CollatzResearch.WordTrace tailWord_5639357 prefixEnd_5639357 965233574432399241167525 := by
  unfold tailWord_5639357
  simp only [CollatzResearch.WordTrace]
  refine ⟨205684247430580189342372325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137122831620386792894914883 205684247430580189342372325)
  ·
    refine ⟨38565796393233785501694811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205684247430580189342372325 38565796393233785501694811)
    ·
      refine ⟨57848694589850678252542217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38565796393233785501694811 57848694589850678252542217)
      ·
        refine ⟨43386520942388008689406663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57848694589850678252542217 43386520942388008689406663)
        ·
          refine ⟨65079781413582013034109995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43386520942388008689406663 65079781413582013034109995)
          ·
            refine ⟨97619672120373019551164993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65079781413582013034109995 97619672120373019551164993)
            ·
              refine ⟨73214754090279764663373745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97619672120373019551164993 73214754090279764663373745)
              ·
                refine ⟨54911065567709823497530309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73214754090279764663373745 54911065567709823497530309)
                ·
                  refine ⟨10295824793945591905786933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54911065567709823497530309 10295824793945591905786933)
                  ·
                    refine ⟨965233574432399241167525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10295824793945591905786933 965233574432399241167525)
                    ·
                      rfl

theorem cell23_5639357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_5639357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639357 prefixEnd_5639357 := by exact prefixLift 5639357
  have htrace : WordTrace (prefixWord ++ tailWord_5639357) baseStart_5639357 baseEnd_5639357 := by
    simpa [prefixWord, tailWord_5639357, baseEnd_5639357] using wordTrace_append hprefix tailTrace_5639357
  have hstable : (prefixWord ++ tailWord_5639357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639357).length < 2 ^ (prefixWord ++ tailWord_5639357).sum := by decide
  have hdescent : baseEnd_5639357 < baseStart_5639357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639374 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_5639374 : Nat := 118140960795 + 5639374 * 2 ^ 59
def prefixEnd_5639374 : Nat := 4983230072969 + 3 ^ 40 * 5639374 * 2
def baseEnd_5639374 : Nat := 965236484156108052329999

theorem tailTrace_5639374 : CollatzResearch.WordTrace tailWord_5639374 prefixEnd_5639374 965236484156108052329999 := by
  unfold tailWord_5639374
  simp only [CollatzResearch.WordTrace]
  refine ⟨25710608433939825155717647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137123244981012400830494117 25710608433939825155717647)
  ·
    refine ⟨38565912650909737733576471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25710608433939825155717647 38565912650909737733576471)
    ·
      refine ⟨57848868976364606600364707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38565912650909737733576471 57848868976364606600364707)
      ·
        refine ⟨86773303464546909900547061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57848868976364606600364707 86773303464546909900547061)
        ·
          refine ⟨8134997199801272803176287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86773303464546909900547061 8134997199801272803176287)
          ·
            refine ⟨12202495799701909204764431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8134997199801272803176287 12202495799701909204764431)
            ·
              refine ⟨18303743699552863807146647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12202495799701909204764431 18303743699552863807146647)
              ·
                refine ⟨27455615549329295710719971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18303743699552863807146647 27455615549329295710719971)
                ·
                  refine ⟨41183423323993943566079957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27455615549329295710719971 41183423323993943566079957)
                  ·
                    refine ⟨965236484156108052329999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41183423323993943566079957 965236484156108052329999)
                    ·
                      rfl

theorem cell23_5639374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_5639374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639374 prefixEnd_5639374 := by exact prefixLift 5639374
  have htrace : WordTrace (prefixWord ++ tailWord_5639374) baseStart_5639374 baseEnd_5639374 := by
    simpa [prefixWord, tailWord_5639374, baseEnd_5639374] using wordTrace_append hprefix tailTrace_5639374
  have hstable : (prefixWord ++ tailWord_5639374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639374).length < 2 ^ (prefixWord ++ tailWord_5639374).sum := by decide
  have hdescent : baseEnd_5639374 < baseStart_5639374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639404 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_5639404 : Nat := 118140960795 + 5639404 * 2 ^ 59
def prefixEnd_5639404 : Nat := 4983230072969 + 3 ^ 40 * 5639404 * 2
def baseEnd_5639404 : Nat := 965241618962653013204953

theorem tailTrace_5639404 : CollatzResearch.WordTrace tailWord_5639404 prefixEnd_5639404 965241618962653013204953 := by
  unfold tailWord_5639404
  simp only [CollatzResearch.WordTrace]
  refine ⟨102842980830704958184666633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137123974440939944246222177 102842980830704958184666633)
  ·
    refine ⟨77132235623028718638499975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102842980830704958184666633 77132235623028718638499975)
    ·
      refine ⟨115698353434543077957749963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77132235623028718638499975 115698353434543077957749963)
      ·
        refine ⟨173547530151814616936624945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115698353434543077957749963 173547530151814616936624945)
        ·
          refine ⟨130160647613860962702468709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173547530151814616936624945 130160647613860962702468709)
          ·
            refine ⟨24405121427598930506712883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130160647613860962702468709 24405121427598930506712883)
            ·
              refine ⟨36607682141398395760069325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24405121427598930506712883 36607682141398395760069325)
              ·
                refine ⟨13727880803024398410025997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36607682141398395760069325 13727880803024398410025997)
                ·
                  refine ⟨5147955301134149403759749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13727880803024398410025997 5147955301134149403759749)
                  ·
                    refine ⟨965241618962653013204953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5147955301134149403759749 965241618962653013204953)
                    ·
                      rfl

theorem cell23_5639404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_5639404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639404 prefixEnd_5639404 := by exact prefixLift 5639404
  have htrace : WordTrace (prefixWord ++ tailWord_5639404) baseStart_5639404 baseEnd_5639404 := by
    simpa [prefixWord, tailWord_5639404, baseEnd_5639404] using wordTrace_append hprefix tailTrace_5639404
  have hstable : (prefixWord ++ tailWord_5639404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639404).length < 2 ^ (prefixWord ++ tailWord_5639404).sum := by decide
  have hdescent : baseEnd_5639404 < baseStart_5639404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639438 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_5639438 : Nat := 118140960795 + 5639438 * 2 ^ 59
def prefixEnd_5639438 : Nat := 4983230072969 + 3 ^ 40 * 5639438 * 2
def baseEnd_5639438 : Nat := 965247438410070635529901

theorem tailTrace_5639438 : CollatzResearch.WordTrace tailWord_5639438 prefixEnd_5639438 965247438410070635529901 := by
  unfold tailWord_5639438
  simp only [CollatzResearch.WordTrace]
  refine ⟨25710900217910842522008871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137124801162191160117380645 25710900217910842522008871)
  ·
    refine ⟨38566350326866263783013307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25710900217910842522008871 38566350326866263783013307)
    ·
      refine ⟨57849525490299395674519961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38566350326866263783013307 57849525490299395674519961)
      ·
        refine ⟨43387144117724546755889971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57849525490299395674519961 43387144117724546755889971)
        ·
          refine ⟨65080716176586820133834957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43387144117724546755889971 65080716176586820133834957)
          ·
            refine ⟨24405268566220057550188109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65080716176586820133834957 24405268566220057550188109)
            ·
              refine ⟨9151975712332521581320541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24405268566220057550188109 9151975712332521581320541)
              ·
                refine ⟨3431990892124695592995203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9151975712332521581320541 3431990892124695592995203)
                ·
                  refine ⟨5147986338187043389492805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431990892124695592995203 5147986338187043389492805)
                  ·
                    refine ⟨965247438410070635529901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5147986338187043389492805 965247438410070635529901)
                    ·
                      rfl

theorem cell23_5639438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_5639438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639438 prefixEnd_5639438 := by exact prefixLift 5639438
  have htrace : WordTrace (prefixWord ++ tailWord_5639438) baseStart_5639438 baseEnd_5639438 := by
    simpa [prefixWord, tailWord_5639438, baseEnd_5639438] using wordTrace_append hprefix tailTrace_5639438
  have hstable : (prefixWord ++ tailWord_5639438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639438).length < 2 ^ (prefixWord ++ tailWord_5639438).sum := by decide
  have hdescent : baseEnd_5639438 < baseStart_5639438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639455 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 1, 4]
def baseStart_5639455 : Nat := 118140960795 + 5639455 * 2 ^ 59
def prefixEnd_5639455 : Nat := 4983230072969 + 3 ^ 40 * 5639455 * 2
def baseEnd_5639455 : Nat := 965250348133779446692375

theorem tailTrace_5639455 : CollatzResearch.WordTrace tailWord_5639455 prefixEnd_5639455 965250348133779446692375 := by
  unfold tailWord_5639455
  simp only [CollatzResearch.WordTrace]
  refine ⟨205687821784225152079439819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137125214522816768052959879 205687821784225152079439819)
  ·
    refine ⟨308531732676337728119159729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205687821784225152079439819 308531732676337728119159729)
    ·
      refine ⟨231398799507253296089369797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308531732676337728119159729 231398799507253296089369797)
      ·
        refine ⟨43387274907609993016756837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231398799507253296089369797 43387274907609993016756837)
        ·
          refine ⟨8135114045176873690641907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43387274907609993016756837 8135114045176873690641907)
          ·
            refine ⟨12202671067765310535962861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135114045176873690641907 12202671067765310535962861)
            ·
              refine ⟨4576001650411991450986073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12202671067765310535962861 4576001650411991450986073)
              ·
                refine ⟨3432001237808993588239555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576001650411991450986073 3432001237808993588239555)
                ·
                  refine ⟨5148001856713490382359333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432001237808993588239555 5148001856713490382359333)
                  ·
                    refine ⟨965250348133779446692375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148001856713490382359333 965250348133779446692375)
                    ·
                      rfl

theorem cell23_5639455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 4].length) (baseStart_5639455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639455 prefixEnd_5639455 := by exact prefixLift 5639455
  have htrace : WordTrace (prefixWord ++ tailWord_5639455) baseStart_5639455 baseEnd_5639455 := by
    simpa [prefixWord, tailWord_5639455, baseEnd_5639455] using wordTrace_append hprefix tailTrace_5639455
  have hstable : (prefixWord ++ tailWord_5639455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639455).length < 2 ^ (prefixWord ++ tailWord_5639455).sum := by decide
  have hdescent : baseEnd_5639455 < baseStart_5639455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639457 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5639457 : Nat := 118140960795 + 5639457 * 2 ^ 59
def prefixEnd_5639457 : Nat := 4983230072969 + 3 ^ 40 * 5639457 * 2
def baseEnd_5639457 : Nat := 2895752071362647332252115

theorem tailTrace_5639457 : CollatzResearch.WordTrace tailWord_5639457 prefixEnd_5639457 2895752071362647332252115 := by
  unfold tailWord_5639457
  simp only [CollatzResearch.WordTrace]
  refine ⟨205687894730217906421012625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137125263153478604280675083 205687894730217906421012625)
  ·
    refine ⟨154265921047663429815759469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205687894730217906421012625 154265921047663429815759469)
    ·
      refine ⟨57849720392873786180909801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154265921047663429815759469 57849720392873786180909801)
      ·
        refine ⟨43387290294655339635682351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57849720392873786180909801 43387290294655339635682351)
        ·
          refine ⟨65080935441983009453523527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43387290294655339635682351 65080935441983009453523527)
          ·
            refine ⟨97621403162974514180285291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65080935441983009453523527 97621403162974514180285291)
            ·
              refine ⟨146432104744461771270427937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97621403162974514180285291 146432104744461771270427937)
              ·
                refine ⟨109824078558346328452820953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146432104744461771270427937 109824078558346328452820953)
                ·
                  refine ⟨82368058918759746339615715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109824078558346328452820953 82368058918759746339615715)
                  ·
                    refine ⟨123552088378139619509423573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82368058918759746339615715 123552088378139619509423573)
                    ·
                      refine ⟨2895752071362647332252115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123552088378139619509423573 2895752071362647332252115)
                      ·
                        rfl

theorem cell23_5639457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5639457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639457 prefixEnd_5639457 := by exact prefixLift 5639457
  have htrace : WordTrace (prefixWord ++ tailWord_5639457) baseStart_5639457 baseEnd_5639457 := by
    simpa [prefixWord, tailWord_5639457, baseEnd_5639457] using wordTrace_append hprefix tailTrace_5639457
  have hstable : (prefixWord ++ tailWord_5639457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639457).length < 2 ^ (prefixWord ++ tailWord_5639457).sum := by decide
  have hdescent : baseEnd_5639457 < baseStart_5639457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639481 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 3, 5]
def baseStart_5639481 : Nat := 118140960795 + 5639481 * 2 ^ 59
def prefixEnd_5639481 : Nat := 4983230072969 + 3 ^ 40 * 5639481 * 2
def baseEnd_5639481 : Nat := 965254798299451746117335

theorem tailTrace_5639481 : CollatzResearch.WordTrace tailWord_5639481 prefixEnd_5639481 965254798299451746117335 := by
  unfold tailWord_5639481
  simp only [CollatzResearch.WordTrace]
  refine ⟨205688770082130958519886297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137125846721420639013257531 205688770082130958519886297)
  ·
    refine ⟨154266577561598218889914723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205688770082130958519886297 154266577561598218889914723)
    ·
      refine ⟨231399866342397328334872085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154266577561598218889914723 231399866342397328334872085)
      ·
        refine ⟨10846868734799874765697129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 231399866342397328334872085 10846868734799874765697129)
        ·
          refine ⟨8135151551099906074272847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10846868734799874765697129 8135151551099906074272847)
          ·
            refine ⟨12202727326649859111409271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135151551099906074272847 12202727326649859111409271)
            ·
              refine ⟨18304090989974788667113907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12202727326649859111409271 18304090989974788667113907)
              ·
                refine ⟨27456136484962183000670861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18304090989974788667113907 27456136484962183000670861)
                ·
                  refine ⟨10296051181860818625251573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27456136484962183000670861 10296051181860818625251573)
                  ·
                    refine ⟨965254798299451746117335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10296051181860818625251573 965254798299451746117335)
                    ·
                      rfl

theorem cell23_5639481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_5639481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639481 prefixEnd_5639481 := by exact prefixLift 5639481
  have htrace : WordTrace (prefixWord ++ tailWord_5639481) baseStart_5639481 baseEnd_5639481 := by
    simpa [prefixWord, tailWord_5639481, baseEnd_5639481] using wordTrace_append hprefix tailTrace_5639481
  have hstable : (prefixWord ++ tailWord_5639481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639481).length < 2 ^ (prefixWord ++ tailWord_5639481).sum := by decide
  have hdescent : baseEnd_5639481 < baseStart_5639481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639511 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 2, 4]
def baseStart_5639511 : Nat := 118140960795 + 5639511 * 2 ^ 59
def prefixEnd_5639511 : Nat := 4983230072969 + 3 ^ 40 * 5639511 * 2
def baseEnd_5639511 : Nat := 965259933105996706992289

theorem tailTrace_5639511 : CollatzResearch.WordTrace tailWord_5639511 prefixEnd_5639511 965259933105996706992289 := by
  unfold tailWord_5639511
  simp only [CollatzResearch.WordTrace]
  refine ⟨205689864272022273643478387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137126576181348182428985591 205689864272022273643478387)
  ·
    refine ⟨308534796408033410465217581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205689864272022273643478387 308534796408033410465217581)
    ·
      refine ⟨115700548653012528924456593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308534796408033410465217581 115700548653012528924456593)
      ·
        refine ⟨86775411489759396693342445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115700548653012528924456593 86775411489759396693342445)
        ·
          refine ⟨32540779308659773760003417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86775411489759396693342445 32540779308659773760003417)
          ·
            refine ⟨24405584481494830320002563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32540779308659773760003417 24405584481494830320002563)
            ·
              refine ⟨36608376722242245480003845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24405584481494830320002563 36608376722242245480003845)
              ·
                refine ⟨6864070635420421027500721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36608376722242245480003845 6864070635420421027500721)
                ·
                  refine ⟨5148052976565315770625541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6864070635420421027500721 5148052976565315770625541)
                  ·
                    refine ⟨965259933105996706992289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148052976565315770625541 965259933105996706992289)
                    ·
                      rfl

theorem cell23_5639511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_5639511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639511 prefixEnd_5639511 := by exact prefixLift 5639511
  have htrace : WordTrace (prefixWord ++ tailWord_5639511) baseStart_5639511 baseEnd_5639511 := by
    simpa [prefixWord, tailWord_5639511, baseEnd_5639511] using wordTrace_append hprefix tailTrace_5639511
  have hstable : (prefixWord ++ tailWord_5639511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639511).length < 2 ^ (prefixWord ++ tailWord_5639511).sum := by decide
  have hdescent : baseEnd_5639511 < baseStart_5639511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639524 : List Nat := [2, 3, 1, 1, 3, 2, 3, 8]
def baseStart_5639524 : Nat := 118140960795 + 5639524 * 2 ^ 59
def prefixEnd_5639524 : Nat := 4983230072969 + 3 ^ 40 * 5639524 * 2
def baseEnd_5639524 : Nat := 107251350909870317411641

theorem tailTrace_5639524 : CollatzResearch.WordTrace tailWord_5639524 prefixEnd_5639524 107251350909870317411641 := by
  unfold tailWord_5639524
  simp only [CollatzResearch.WordTrace]
  refine ⟨102845169210487588431850813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137126892280650117909134417 102845169210487588431850813)
  ·
    refine ⟨38566938453932845661944055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102845169210487588431850813 38566938453932845661944055)
    ·
      refine ⟨57850407680899268492916083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38566938453932845661944055 57850407680899268492916083)
      ·
        refine ⟨86775611521348902739374125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57850407680899268492916083 86775611521348902739374125)
        ·
          refine ⟨32540854320505838527265297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86775611521348902739374125 32540854320505838527265297)
          ·
            refine ⟨24405640740379378895448973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32540854320505838527265297 24405640740379378895448973)
            ·
              refine ⟨9152115277642267085793365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24405640740379378895448973 9152115277642267085793365)
              ·
                refine ⟨107251350909870317411641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9152115277642267085793365 107251350909870317411641)
                ·
                  rfl

theorem cell23_5639524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 8].length) (baseStart_5639524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639524 prefixEnd_5639524 := by exact prefixLift 5639524
  have htrace : WordTrace (prefixWord ++ tailWord_5639524) baseStart_5639524 baseEnd_5639524 := by
    simpa [prefixWord, tailWord_5639524, baseEnd_5639524] using wordTrace_append hprefix tailTrace_5639524
  have hstable : (prefixWord ++ tailWord_5639524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639524).length < 2 ^ (prefixWord ++ tailWord_5639524).sum := by decide
  have hdescent : baseEnd_5639524 < baseStart_5639524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639555 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 1, 2, 3]
def baseStart_5639555 : Nat := 118140960795 + 5639555 * 2 ^ 59
def prefixEnd_5639555 : Nat := 4983230072969 + 3 ^ 40 * 5639555 * 2
def baseEnd_5639555 : Nat := 2895802392466787948826665

theorem tailTrace_5639555 : CollatzResearch.WordTrace tailWord_5639555 prefixEnd_5639555 2895802392466787948826665 := by
  unfold tailWord_5639555
  simp only [CollatzResearch.WordTrace]
  refine ⟨205691469083862869158080119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137127646055908579438720079 205691469083862869158080119)
  ·
    refine ⟨308537203625794303737120179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205691469083862869158080119 308537203625794303737120179)
    ·
      refine ⟨462805805438691455605680269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308537203625794303737120179 462805805438691455605680269)
      ·
        refine ⟨173552177039509295852130101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462805805438691455605680269 173552177039509295852130101)
        ·
          refine ⟨16270516597453996486137197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173552177039509295852130101 16270516597453996486137197)
          ·
            refine ⟨6101443724045248682301449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16270516597453996486137197 6101443724045248682301449)
            ·
              refine ⟨4576082793033936511726087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6101443724045248682301449 4576082793033936511726087)
              ·
                refine ⟨6864124189550904767589131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576082793033936511726087 6864124189550904767589131)
                ·
                  refine ⟨10296186284326357151383697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6864124189550904767589131 10296186284326357151383697)
                  ·
                    refine ⟨7722139713244767863537773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10296186284326357151383697 7722139713244767863537773)
                    ·
                      refine ⟨2895802392466787948826665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7722139713244767863537773 2895802392466787948826665)
                      ·
                        rfl

theorem cell23_5639555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_5639555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639555 prefixEnd_5639555 := by exact prefixLift 5639555
  have htrace : WordTrace (prefixWord ++ tailWord_5639555) baseStart_5639555 baseEnd_5639555 := by
    simpa [prefixWord, tailWord_5639555, baseEnd_5639555] using wordTrace_append hprefix tailTrace_5639555
  have hstable : (prefixWord ++ tailWord_5639555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639555).length < 2 ^ (prefixWord ++ tailWord_5639555).sum := by decide
  have hdescent : baseEnd_5639555 < baseStart_5639555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639582 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5639582 : Nat := 118140960795 + 5639582 * 2 ^ 59
def prefixEnd_5639582 : Nat := 4983230072969 + 3 ^ 40 * 5639582 * 2
def baseEnd_5639582 : Nat := 2895816256444459343189041

theorem tailTrace_5639582 : CollatzResearch.WordTrace tailWord_5639582 prefixEnd_5639582 2895816256444459343189041 := by
  unfold tailWord_5639582
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711556731845631596164125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137128302569843368512875333 25711556731845631596164125)
  ·
    refine ⟨9641833774442111848561547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25711556731845631596164125 9641833774442111848561547)
    ·
      refine ⟨14462750661663167772842321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9641833774442111848561547 14462750661663167772842321)
      ·
        refine ⟨10847062996247375829631741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14462750661663167772842321 10847062996247375829631741)
        ·
          refine ⟨4067648623592765936111903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10847062996247375829631741 4067648623592765936111903)
          ·
            refine ⟨6101472935389148904167855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067648623592765936111903 6101472935389148904167855)
            ·
              refine ⟨9152209403083723356251783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101472935389148904167855 9152209403083723356251783)
              ·
                refine ⟨13728314104625585034377675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9152209403083723356251783 13728314104625585034377675)
                ·
                  refine ⟨20592471156938377551566513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13728314104625585034377675 20592471156938377551566513)
                  ·
                    refine ⟨15444353367703783163674885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20592471156938377551566513 15444353367703783163674885)
                    ·
                      refine ⟨2895816256444459343189041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15444353367703783163674885 2895816256444459343189041)
                      ·
                        rfl

theorem cell23_5639582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5639582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639582 prefixEnd_5639582 := by exact prefixLift 5639582
  have htrace : WordTrace (prefixWord ++ tailWord_5639582) baseStart_5639582 baseEnd_5639582 := by
    simpa [prefixWord, tailWord_5639582, baseEnd_5639582] using wordTrace_append hprefix tailTrace_5639582
  have hstable : (prefixWord ++ tailWord_5639582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639582).length < 2 ^ (prefixWord ++ tailWord_5639582).sum := by decide
  have hdescent : baseEnd_5639582 < baseStart_5639582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639584 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_5639584 : Nat := 118140960795 + 5639584 * 2 ^ 59
def prefixEnd_5639584 : Nat := 4983230072969 + 3 ^ 40 * 5639584 * 2
def baseEnd_5639584 : Nat := 965272427801922778454677

theorem tailTrace_5639584 : CollatzResearch.WordTrace tailWord_5639584 prefixEnd_5639584 965272427801922778454677 := by
  unfold tailWord_5639584
  simp only [CollatzResearch.WordTrace]
  refine ⟨102846263400378903555442903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137128351200505204740590537 102846263400378903555442903)
  ·
    refine ⟨154269395100568355333164355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102846263400378903555442903 154269395100568355333164355)
    ·
      refine ⟨231404092650852532999746533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154269395100568355333164355 231404092650852532999746533)
      ·
        refine ⟨43388267372034849937452475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231404092650852532999746533 43388267372034849937452475)
        ·
          refine ⟨65082401058052274906178713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43388267372034849937452475 65082401058052274906178713)
          ·
            refine ⟨48811800793539206179634035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65082401058052274906178713 48811800793539206179634035)
            ·
              refine ⟨73217701190308809269451053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48811800793539206179634035 73217701190308809269451053)
              ·
                refine ⟨27456637946365803476044145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73217701190308809269451053 27456637946365803476044145)
                ·
                  refine ⟨20592478459774352607033109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27456637946365803476044145 20592478459774352607033109)
                  ·
                    refine ⟨965272427801922778454677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20592478459774352607033109 965272427801922778454677)
                    ·
                      rfl

theorem cell23_5639584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_5639584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639584 prefixEnd_5639584 := by exact prefixLift 5639584
  have htrace : WordTrace (prefixWord ++ tailWord_5639584) baseStart_5639584 baseEnd_5639584 := by
    simpa [prefixWord, tailWord_5639584, baseEnd_5639584] using wordTrace_append hprefix tailTrace_5639584
  have hstable : (prefixWord ++ tailWord_5639584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639584).length < 2 ^ (prefixWord ++ tailWord_5639584).sum := by decide
  have hdescent : baseEnd_5639584 < baseStart_5639584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639608 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 4, 2, 2]
def baseStart_5639608 : Nat := 118140960795 + 5639608 * 2 ^ 59
def prefixEnd_5639608 : Nat := 4983230072969 + 3 ^ 40 * 5639608 * 2
def baseEnd_5639608 : Nat := 2895829606941476241463921

theorem tailTrace_5639608 : CollatzResearch.WordTrace tailWord_5639608 prefixEnd_5639608 2895829606941476241463921 := by
  unfold tailWord_5639608
  simp only [CollatzResearch.WordTrace]
  refine ⟨102846701076335429604879739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137128934768447239473172985 102846701076335429604879739)
  ·
    refine ⟨154270051614503144407319609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102846701076335429604879739 154270051614503144407319609)
    ·
      refine ⟨115702538710877358305489707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154270051614503144407319609 115702538710877358305489707)
      ·
        refine ⟨173553808066316037458234561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115702538710877358305489707 173553808066316037458234561)
        ·
          refine ⟨130165356049737028093675921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173553808066316037458234561 130165356049737028093675921)
          ·
            refine ⟨97624017037302771070256941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130165356049737028093675921 97624017037302771070256941)
            ·
              refine ⟨36609006388988539151346353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97624017037302771070256941 36609006388988539151346353)
              ·
                refine ⟨27456754791741404363509765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36609006388988539151346353 27456754791741404363509765)
                ·
                  refine ⟨5148141523451513318158081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27456754791741404363509765 5148141523451513318158081)
                  ·
                    refine ⟨3861106142588634988618561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5148141523451513318158081 3861106142588634988618561)
                    ·
                      refine ⟨2895829606941476241463921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3861106142588634988618561 2895829606941476241463921)
                      ·
                        rfl

theorem cell23_5639608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_5639608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639608 prefixEnd_5639608 := by exact prefixLift 5639608
  have htrace : WordTrace (prefixWord ++ tailWord_5639608) baseStart_5639608 baseEnd_5639608 := by
    simpa [prefixWord, tailWord_5639608, baseEnd_5639608] using wordTrace_append hprefix tailTrace_5639608
  have hstable : (prefixWord ++ tailWord_5639608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639608).length < 2 ^ (prefixWord ++ tailWord_5639608).sum := by decide
  have hdescent : baseEnd_5639608 < baseStart_5639608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639624 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_5639624 : Nat := 118140960795 + 5639624 * 2 ^ 59
def prefixEnd_5639624 : Nat := 4983230072969 + 3 ^ 40 * 5639624 * 2
def baseEnd_5639624 : Nat := 2895837822631948178863847

theorem tailTrace_5639624 : CollatzResearch.WordTrace tailWord_5639624 prefixEnd_5639624 2895837822631948178863847 := by
  unfold tailWord_5639624
  simp only [CollatzResearch.WordTrace]
  refine ⟨102846992860306446971170963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137129323813741929294894617 102846992860306446971170963)
  ·
    refine ⟨154270489290459670456756445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102846992860306446971170963 154270489290459670456756445)
    ·
      refine ⟨57851433483922376421283667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154270489290459670456756445 57851433483922376421283667)
      ·
        refine ⟨86777150225883564631925501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57851433483922376421283667 86777150225883564631925501)
        ·
          refine ⟨32541431334706336736972063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86777150225883564631925501 32541431334706336736972063)
          ·
            refine ⟨48812147002059505105458095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32541431334706336736972063 48812147002059505105458095)
            ·
              refine ⟨73218220503089257658187143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48812147002059505105458095 73218220503089257658187143)
              ·
                refine ⟨109827330754633886487280715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73218220503089257658187143 109827330754633886487280715)
                ·
                  refine ⟨164740996131950829730921073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109827330754633886487280715 164740996131950829730921073)
                  ·
                    refine ⟨123555747098963122298190805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164740996131950829730921073 123555747098963122298190805)
                    ·
                      refine ⟨2895837822631948178863847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123555747098963122298190805 2895837822631948178863847)
                      ·
                        rfl

theorem cell23_5639624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_5639624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639624 prefixEnd_5639624 := by exact prefixLift 5639624
  have htrace : WordTrace (prefixWord ++ tailWord_5639624) baseStart_5639624 baseEnd_5639624 := by
    simpa [prefixWord, tailWord_5639624, baseEnd_5639624] using wordTrace_append hprefix tailTrace_5639624
  have hstable : (prefixWord ++ tailWord_5639624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639624).length < 2 ^ (prefixWord ++ tailWord_5639624).sum := by decide
  have hdescent : baseEnd_5639624 < baseStart_5639624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639631 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 5]
def baseStart_5639631 : Nat := 118140960795 + 5639631 * 2 ^ 59
def prefixEnd_5639631 : Nat := 4983230072969 + 3 ^ 40 * 5639631 * 2
def baseEnd_5639631 : Nat := 321760157444058850164035

theorem tailTrace_5639631 : CollatzResearch.WordTrace tailWord_5639631 prefixEnd_5639631 321760157444058850164035 := by
  unfold tailWord_5639631
  simp only [CollatzResearch.WordTrace]
  refine ⟨205694241031587534137846747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137129494021058356091897831 205694241031587534137846747)
  ·
    refine ⟨308541361547381301206770121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205694241031587534137846747 308541361547381301206770121)
    ·
      refine ⟨231406021160535975905077591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308541361547381301206770121 231406021160535975905077591)
      ·
        refine ⟨347109031740803963857616387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231406021160535975905077591 347109031740803963857616387)
        ·
          refine ⟨520663547611205945786424581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347109031740803963857616387 520663547611205945786424581)
          ·
            refine ⟨97624415177101114834954609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 520663547611205945786424581 97624415177101114834954609)
            ·
              refine ⟨73218311382825836126215957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97624415177101114834954609 73218311382825836126215957)
              ·
                refine ⟨3432108346069961068416373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73218311382825836126215957 3432108346069961068416373)
                ·
                  refine ⟨321760157444058850164035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432108346069961068416373 321760157444058850164035)
                  ·
                    rfl

theorem cell23_5639631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 5].length) (baseStart_5639631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639631 prefixEnd_5639631 := by exact prefixLift 5639631
  have htrace : WordTrace (prefixWord ++ tailWord_5639631) baseStart_5639631 baseEnd_5639631 := by
    simpa [prefixWord, tailWord_5639631, baseEnd_5639631] using wordTrace_append hprefix tailTrace_5639631
  have hstable : (prefixWord ++ tailWord_5639631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639631).length < 2 ^ (prefixWord ++ tailWord_5639631).sum := by decide
  have hdescent : baseEnd_5639631 < baseStart_5639631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639642 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2]
def baseStart_5639642 : Nat := 118140960795 + 5639642 * 2 ^ 59
def prefixEnd_5639642 : Nat := 4983230072969 + 3 ^ 40 * 5639642 * 2
def baseEnd_5639642 : Nat := 2895847065283729108438765

theorem tailTrace_5639642 : CollatzResearch.WordTrace tailWord_5639642 prefixEnd_5639642 2895847065283729108438765 := by
  unfold tailWord_5639642
  simp only [CollatzResearch.WordTrace]
  refine ⟨51423660558636920754124295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137129761489698455344331453 51423660558636920754124295)
  ·
    refine ⟨77135490837955381131186443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51423660558636920754124295 77135490837955381131186443)
    ·
      refine ⟨115703236256933071696779665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77135490837955381131186443 115703236256933071696779665)
      ·
        refine ⟨86777427192699803772584749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115703236256933071696779665 86777427192699803772584749)
        ·
          refine ⟨32541535197262426414719281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86777427192699803772584749 32541535197262426414719281)
          ·
            refine ⟨24406151397946819811039461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32541535197262426414719281 24406151397946819811039461)
            ·
              refine ⟨4576153387115028714569899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24406151397946819811039461 4576153387115028714569899)
              ·
                refine ⟨6864230080672543071854849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576153387115028714569899 6864230080672543071854849)
                ·
                  refine ⟨5148172560504407303891137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6864230080672543071854849 5148172560504407303891137)
                  ·
                    refine ⟨3861129420378305477918353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5148172560504407303891137 3861129420378305477918353)
                    ·
                      refine ⟨2895847065283729108438765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3861129420378305477918353 2895847065283729108438765)
                      ·
                        rfl

theorem cell23_5639642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_5639642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639642 prefixEnd_5639642 := by exact prefixLift 5639642
  have htrace : WordTrace (prefixWord ++ tailWord_5639642) baseStart_5639642 baseEnd_5639642 := by
    simpa [prefixWord, tailWord_5639642, baseEnd_5639642] using wordTrace_append hprefix tailTrace_5639642
  have hstable : (prefixWord ++ tailWord_5639642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639642).length < 2 ^ (prefixWord ++ tailWord_5639642).sum := by decide
  have hdescent : baseEnd_5639642 < baseStart_5639642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639682 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_5639682 : Nat := 118140960795 + 5639682 * 2 ^ 59
def prefixEnd_5639682 : Nat := 4983230072969 + 3 ^ 40 * 5639682 * 2
def baseEnd_5639682 : Nat := 321763067167767661326509

theorem tailTrace_5639682 : CollatzResearch.WordTrace tailWord_5639682 prefixEnd_5639682 321763067167767661326509 := by
  unfold tailWord_5639682
  simp only [CollatzResearch.WordTrace]
  refine ⟨51424025288600692461988325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137130734102935179898635533 51424025288600692461988325)
  ·
    refine ⟨9642004741612629836622811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51424025288600692461988325 9642004741612629836622811)
    ·
      refine ⟨14463007112418944754934217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9642004741612629836622811 14463007112418944754934217)
      ·
        refine ⟨10847255334314208566200663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14463007112418944754934217 10847255334314208566200663)
        ·
          refine ⟨16270883001471312849300995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10847255334314208566200663 16270883001471312849300995)
          ·
            refine ⟨24406324502206969273951493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16270883001471312849300995 24406324502206969273951493)
            ·
              refine ⟨4576185844163806738865905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24406324502206969273951493 4576185844163806738865905)
              ·
                refine ⟨3432139383122855054149429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576185844163806738865905 3432139383122855054149429)
                ·
                  refine ⟨321763067167767661326509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432139383122855054149429 321763067167767661326509)
                  ·
                    rfl

theorem cell23_5639682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_5639682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639682 prefixEnd_5639682 := by exact prefixLift 5639682
  have htrace : WordTrace (prefixWord ++ tailWord_5639682) baseStart_5639682 baseEnd_5639682 := by
    simpa [prefixWord, tailWord_5639682, baseEnd_5639682] using wordTrace_append hprefix tailTrace_5639682
  have hstable : (prefixWord ++ tailWord_5639682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639682).length < 2 ^ (prefixWord ++ tailWord_5639682).sum := by decide
  have hdescent : baseEnd_5639682 < baseStart_5639682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639708 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_5639708 : Nat := 118140960795 + 5639708 * 2 ^ 59
def prefixEnd_5639708 : Nat := 4983230072969 + 3 ^ 40 * 5639708 * 2
def baseEnd_5639708 : Nat := 965293651668975283404487

theorem tailTrace_5639708 : CollatzResearch.WordTrace tailWord_5639708 prefixEnd_5639708 965293651668975283404487 := by
  unfold tailWord_5639708
  simp only [CollatzResearch.WordTrace]
  refine ⟨102848524726154288144199889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137131366301539050858933185 102848524726154288144199889)
  ·
    refine ⟨77136393544615716108149917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102848524726154288144199889 77136393544615716108149917)
    ·
      refine ⟨28926147579230893540556219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77136393544615716108149917 28926147579230893540556219)
      ·
        refine ⟨43389221368846340310834329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28926147579230893540556219 43389221368846340310834329)
        ·
          refine ⟨32541916026634755233125747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43389221368846340310834329 32541916026634755233125747)
          ·
            refine ⟨48812874039952132849688621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32541916026634755233125747 48812874039952132849688621)
            ·
              refine ⟨18304827764982049818633233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48812874039952132849688621 18304827764982049818633233)
              ·
                refine ⟨13728620823736537363974925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18304827764982049818633233 13728620823736537363974925)
                ·
                  refine ⟨5148232808901201511490597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13728620823736537363974925 5148232808901201511490597)
                  ·
                    refine ⟨965293651668975283404487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148232808901201511490597 965293651668975283404487)
                    ·
                      rfl

theorem cell23_5639708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_5639708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639708 prefixEnd_5639708 := by exact prefixLift 5639708
  have htrace : WordTrace (prefixWord ++ tailWord_5639708) baseStart_5639708 baseEnd_5639708 := by
    simpa [prefixWord, tailWord_5639708, baseEnd_5639708] using wordTrace_append hprefix tailTrace_5639708
  have hstable : (prefixWord ++ tailWord_5639708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639708).length < 2 ^ (prefixWord ++ tailWord_5639708).sum := by decide
  have hdescent : baseEnd_5639708 < baseStart_5639708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639715 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 4]
def baseStart_5639715 : Nat := 118140960795 + 5639715 * 2 ^ 59
def prefixEnd_5639715 : Nat := 4983230072969 + 3 ^ 40 * 5639715 * 2
def baseEnd_5639715 : Nat := 2895884549371507322825929

theorem tailTrace_5639715 : CollatzResearch.WordTrace tailWord_5639715 prefixEnd_5639715 2895884549371507322825929 := by
  unfold tailWord_5639715
  simp only [CollatzResearch.WordTrace]
  refine ⟨205697304763283216483904599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137131536508855477655936399 205697304763283216483904599)
  ·
    refine ⟨308545957144924824725856899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205697304763283216483904599 308545957144924824725856899)
    ·
      refine ⟨462818935717387237088785349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308545957144924824725856899 462818935717387237088785349)
      ·
        refine ⟨86778550447010106954147253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 462818935717387237088785349 86778550447010106954147253)
        ·
          refine ⟨8135489104407197526951305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86778550447010106954147253 8135489104407197526951305)
          ·
            refine ⟨6101616828305398145213479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8135489104407197526951305 6101616828305398145213479)
            ·
              refine ⟨9152425242458097217820219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101616828305398145213479 9152425242458097217820219)
              ·
                refine ⟨13728637863687145826730329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9152425242458097217820219 13728637863687145826730329)
                ·
                  refine ⟨10296478397765359370047747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13728637863687145826730329 10296478397765359370047747)
                  ·
                    refine ⟨15444717596648039055071621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10296478397765359370047747 15444717596648039055071621)
                    ·
                      refine ⟨2895884549371507322825929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15444717596648039055071621 2895884549371507322825929)
                      ·
                        rfl

theorem cell23_5639715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_5639715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639715 prefixEnd_5639715 := by exact prefixLift 5639715
  have htrace : WordTrace (prefixWord ++ tailWord_5639715) baseStart_5639715 baseEnd_5639715 := by
    simpa [prefixWord, tailWord_5639715, baseEnd_5639715] using wordTrace_append hprefix tailTrace_5639715
  have hstable : (prefixWord ++ tailWord_5639715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639715).length < 2 ^ (prefixWord ++ tailWord_5639715).sum := by decide
  have hdescent : baseEnd_5639715 < baseStart_5639715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639801 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_5639801 : Nat := 118140960795 + 5639801 * 2 ^ 59
def prefixEnd_5639801 : Nat := 4983230072969 + 3 ^ 40 * 5639801 * 2
def baseEnd_5639801 : Nat := 2895928708707793986350533

theorem tailTrace_5639801 : CollatzResearch.WordTrace tailWord_5639801 prefixEnd_5639801 2895928708707793986350533 := by
  unfold tailWord_5639801
  simp only [CollatzResearch.WordTrace]
  refine ⟨205700441440971653171535257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137133627627314435447690171 205700441440971653171535257)
  ·
    refine ⟨154275331080728739878651443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205700441440971653171535257 154275331080728739878651443)
    ·
      refine ⟨231412996621093109817977165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154275331080728739878651443 231412996621093109817977165)
      ·
        refine ⟨86779873732909916181741437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231412996621093109817977165 86779873732909916181741437)
        ·
          refine ⟨32542452649841218568153039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86779873732909916181741437 32542452649841218568153039)
          ·
            refine ⟨48813678974761827852229559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32542452649841218568153039 48813678974761827852229559)
            ·
              refine ⟨73220518462142741778344339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48813678974761827852229559 73220518462142741778344339)
              ·
                refine ⟨109830777693214112667516509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73220518462142741778344339 109830777693214112667516509)
                ·
                  refine ⟨41186541634955292250318691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109830777693214112667516509 41186541634955292250318691)
                  ·
                    refine ⟨61779812452432938375478037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41186541634955292250318691 61779812452432938375478037)
                    ·
                      refine ⟨2895928708707793986350533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61779812452432938375478037 2895928708707793986350533)
                      ·
                        rfl

theorem cell23_5639801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_5639801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639801 prefixEnd_5639801 := by exact prefixLift 5639801
  have htrace : WordTrace (prefixWord ++ tailWord_5639801) baseStart_5639801 baseEnd_5639801 := by
    simpa [prefixWord, tailWord_5639801, baseEnd_5639801] using wordTrace_append hprefix tailTrace_5639801
  have hstable : (prefixWord ++ tailWord_5639801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639801).length < 2 ^ (prefixWord ++ tailWord_5639801).sum := by decide
  have hdescent : baseEnd_5639801 < baseStart_5639801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639808 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_5639808 : Nat := 118140960795 + 5639808 * 2 ^ 59
def prefixEnd_5639808 : Nat := 4983230072969 + 3 ^ 40 * 5639808 * 2
def baseEnd_5639808 : Nat := 2895932303072375458963001

theorem tailTrace_5639808 : CollatzResearch.WordTrace tailWord_5639808 prefixEnd_5639808 2895932303072375458963001 := by
  unfold tailWord_5639808
  simp only [CollatzResearch.WordTrace]
  refine ⟨102850348375973146683520039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137133797834630862244693385 102850348375973146683520039)
  ·
    refine ⟨154275522563959720025280059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102850348375973146683520039 154275522563959720025280059)
    ·
      refine ⟨231413283845939580037920089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154275522563959720025280059 231413283845939580037920089)
      ·
        refine ⟨173559962884454685028440067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231413283845939580037920089 173559962884454685028440067)
        ·
          refine ⟨260339944326682027542660101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173559962884454685028440067 260339944326682027542660101)
          ·
            refine ⟨48813739561252880164248769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260339944326682027542660101 48813739561252880164248769)
            ·
              refine ⟨36610304670939660123186577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48813739561252880164248769 36610304670939660123186577)
              ·
                refine ⟨27457728503204745092389933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36610304670939660123186577 27457728503204745092389933)
                ·
                  refine ⟨10296648188701779409646225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27457728503204745092389933 10296648188701779409646225)
                  ·
                    refine ⟨7722486141526334557234669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10296648188701779409646225 7722486141526334557234669)
                    ·
                      refine ⟨2895932303072375458963001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7722486141526334557234669 2895932303072375458963001)
                      ·
                        rfl

theorem cell23_5639808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_5639808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639808 prefixEnd_5639808 := by exact prefixLift 5639808
  have htrace : WordTrace (prefixWord ++ tailWord_5639808) baseStart_5639808 baseEnd_5639808 := by
    simpa [prefixWord, tailWord_5639808, baseEnd_5639808] using wordTrace_append hprefix tailTrace_5639808
  have hstable : (prefixWord ++ tailWord_5639808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639808).length < 2 ^ (prefixWord ++ tailWord_5639808).sum := by decide
  have hdescent : baseEnd_5639808 < baseStart_5639808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639815 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 2, 4]
def baseStart_5639815 : Nat := 118140960795 + 5639815 * 2 ^ 59
def prefixEnd_5639815 : Nat := 4983230072969 + 3 ^ 40 * 5639815 * 2
def baseEnd_5639815 : Nat := 965311965812318977191823

theorem tailTrace_5639815 : CollatzResearch.WordTrace tailWord_5639815 prefixEnd_5639815 965311965812318977191823 := by
  unfold tailWord_5639815
  simp only [CollatzResearch.WordTrace]
  refine ⟨205700952062920933562544899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137133968041947289041696599 205700952062920933562544899)
  ·
    refine ⟨308551428094381400343817349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205700952062920933562544899 308551428094381400343817349)
    ·
      refine ⟨57853392767696512564465753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308551428094381400343817349 57853392767696512564465753)
      ·
        refine ⟨43390044575772384423349315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57853392767696512564465753 43390044575772384423349315)
        ·
          refine ⟨65085066863658576635023973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43390044575772384423349315 65085066863658576635023973)
          ·
            refine ⟨12203450036935983119066995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65085066863658576635023973 12203450036935983119066995)
            ·
              refine ⟨18305175055403974678600493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12203450036935983119066995 18305175055403974678600493)
              ·
                refine ⟨6864440645776490504475185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18305175055403974678600493 6864440645776490504475185)
                ·
                  refine ⟨5148330484332367878356389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6864440645776490504475185 5148330484332367878356389)
                  ·
                    refine ⟨965311965812318977191823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148330484332367878356389 965311965812318977191823)
                    ·
                      rfl

theorem cell23_5639815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_5639815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639815 prefixEnd_5639815 := by exact prefixLift 5639815
  have htrace : WordTrace (prefixWord ++ tailWord_5639815) baseStart_5639815 baseEnd_5639815 := by
    simpa [prefixWord, tailWord_5639815, baseEnd_5639815] using wordTrace_append hprefix tailTrace_5639815
  have hstable : (prefixWord ++ tailWord_5639815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639815).length < 2 ^ (prefixWord ++ tailWord_5639815).sum := by decide
  have hdescent : baseEnd_5639815 < baseStart_5639815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639818 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5639818 : Nat := 118140960795 + 5639818 * 2 ^ 59
def prefixEnd_5639818 : Nat := 4983230072969 + 3 ^ 40 * 5639818 * 2
def baseEnd_5639818 : Nat := 2895937437878920419837955

theorem tailTrace_5639818 : CollatzResearch.WordTrace tailWord_5639818 prefixEnd_5639818 2895937437878920419837955 := by
  unfold tailWord_5639818
  simp only [CollatzResearch.WordTrace]
  refine ⟨51425265370477516268726027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137134040987940043383269405 51425265370477516268726027)
  ·
    refine ⟨77137898055716274403089041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51425265370477516268726027 77137898055716274403089041)
    ·
      refine ⟨57853423541787205802316781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77137898055716274403089041 57853423541787205802316781)
      ·
        refine ⟨21695033828170202175868793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57853423541787205802316781 21695033828170202175868793)
        ·
          refine ⟨16271275371127651631901595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21695033828170202175868793 16271275371127651631901595)
          ·
            refine ⟨24406913056691477447852393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16271275371127651631901595 24406913056691477447852393)
            ·
              refine ⟨18305184792518608085889295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24406913056691477447852393 18305184792518608085889295)
              ·
                refine ⟨27457777188777912128833943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18305184792518608085889295 27457777188777912128833943)
                ·
                  refine ⟨41186665783166868193250915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27457777188777912128833943 41186665783166868193250915)
                  ·
                    refine ⟨61779998674750302289876373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41186665783166868193250915 61779998674750302289876373)
                    ·
                      refine ⟨2895937437878920419837955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61779998674750302289876373 2895937437878920419837955)
                      ·
                        rfl

theorem cell23_5639818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5639818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639818 prefixEnd_5639818 := by exact prefixLift 5639818
  have htrace : WordTrace (prefixWord ++ tailWord_5639818) baseStart_5639818 baseEnd_5639818 := by
    simpa [prefixWord, tailWord_5639818, baseEnd_5639818] using wordTrace_append hprefix tailTrace_5639818
  have hstable : (prefixWord ++ tailWord_5639818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639818).length < 2 ^ (prefixWord ++ tailWord_5639818).sum := by decide
  have hdescent : baseEnd_5639818 < baseStart_5639818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639822 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5639822 : Nat := 118140960795 + 5639822 * 2 ^ 59
def prefixEnd_5639822 : Nat := 4983230072969 + 3 ^ 40 * 5639822 * 2
def baseEnd_5639822 : Nat := 2895939491801538404187937

theorem tailTrace_5639822 : CollatzResearch.WordTrace tailWord_5639822 prefixEnd_5639822 2895939491801538404187937 := by
  unfold tailWord_5639822
  simp only [CollatzResearch.WordTrace]
  refine ⟨25712650921736946719756215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137134138249263715838699813 25712650921736946719756215)
  ·
    refine ⟨38568976382605420079634323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25712650921736946719756215 38568976382605420079634323)
    ·
      refine ⟨57853464573908130119451485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38568976382605420079634323 57853464573908130119451485)
      ·
        refine ⟨21695049215215548794794307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57853464573908130119451485 21695049215215548794794307)
        ·
          refine ⟨32542573822823323192191461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21695049215215548794794307 32542573822823323192191461)
          ·
            refine ⟨6101732591779373098535899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32542573822823323192191461 6101732591779373098535899)
            ·
              refine ⟨9152598887669059647803849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101732591779373098535899 9152598887669059647803849)
              ·
                refine ⟨6864449165751794735852887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9152598887669059647803849 6864449165751794735852887)
                ·
                  refine ⟨10296673748627692103779331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6864449165751794735852887 10296673748627692103779331)
                  ·
                    refine ⟨15445010622941538155668997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10296673748627692103779331 15445010622941538155668997)
                    ·
                      refine ⟨2895939491801538404187937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15445010622941538155668997 2895939491801538404187937)
                      ·
                        rfl

theorem cell23_5639822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5639822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639822 prefixEnd_5639822 := by exact prefixLift 5639822
  have htrace : WordTrace (prefixWord ++ tailWord_5639822) baseStart_5639822 baseEnd_5639822 := by
    simpa [prefixWord, tailWord_5639822, baseEnd_5639822] using wordTrace_append hprefix tailTrace_5639822
  have hstable : (prefixWord ++ tailWord_5639822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639822).length < 2 ^ (prefixWord ++ tailWord_5639822).sum := by decide
  have hdescent : baseEnd_5639822 < baseStart_5639822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639839 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5639839 : Nat := 118140960795 + 5639839 * 2 ^ 59
def prefixEnd_5639839 : Nat := 4983230072969 + 3 ^ 40 * 5639839 * 2
def baseEnd_5639839 : Nat := 2895948220972664837675359

theorem tailTrace_5639839 : CollatzResearch.WordTrace tailWord_5639839 prefixEnd_5639839 2895948220972664837675359 := by
  unfold tailWord_5639839
  simp only [CollatzResearch.WordTrace]
  refine ⟨205701827414833985661418571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137134551609889323774279047 205701827414833985661418571)
  ·
    refine ⟨308552741122250978492127857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205701827414833985661418571 308552741122250978492127857)
    ·
      refine ⟨231414555841688233869095893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308552741122250978492127857 231414555841688233869095893)
      ·
        refine ⟨5423778652539567981306935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 231414555841688233869095893 5423778652539567981306935)
        ·
          refine ⟨8135667978809351971960403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5423778652539567981306935 8135667978809351971960403)
          ·
            refine ⟨12203501968214027957940605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135667978809351971960403 12203501968214027957940605)
            ·
              refine ⟨4576313238080260484227727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12203501968214027957940605 4576313238080260484227727)
              ·
                refine ⟨6864469857120390726341591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576313238080260484227727 6864469857120390726341591)
                ·
                  refine ⟨10296704785680586089512387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6864469857120390726341591 10296704785680586089512387)
                  ·
                    refine ⟨15445057178520879134268581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10296704785680586089512387 15445057178520879134268581)
                    ·
                      refine ⟨2895948220972664837675359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15445057178520879134268581 2895948220972664837675359)
                      ·
                        rfl

theorem cell23_5639839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5639839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639839 prefixEnd_5639839 := by exact prefixLift 5639839
  have htrace : WordTrace (prefixWord ++ tailWord_5639839) baseStart_5639839 baseEnd_5639839 := by
    simpa [prefixWord, tailWord_5639839, baseEnd_5639839] using wordTrace_append hprefix tailTrace_5639839
  have hstable : (prefixWord ++ tailWord_5639839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639839).length < 2 ^ (prefixWord ++ tailWord_5639839).sum := by decide
  have hdescent : baseEnd_5639839 < baseStart_5639839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639862 : List Nat := [5, 1, 3, 1, 1, 3, 1, 8]
def baseStart_5639862 : Nat := 118140960795 + 5639862 * 2 ^ 59
def prefixEnd_5639862 : Nat := 4983230072969 + 3 ^ 40 * 5639862 * 2
def baseEnd_5639862 : Nat := 107257778926952527692139

theorem tailTrace_5639862 : CollatzResearch.WordTrace tailWord_5639862 prefixEnd_5639862 107257778926952527692139 := by
  unfold tailWord_5639862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856416643359416286844115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137135110862500440393003893 12856416643359416286844115)
  ·
    refine ⟨19284624965039124430266173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12856416643359416286844115 19284624965039124430266173)
    ·
      refine ⟨7231734361889671661349815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19284624965039124430266173 7231734361889671661349815)
      ·
        refine ⟨10847601542834507492024723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7231734361889671661349815 10847601542834507492024723)
        ·
          refine ⟨16271402314251761238037085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10847601542834507492024723 16271402314251761238037085)
          ·
            refine ⟨6101775867844410464263907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16271402314251761238037085 6101775867844410464263907)
            ·
              refine ⟨9152663801766615696395861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101775867844410464263907 9152663801766615696395861)
              ·
                refine ⟨107257778926952527692139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9152663801766615696395861 107257778926952527692139)
                ·
                  rfl

theorem cell23_5639862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_5639862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639862 prefixEnd_5639862 := by exact prefixLift 5639862
  have htrace : WordTrace (prefixWord ++ tailWord_5639862) baseStart_5639862 baseEnd_5639862 := by
    simpa [prefixWord, tailWord_5639862, baseEnd_5639862] using wordTrace_append hprefix tailTrace_5639862
  have hstable : (prefixWord ++ tailWord_5639862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639862).length < 2 ^ (prefixWord ++ tailWord_5639862).sum := by decide
  have hdescent : baseEnd_5639862 < baseStart_5639862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639865 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 3, 3, 2]
def baseStart_5639865 : Nat := 118140960795 + 5639865 * 2 ^ 59
def prefixEnd_5639865 : Nat := 4983230072969 + 3 ^ 40 * 5639865 * 2
def baseEnd_5639865 : Nat := 2895961571469681735950239

theorem tailTrace_5639865 : CollatzResearch.WordTrace tailWord_5639865 prefixEnd_5639865 2895961571469681735950239 := by
  unfold tailWord_5639865
  simp only [CollatzResearch.WordTrace]
  refine ⟨205702775712739792101865049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137135183808493194734576699 205702775712739792101865049)
  ·
    refine ⟨154277081784554844076398787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205702775712739792101865049 154277081784554844076398787)
    ·
      refine ⟨231415622676832266114598181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154277081784554844076398787 231415622676832266114598181)
      ·
        refine ⟨43390429251906049896487159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231415622676832266114598181 43390429251906049896487159)
        ·
          refine ⟨65085643877859074844730739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43390429251906049896487159 65085643877859074844730739)
          ·
            refine ⟨97628465816788612267096109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65085643877859074844730739 97628465816788612267096109)
            ·
              refine ⟨36610674681295729600161041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97628465816788612267096109 36610674681295729600161041)
              ·
                refine ⟨27458006010971797200120781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36610674681295729600161041 27458006010971797200120781)
                ·
                  refine ⟨10296752254114423950045293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27458006010971797200120781 10296752254114423950045293)
                  ·
                    refine ⟨3861282095292908981266985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10296752254114423950045293 3861282095292908981266985)
                    ·
                      refine ⟨2895961571469681735950239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3861282095292908981266985 2895961571469681735950239)
                      ·
                        rfl

theorem cell23_5639865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_5639865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639865 prefixEnd_5639865 := by exact prefixLift 5639865
  have htrace : WordTrace (prefixWord ++ tailWord_5639865) baseStart_5639865 baseEnd_5639865 := by
    simpa [prefixWord, tailWord_5639865, baseEnd_5639865] using wordTrace_append hprefix tailTrace_5639865
  have hstable : (prefixWord ++ tailWord_5639865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639865).length < 2 ^ (prefixWord ++ tailWord_5639865).sum := by decide
  have hdescent : baseEnd_5639865 < baseStart_5639865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639891 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_5639891 : Nat := 118140960795 + 5639891 * 2 ^ 59
def prefixEnd_5639891 : Nat := 4983230072969 + 3 ^ 40 * 5639891 * 2
def baseEnd_5639891 : Nat := 2895974921966698634225119

theorem tailTrace_5639891 : CollatzResearch.WordTrace tailWord_5639891 prefixEnd_5639891 2895974921966698634225119 := by
  unfold tailWord_5639891
  simp only [CollatzResearch.WordTrace]
  refine ⟨205703724010645598542311527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137135816007097065694874351 205703724010645598542311527)
  ·
    refine ⟨308555586015968397813467291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205703724010645598542311527 308555586015968397813467291)
    ·
      refine ⟨462833379023952596720200937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308555586015968397813467291 462833379023952596720200937)
      ·
        refine ⟨347125034267964447540150703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462833379023952596720200937 347125034267964447540150703)
        ·
          refine ⟨520687551401946671310226055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347125034267964447540150703 520687551401946671310226055)
          ·
            refine ⟨781031327102920006965339083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520687551401946671310226055 781031327102920006965339083)
            ·
              refine ⟨1171546990654380010448008625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781031327102920006965339083 1171546990654380010448008625)
              ·
                refine ⟨878660242990785007836006469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1171546990654380010448008625 878660242990785007836006469)
                ·
                  refine ⟨164748795560772188969251213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878660242990785007836006469 164748795560772188969251213)
                  ·
                    refine ⟨61780798335289570863469205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164748795560772188969251213 61780798335289570863469205)
                    ·
                      refine ⟨2895974921966698634225119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61780798335289570863469205 2895974921966698634225119)
                      ·
                        rfl

theorem cell23_5639891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_5639891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639891 prefixEnd_5639891 := by exact prefixLift 5639891
  have htrace : WordTrace (prefixWord ++ tailWord_5639891) baseStart_5639891 baseEnd_5639891 := by
    simpa [prefixWord, tailWord_5639891, baseEnd_5639891] using wordTrace_append hprefix tailTrace_5639891
  have hstable : (prefixWord ++ tailWord_5639891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639891).length < 2 ^ (prefixWord ++ tailWord_5639891).sum := by decide
  have hdescent : baseEnd_5639891 < baseStart_5639891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639895 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 1, 4, 2]
def baseStart_5639895 : Nat := 118140960795 + 5639895 * 2 ^ 59
def prefixEnd_5639895 : Nat := 4983230072969 + 3 ^ 40 * 5639895 * 2
def baseEnd_5639895 : Nat := 2895976975889316618575101

theorem tailTrace_5639895 : CollatzResearch.WordTrace tailWord_5639895 prefixEnd_5639895 2895976975889316618575101 := by
  unfold tailWord_5639895
  simp only [CollatzResearch.WordTrace]
  refine ⟨205703869902631107225457139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137135913268420738150304759 205703869902631107225457139)
  ·
    refine ⟨308555804853946660838185709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205703869902631107225457139 308555804853946660838185709)
    ·
      refine ⟨115708426820229997814319641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308555804853946660838185709 115708426820229997814319641)
      ·
        refine ⟨86781320115172498360739731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115708426820229997814319641 86781320115172498360739731)
        ·
          refine ⟨130171980172758747541109597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86781320115172498360739731 130171980172758747541109597)
          ·
            refine ⟨48814492564784530327916099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130171980172758747541109597 48814492564784530327916099)
            ·
              refine ⟨73221738847176795491874149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48814492564784530327916099 73221738847176795491874149)
              ·
                refine ⟨13729076033845649154726403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73221738847176795491874149 13729076033845649154726403)
                ·
                  refine ⟨20593614050768473732089605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13729076033845649154726403 20593614050768473732089605)
                  ·
                    refine ⟨3861302634519088824766801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20593614050768473732089605 3861302634519088824766801)
                    ·
                      refine ⟨2895976975889316618575101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3861302634519088824766801 2895976975889316618575101)
                      ·
                        rfl

theorem cell23_5639895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_5639895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639895 prefixEnd_5639895 := by exact prefixLift 5639895
  have htrace : WordTrace (prefixWord ++ tailWord_5639895) baseStart_5639895 baseEnd_5639895 := by
    simpa [prefixWord, tailWord_5639895, baseEnd_5639895] using wordTrace_append hprefix tailTrace_5639895
  have hstable : (prefixWord ++ tailWord_5639895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639895).length < 2 ^ (prefixWord ++ tailWord_5639895).sum := by decide
  have hdescent : baseEnd_5639895 < baseStart_5639895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639908 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_5639908 : Nat := 118140960795 + 5639908 * 2 ^ 59
def prefixEnd_5639908 : Nat := 4983230072969 + 3 ^ 40 * 5639908 * 2
def baseEnd_5639908 : Nat := 2895983651137825067712541

theorem tailTrace_5639908 : CollatzResearch.WordTrace tailWord_5639908 prefixEnd_5639908 2895983651137825067712541 := by
  unfold tailWord_5639908
  simp only [CollatzResearch.WordTrace]
  refine ⟨102852172025792005222840189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137136229367722673630453585 102852172025792005222840189)
  ·
    refine ⟨38569564509672001958565071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102852172025792005222840189 38569564509672001958565071)
    ·
      refine ⟨57854346764508002937847607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38569564509672001958565071 57854346764508002937847607)
      ·
        refine ⟨86781520146762004406771411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57854346764508002937847607 86781520146762004406771411)
        ·
          refine ⟨130172280220143006610157117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86781520146762004406771411 130172280220143006610157117)
          ·
            refine ⟨48814605082553627478808919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130172280220143006610157117 48814605082553627478808919)
            ·
              refine ⟨73221907623830441218213379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48814605082553627478808919 73221907623830441218213379)
              ·
                refine ⟨109832861435745661827320069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73221907623830441218213379 109832861435745661827320069)
                ·
                  refine ⟨20593661519202311592622513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109832861435745661827320069 20593661519202311592622513)
                  ·
                    refine ⟨15445246139401733694466885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20593661519202311592622513 15445246139401733694466885)
                    ·
                      refine ⟨2895983651137825067712541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15445246139401733694466885 2895983651137825067712541)
                      ·
                        rfl

theorem cell23_5639908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_5639908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639908 prefixEnd_5639908 := by exact prefixLift 5639908
  have htrace : WordTrace (prefixWord ++ tailWord_5639908) baseStart_5639908 baseEnd_5639908 := by
    simpa [prefixWord, tailWord_5639908, baseEnd_5639908] using wordTrace_append hprefix tailTrace_5639908
  have hstable : (prefixWord ++ tailWord_5639908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639908).length < 2 ^ (prefixWord ++ tailWord_5639908).sum := by decide
  have hdescent : baseEnd_5639908 < baseStart_5639908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639928 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_5639928 : Nat := 118140960795 + 5639928 * 2 ^ 59
def prefixEnd_5639928 : Nat := 4983230072969 + 3 ^ 40 * 5639928 * 2
def baseEnd_5639928 : Nat := 2895993920750914989462449

theorem tailTrace_5639928 : CollatzResearch.WordTrace tailWord_5639928 prefixEnd_5639928 2895993920750914989462449 := by
  unfold tailWord_5639928
  simp only [CollatzResearch.WordTrace]
  refine ⟨102852536755755776930704219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137136715674341035907605625 102852536755755776930704219)
  ·
    refine ⟨154278805133633665396056329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102852536755755776930704219 154278805133633665396056329)
    ·
      refine ⟨115709103850225249047042247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154278805133633665396056329 115709103850225249047042247)
      ·
        refine ⟨173563655775337873570563371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115709103850225249047042247 173563655775337873570563371)
        ·
          refine ⟨260345483663006810355845057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173563655775337873570563371 260345483663006810355845057)
          ·
            refine ⟨195259112747255107766883793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260345483663006810355845057 195259112747255107766883793)
            ·
              refine ⟨146444334560441330825162845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195259112747255107766883793 146444334560441330825162845)
              ·
                refine ⟨54916625460165499059436067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146444334560441330825162845 54916625460165499059436067)
                ·
                  refine ⟨82374938190248248589154101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54916625460165499059436067 82374938190248248589154101)
                  ·
                    refine ⟨7722650455335773305233197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82374938190248248589154101 7722650455335773305233197)
                    ·
                      refine ⟨2895993920750914989462449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7722650455335773305233197 2895993920750914989462449)
                      ·
                        rfl

theorem cell23_5639928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_5639928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639928 prefixEnd_5639928 := by exact prefixLift 5639928
  have htrace : WordTrace (prefixWord ++ tailWord_5639928) baseStart_5639928 baseEnd_5639928 := by
    simpa [prefixWord, tailWord_5639928, baseEnd_5639928] using wordTrace_append hprefix tailTrace_5639928
  have hstable : (prefixWord ++ tailWord_5639928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639928).length < 2 ^ (prefixWord ++ tailWord_5639928).sum := by decide
  have hdescent : baseEnd_5639928 < baseStart_5639928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5639948 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_5639948 : Nat := 118140960795 + 5639948 * 2 ^ 59
def prefixEnd_5639948 : Nat := 4983230072969 + 3 ^ 40 * 5639948 * 2
def baseEnd_5639948 : Nat := 965334730121334970404119

theorem tailTrace_5639948 : CollatzResearch.WordTrace tailWord_5639948 prefixEnd_5639948 965334730121334970404119 := by
  unfold tailWord_5639948
  simp only [CollatzResearch.WordTrace]
  refine ⟨102852901485719548638568249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137137201980959398184757665 102852901485719548638568249)
  ·
    refine ⟨77139676114289661478926187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102852901485719548638568249 77139676114289661478926187)
    ·
      refine ⟨115709514171434492218389281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77139676114289661478926187 115709514171434492218389281)
      ·
        refine ⟨86782135628575869163791961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115709514171434492218389281 86782135628575869163791961)
        ·
          refine ⟨65086601721431901872843971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86782135628575869163791961 65086601721431901872843971)
          ·
            refine ⟨97629902582147852809265957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65086601721431901872843971 97629902582147852809265957)
            ·
              refine ⟨18305606734152722401737367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97629902582147852809265957 18305606734152722401737367)
              ·
                refine ⟨27458410101229083602606051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18305606734152722401737367 27458410101229083602606051)
                ·
                  refine ⟨41187615151843625403909077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27458410101229083602606051 41187615151843625403909077)
                  ·
                    refine ⟨965334730121334970404119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41187615151843625403909077 965334730121334970404119)
                    ·
                      rfl

theorem cell23_5639948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_5639948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5639948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5639948 prefixEnd_5639948 := by exact prefixLift 5639948
  have htrace : WordTrace (prefixWord ++ tailWord_5639948) baseStart_5639948 baseEnd_5639948 := by
    simpa [prefixWord, tailWord_5639948, baseEnd_5639948] using wordTrace_append hprefix tailTrace_5639948
  have hstable : (prefixWord ++ tailWord_5639948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5639948).length < 2 ^ (prefixWord ++ tailWord_5639948).sum := by decide
  have hdescent : baseEnd_5639948 < baseStart_5639948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5639948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640025 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 6]
def baseStart_5640025 : Nat := 118140960795 + 5640025 * 2 ^ 59
def prefixEnd_5640025 : Nat := 4983230072969 + 3 ^ 40 * 5640025 * 2
def baseEnd_5640025 : Nat := 321782636486044567772167

theorem tailTrace_5640025 : CollatzResearch.WordTrace tailWord_5640025 prefixEnd_5640025 321782636486044567772167 := by
  unfold tailWord_5640025
  simp only [CollatzResearch.WordTrace]
  refine ⟨205708611392160139427689529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137139074261440092951793019 205708611392160139427689529)
  ·
    refine ⟨154281458544120104570767147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205708611392160139427689529 154281458544120104570767147)
    ·
      refine ⟨231422187816180156856150721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154281458544120104570767147 231422187816180156856150721)
      ·
        refine ⟨173566640862135117642113041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231422187816180156856150721 173566640862135117642113041)
        ·
          refine ⟨130174980646601338231584781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173566640862135117642113041 130174980646601338231584781)
          ·
            refine ⟨48815617742475501836844293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130174980646601338231584781 48815617742475501836844293)
            ·
              refine ⟨9152928326714156594408305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48815617742475501836844293 9152928326714156594408305)
              ·
                refine ⟨6864696245035617445806229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9152928326714156594408305 6864696245035617445806229)
                ·
                  refine ⟨321782636486044567772167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6864696245035617445806229 321782636486044567772167)
                  ·
                    rfl

theorem cell23_5640025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_5640025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640025 prefixEnd_5640025 := by exact prefixLift 5640025
  have htrace : WordTrace (prefixWord ++ tailWord_5640025) baseStart_5640025 baseEnd_5640025 := by
    simpa [prefixWord, tailWord_5640025, baseEnd_5640025] using wordTrace_append hprefix tailTrace_5640025
  have hstable : (prefixWord ++ tailWord_5640025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640025).length < 2 ^ (prefixWord ++ tailWord_5640025).sum := by decide
  have hdescent : baseEnd_5640025 < baseStart_5640025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640048 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_5640048 : Nat := 118140960795 + 5640048 * 2 ^ 59
def prefixEnd_5640048 : Nat := 4983230072969 + 3 ^ 40 * 5640048 * 2
def baseEnd_5640048 : Nat := 2896055538429454519961897

theorem tailTrace_5640048 : CollatzResearch.WordTrace tailWord_5640048 prefixEnd_5640048 2896055538429454519961897 := by
  unfold tailWord_5640048
  simp only [CollatzResearch.WordTrace]
  refine ⟨102854725135538407177888399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137139633514051209570517865 102854725135538407177888399)
  ·
    refine ⟨154282087703307610766832599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102854725135538407177888399 154282087703307610766832599)
    ·
      refine ⟨231423131554961416150248899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154282087703307610766832599 231423131554961416150248899)
      ·
        refine ⟨347134697332442124225373349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231423131554961416150248899 347134697332442124225373349)
        ·
          refine ⟨65087755749832898292257503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347134697332442124225373349 65087755749832898292257503)
          ·
            refine ⟨97631633624749347438386255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65087755749832898292257503 97631633624749347438386255)
            ·
              refine ⟨146447450437124021157579383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97631633624749347438386255 146447450437124021157579383)
              ·
                refine ⟨219671175655686031736369075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146447450437124021157579383 219671175655686031736369075)
                ·
                  refine ⟨329506763483529047604553613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219671175655686031736369075 329506763483529047604553613)
                  ·
                    refine ⟨123565036306323392851707605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329506763483529047604553613 123565036306323392851707605)
                    ·
                      refine ⟨2896055538429454519961897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123565036306323392851707605 2896055538429454519961897)
                      ·
                        rfl

theorem cell23_5640048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_5640048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640048 prefixEnd_5640048 := by exact prefixLift 5640048
  have htrace : WordTrace (prefixWord ++ tailWord_5640048) baseStart_5640048 baseEnd_5640048 := by
    simpa [prefixWord, tailWord_5640048, baseEnd_5640048] using wordTrace_append hprefix tailTrace_5640048
  have hstable : (prefixWord ++ tailWord_5640048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640048).length < 2 ^ (prefixWord ++ tailWord_5640048).sum := by decide
  have hdescent : baseEnd_5640048 < baseStart_5640048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640105 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_5640105 : Nat := 118140960795 + 5640105 * 2 ^ 59
def prefixEnd_5640105 : Nat := 4983230072969 + 3 ^ 40 * 5640105 * 2
def baseEnd_5640105 : Nat := 2896084806826760796949135

theorem tailTrace_5640105 : CollatzResearch.WordTrace tailWord_5640105 prefixEnd_5640105 2896084806826760796949135 := by
  unfold tailWord_5640105
  simp only [CollatzResearch.WordTrace]
  refine ⟨205711529231870313090601769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137141019487913542060401179 205711529231870313090601769)
  ·
    refine ⟨154283646923902734817951327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205711529231870313090601769 154283646923902734817951327)
    ·
      refine ⟨231425470385854102226926991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154283646923902734817951327 231425470385854102226926991)
      ·
        refine ⟨347138205578781153340390487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231425470385854102226926991 347138205578781153340390487)
        ·
          refine ⟨520707308368171730010585731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347138205578781153340390487 520707308368171730010585731)
          ·
            refine ⟨781060962552257595015878597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520707308368171730010585731 781060962552257595015878597)
            ·
              refine ⟨146448930478548299065477237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 781060962552257595015878597 146448930478548299065477237)
              ·
                refine ⟨13729587232363903037388491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146448930478548299065477237 13729587232363903037388491)
                ·
                  refine ⟨20594380848545854556082737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13729587232363903037388491 20594380848545854556082737)
                  ·
                    refine ⟨15445785636409390917062053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20594380848545854556082737 15445785636409390917062053)
                    ·
                      refine ⟨2896084806826760796949135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15445785636409390917062053 2896084806826760796949135)
                      ·
                        rfl

theorem cell23_5640105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_5640105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640105 prefixEnd_5640105 := by exact prefixLift 5640105
  have htrace : WordTrace (prefixWord ++ tailWord_5640105) baseStart_5640105 baseEnd_5640105 := by
    simpa [prefixWord, tailWord_5640105, baseEnd_5640105] using wordTrace_append hprefix tailTrace_5640105
  have hstable : (prefixWord ++ tailWord_5640105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640105).length < 2 ^ (prefixWord ++ tailWord_5640105).sum := by decide
  have hdescent : baseEnd_5640105 < baseStart_5640105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640143 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 1, 2, 2]
def baseStart_5640143 : Nat := 118140960795 + 5640143 * 2 ^ 59
def prefixEnd_5640143 : Nat := 4983230072969 + 3 ^ 40 * 5640143 * 2
def baseEnd_5640143 : Nat := 2896104319091631648273961

theorem tailTrace_5640143 : CollatzResearch.WordTrace tailWord_5640143 prefixEnd_5640143 2896104319091631648273961 := by
  unfold tailWord_5640143
  simp only [CollatzResearch.WordTrace]
  refine ⟨205712915205732645580485083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137141943470488430386990055 205712915205732645580485083)
  ·
    refine ⟨308569372808598968370727625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205712915205732645580485083 308569372808598968370727625)
    ·
      refine ⟨231427029606449226278045719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308569372808598968370727625 231427029606449226278045719)
      ·
        refine ⟨347140544409673839417068579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231427029606449226278045719 347140544409673839417068579)
        ·
          refine ⟨520710816614510759125602869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347140544409673839417068579 520710816614510759125602869)
          ·
            refine ⟨48816639057610383668025269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 520710816614510759125602869 48816639057610383668025269)
            ·
              refine ⟨4576559911650973468877369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48816639057610383668025269 4576559911650973468877369)
              ·
                refine ⟨3432419933738230101658027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576559911650973468877369 3432419933738230101658027)
                ·
                  refine ⟨5148629900607345152487041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432419933738230101658027 5148629900607345152487041)
                  ·
                    refine ⟨3861472425455508864365281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5148629900607345152487041 3861472425455508864365281)
                    ·
                      refine ⟨2896104319091631648273961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3861472425455508864365281 2896104319091631648273961)
                      ·
                        rfl

theorem cell23_5640143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 2, 2].length) (baseStart_5640143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640143 prefixEnd_5640143 := by exact prefixLift 5640143
  have htrace : WordTrace (prefixWord ++ tailWord_5640143) baseStart_5640143 baseEnd_5640143 := by
    simpa [prefixWord, tailWord_5640143, baseEnd_5640143] using wordTrace_append hprefix tailTrace_5640143
  have hstable : (prefixWord ++ tailWord_5640143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640143).length < 2 ^ (prefixWord ++ tailWord_5640143).sum := by decide
  have hdescent : baseEnd_5640143 < baseStart_5640143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640153 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 2, 4]
def baseStart_5640153 : Nat := 118140960795 + 5640153 * 2 ^ 59
def prefixEnd_5640153 : Nat := 4983230072969 + 3 ^ 40 * 5640153 * 2
def baseEnd_5640153 : Nat := 965369817966058869716305

theorem tailTrace_5640153 : CollatzResearch.WordTrace tailWord_5640153 prefixEnd_5640153 965369817966058869716305 := by
  unfold tailWord_5640153
  simp only [CollatzResearch.WordTrace]
  refine ⟨205713279935696417288349113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137142186623797611525566075 205713279935696417288349113)
  ·
    refine ⟨154284959951772312966261835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205713279935696417288349113 154284959951772312966261835)
    ·
      refine ⟨231427439927658469449392753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154284959951772312966261835 231427439927658469449392753)
      ·
        refine ⟨173570579945743852087044565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231427439927658469449392753 173570579945743852087044565)
        ·
          refine ⟨4068060467478371533290107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173570579945743852087044565 4068060467478371533290107)
          ·
            refine ⟨6102090701217557299935161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068060467478371533290107 6102090701217557299935161)
            ·
              refine ⟨4576568025913167974951371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102090701217557299935161 4576568025913167974951371)
              ·
                refine ⟨6864852038869751962427057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576568025913167974951371 6864852038869751962427057)
                ·
                  refine ⟨5148639029152313971820293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6864852038869751962427057 5148639029152313971820293)
                  ·
                    refine ⟨965369817966058869716305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148639029152313971820293 965369817966058869716305)
                    ·
                      rfl

theorem cell23_5640153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 4].length) (baseStart_5640153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640153 prefixEnd_5640153 := by exact prefixLift 5640153
  have htrace : WordTrace (prefixWord ++ tailWord_5640153) baseStart_5640153 baseEnd_5640153 := by
    simpa [prefixWord, tailWord_5640153, baseEnd_5640153] using wordTrace_append hprefix tailTrace_5640153
  have hstable : (prefixWord ++ tailWord_5640153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640153).length < 2 ^ (prefixWord ++ tailWord_5640153).sum := by decide
  have hdescent : baseEnd_5640153 < baseStart_5640153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640195 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4]
def baseStart_5640195 : Nat := 118140960795 + 5640195 * 2 ^ 59
def prefixEnd_5640195 : Nat := 4983230072969 + 3 ^ 40 * 5640195 * 2
def baseEnd_5640195 : Nat := 2896131020085665444823721

theorem tailTrace_5640195 : CollatzResearch.WordTrace tailWord_5640195 prefixEnd_5640195 2896131020085665444823721 := by
  unfold tailWord_5640195
  simp only [CollatzResearch.WordTrace]
  refine ⟨205714811801544258461378039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137143207867696172307585359 205714811801544258461378039)
  ·
    refine ⟨308572217702316387692067059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205714811801544258461378039 308572217702316387692067059)
    ·
      refine ⟨462858326553474581538100589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308572217702316387692067059 462858326553474581538100589)
      ·
        refine ⟨173571872457552968076787721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462858326553474581538100589 173571872457552968076787721)
        ·
          refine ⟨130178904343164726057590791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173571872457552968076787721 130178904343164726057590791)
          ·
            refine ⟨195268356514747089086386187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130178904343164726057590791 195268356514747089086386187)
            ·
              refine ⟨292902534772120633629579281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195268356514747089086386187 292902534772120633629579281)
              ·
                refine ⟨219676901079090475222184461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292902534772120633629579281 219676901079090475222184461)
                ·
                  refine ⟨82378837904658928208319173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219676901079090475222184461 82378837904658928208319173)
                  ·
                    refine ⟨15446032107123549039059845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82378837904658928208319173 15446032107123549039059845)
                    ·
                      refine ⟨2896131020085665444823721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15446032107123549039059845 2896131020085665444823721)
                      ·
                        rfl

theorem cell23_5640195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_5640195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640195 prefixEnd_5640195 := by exact prefixLift 5640195
  have htrace : WordTrace (prefixWord ++ tailWord_5640195) baseStart_5640195 baseEnd_5640195 := by
    simpa [prefixWord, tailWord_5640195, baseEnd_5640195] using wordTrace_append hprefix tailTrace_5640195
  have hstable : (prefixWord ++ tailWord_5640195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640195).length < 2 ^ (prefixWord ++ tailWord_5640195).sum := by decide
  have hdescent : baseEnd_5640195 < baseStart_5640195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640216 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 2, 2, 2]
def baseStart_5640216 : Nat := 118140960795 + 5640216 * 2 ^ 59
def prefixEnd_5640216 : Nat := 4983230072969 + 3 ^ 40 * 5640216 * 2
def baseEnd_5640216 : Nat := 2896141803179409862661125

theorem tailTrace_5640216 : CollatzResearch.WordTrace tailWord_5640216 prefixEnd_5640216 2896141803179409862661125 := by
  unfold tailWord_5640216
  simp only [CollatzResearch.WordTrace]
  refine ⟨102857788867234089523946251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137143718489645452698595001 102857788867234089523946251)
  ·
    refine ⟨154286683300851134285919377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102857788867234089523946251 154286683300851134285919377)
    ·
      refine ⟨115715012475638350714439533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154286683300851134285919377 115715012475638350714439533)
      ·
        refine ⟨43393129678364381517914825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115715012475638350714439533 43393129678364381517914825)
        ·
          refine ⟨32544847258773286138436119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43393129678364381517914825 32544847258773286138436119)
          ·
            refine ⟨48817270888159929207654179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32544847258773286138436119 48817270888159929207654179)
            ·
              refine ⟨73225906332239893811481269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48817270888159929207654179 73225906332239893811481269)
              ·
                refine ⟨6864928718647490044826369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73225906332239893811481269 6864928718647490044826369)
                ·
                  refine ⟨5148696538985617533619777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6864928718647490044826369 5148696538985617533619777)
                  ·
                    refine ⟨3861522404239213150214833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5148696538985617533619777 3861522404239213150214833)
                    ·
                      refine ⟨2896141803179409862661125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3861522404239213150214833 2896141803179409862661125)
                      ·
                        rfl

theorem cell23_5640216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_5640216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640216 prefixEnd_5640216 := by exact prefixLift 5640216
  have htrace : WordTrace (prefixWord ++ tailWord_5640216) baseStart_5640216 baseEnd_5640216 := by
    simpa [prefixWord, tailWord_5640216, baseEnd_5640216] using wordTrace_append hprefix tailTrace_5640216
  have hstable : (prefixWord ++ tailWord_5640216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640216).length < 2 ^ (prefixWord ++ tailWord_5640216).sum := by decide
  have hdescent : baseEnd_5640216 < baseStart_5640216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640252 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_5640252 : Nat := 118140960795 + 5640252 * 2 ^ 59
def prefixEnd_5640252 : Nat := 4983230072969 + 3 ^ 40 * 5640252 * 2
def baseEnd_5640252 : Nat := 965386762827657240603653

theorem tailTrace_5640252 : CollatzResearch.WordTrace tailWord_5640252 prefixEnd_5640252 965386762827657240603653 := by
  unfold tailWord_5640252
  simp only [CollatzResearch.WordTrace]
  refine ⟨102858445381168878598101505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137144593841558504797468673 102858445381168878598101505)
  ·
    refine ⟨77143834035876658948576129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102858445381168878598101505 77143834035876658948576129)
    ·
      refine ⟨57857875526907494211432097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77143834035876658948576129 57857875526907494211432097)
      ·
        refine ⟨43393406645180620658574073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57857875526907494211432097 43393406645180620658574073)
        ·
          refine ⟨32545054983885465493930555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43393406645180620658574073 32545054983885465493930555)
          ·
            refine ⟨48817582475828198240895833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32545054983885465493930555 48817582475828198240895833)
            ·
              refine ⟨36613186856871148680671875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48817582475828198240895833 36613186856871148680671875)
              ·
                refine ⟨54919780285306723021007813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36613186856871148680671875 54919780285306723021007813)
                ·
                  refine ⟨10297458803495010566438965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54919780285306723021007813 10297458803495010566438965)
                  ·
                    refine ⟨965386762827657240603653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10297458803495010566438965 965386762827657240603653)
                    ·
                      rfl

theorem cell23_5640252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_5640252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640252 prefixEnd_5640252 := by exact prefixLift 5640252
  have htrace : WordTrace (prefixWord ++ tailWord_5640252) baseStart_5640252 baseEnd_5640252 := by
    simpa [prefixWord, tailWord_5640252, baseEnd_5640252] using wordTrace_append hprefix tailTrace_5640252
  have hstable : (prefixWord ++ tailWord_5640252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640252).length < 2 ^ (prefixWord ++ tailWord_5640252).sum := by decide
  have hdescent : baseEnd_5640252 < baseStart_5640252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640275 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_5640275 : Nat := 118140960795 + 5640275 * 2 ^ 59
def prefixEnd_5640275 : Nat := 4983230072969 + 3 ^ 40 * 5640275 * 2
def baseEnd_5640275 : Nat := 2896172098538025131823353

theorem tailTrace_5640275 : CollatzResearch.WordTrace tailWord_5640275 prefixEnd_5640275 2896172098538025131823353 := by
  unfold tailWord_5640275
  simp only [CollatzResearch.WordTrace]
  refine ⟨205717729641254432124290279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137145153094169621416193519 205717729641254432124290279)
  ·
    refine ⟨308576594461881648186435419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205717729641254432124290279 308576594461881648186435419)
    ·
      refine ⟨462864891692822472279653129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308576594461881648186435419 462864891692822472279653129)
      ·
        refine ⟨347148668769616854209739847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462864891692822472279653129 347148668769616854209739847)
        ·
          refine ⟨520723003154425281314609771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347148668769616854209739847 520723003154425281314609771)
          ·
            refine ⟨781084504731637921971914657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520723003154425281314609771 781084504731637921971914657)
            ·
              refine ⟨585813378548728441478935993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781084504731637921971914657 585813378548728441478935993)
              ·
                refine ⟨439360033911546331109201995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585813378548728441478935993 439360033911546331109201995)
                ·
                  refine ⟨659040050867319496663802993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439360033911546331109201995 659040050867319496663802993)
                  ·
                    refine ⟨494280038150489622497852245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 659040050867319496663802993 494280038150489622497852245)
                    ·
                      refine ⟨2896172098538025131823353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 494280038150489622497852245 2896172098538025131823353)
                      ·
                        rfl

theorem cell23_5640275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_5640275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640275 prefixEnd_5640275 := by exact prefixLift 5640275
  have htrace : WordTrace (prefixWord ++ tailWord_5640275) baseStart_5640275 baseEnd_5640275 := by
    simpa [prefixWord, tailWord_5640275, baseEnd_5640275] using wordTrace_append hprefix tailTrace_5640275
  have hstable : (prefixWord ++ tailWord_5640275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640275).length < 2 ^ (prefixWord ++ tailWord_5640275).sum := by decide
  have hdescent : baseEnd_5640275 < baseStart_5640275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640290 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_5640290 : Nat := 118140960795 + 5640290 * 2 ^ 59
def prefixEnd_5640290 : Nat := 4983230072969 + 3 ^ 40 * 5640290 * 2
def baseEnd_5640290 : Nat := 321797755638649174792865

theorem tailTrace_5640290 : CollatzResearch.WordTrace tailWord_5640290 prefixEnd_5640290 321797755638649174792865 := by
  unfold tailWord_5640290
  simp only [CollatzResearch.WordTrace]
  refine ⟨51429569184050022421521581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137145517824133393124057549 51429569184050022421521581)
  ·
    refine ⟨19286088444018758408070593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51429569184050022421521581 19286088444018758408070593)
    ·
      refine ⟨14464566333014068806052945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19286088444018758408070593 14464566333014068806052945)
      ·
        refine ⟨10848424749760551604539709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14464566333014068806052945 10848424749760551604539709)
        ·
          refine ⟨4068159281160206851702391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10848424749760551604539709 4068159281160206851702391)
          ·
            refine ⟨6102238921740310277553587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068159281160206851702391 6102238921740310277553587)
            ·
              refine ⟨9153358382610465416330381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102238921740310277553587 9153358382610465416330381)
              ·
                refine ⟨3432509393478924531123893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9153358382610465416330381 3432509393478924531123893)
                ·
                  refine ⟨321797755638649174792865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432509393478924531123893 321797755638649174792865)
                  ·
                    rfl

theorem cell23_5640290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_5640290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640290 prefixEnd_5640290 := by exact prefixLift 5640290
  have htrace : WordTrace (prefixWord ++ tailWord_5640290) baseStart_5640290 baseEnd_5640290 := by
    simpa [prefixWord, tailWord_5640290, baseEnd_5640290] using wordTrace_append hprefix tailTrace_5640290
  have hstable : (prefixWord ++ tailWord_5640290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640290).length < 2 ^ (prefixWord ++ tailWord_5640290).sum := by decide
  have hdescent : baseEnd_5640290 < baseStart_5640290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640312 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 6]
def baseStart_5640312 : Nat := 118140960795 + 5640312 * 2 ^ 59
def prefixEnd_5640312 : Nat := 4983230072969 + 3 ^ 40 * 5640312 * 2
def baseEnd_5640312 : Nat := 321799010813582387451187

theorem tailTrace_5640312 : CollatzResearch.WordTrace tailWord_5640312 prefixEnd_5640312 321799010813582387451187 := by
  unfold tailWord_5640312
  simp only [CollatzResearch.WordTrace]
  refine ⟨102859539571060193721693595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137146052761413591628924793 102859539571060193721693595)
  ·
    refine ⟨154289309356590290582540393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102859539571060193721693595 154289309356590290582540393)
    ·
      refine ⟨115716982017442717936905295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154289309356590290582540393 115716982017442717936905295)
      ·
        refine ⟨173575473026164076905357943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115716982017442717936905295 173575473026164076905357943)
        ·
          refine ⟨260363209539246115358036915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173575473026164076905357943 260363209539246115358036915)
          ·
            refine ⟨390544814308869173037055373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260363209539246115358036915 390544814308869173037055373)
            ·
              refine ⟨146454305365825939888895765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390544814308869173037055373 146454305365825939888895765)
              ·
                refine ⟨6865045564023090932291989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146454305365825939888895765 6865045564023090932291989)
                ·
                  refine ⟨321799010813582387451187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6865045564023090932291989 321799010813582387451187)
                  ·
                    rfl

theorem cell23_5640312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 6].length) (baseStart_5640312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640312 prefixEnd_5640312 := by exact prefixLift 5640312
  have htrace : WordTrace (prefixWord ++ tailWord_5640312) baseStart_5640312 baseEnd_5640312 := by
    simpa [prefixWord, tailWord_5640312, baseEnd_5640312] using wordTrace_append hprefix tailTrace_5640312
  have hstable : (prefixWord ++ tailWord_5640312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640312).length < 2 ^ (prefixWord ++ tailWord_5640312).sum := by decide
  have hdescent : baseEnd_5640312 < baseStart_5640312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640316 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_5640316 : Nat := 118140960795 + 5640316 * 2 ^ 59
def prefixEnd_5640316 : Nat := 4983230072969 + 3 ^ 40 * 5640316 * 2
def baseEnd_5640316 : Nat := 965397717081619823803555

theorem tailTrace_5640316 : CollatzResearch.WordTrace tailWord_5640316 prefixEnd_5640316 965397717081619823803555 := by
  unfold tailWord_5640316
  simp only [CollatzResearch.WordTrace]
  refine ⟨102859612517052948063266401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137146150022737264084355201 102859612517052948063266401)
  ·
    refine ⟨77144709387789711047449801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102859612517052948063266401 77144709387789711047449801)
    ·
      refine ⟨57858532040842283285587351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77144709387789711047449801 57858532040842283285587351)
      ·
        refine ⟨86787798061263424928381027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57858532040842283285587351 86787798061263424928381027)
        ·
          refine ⟨130181697091895137392571541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86787798061263424928381027 130181697091895137392571541)
          ·
            refine ⟨6102267051182584565276791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130181697091895137392571541 6102267051182584565276791)
            ·
              refine ⟨9153400576773876847915187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102267051182584565276791 9153400576773876847915187)
              ·
                refine ⟨13730100865160815271872781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9153400576773876847915187 13730100865160815271872781)
                ·
                  refine ⟨5148787824435305726952293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13730100865160815271872781 5148787824435305726952293)
                  ·
                    refine ⟨965397717081619823803555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148787824435305726952293 965397717081619823803555)
                    ·
                      rfl

theorem cell23_5640316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_5640316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640316 prefixEnd_5640316 := by exact prefixLift 5640316
  have htrace : WordTrace (prefixWord ++ tailWord_5640316) baseStart_5640316 baseEnd_5640316 := by
    simpa [prefixWord, tailWord_5640316, baseEnd_5640316] using wordTrace_append hprefix tailTrace_5640316
  have hstable : (prefixWord ++ tailWord_5640316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640316).length < 2 ^ (prefixWord ++ tailWord_5640316).sum := by decide
  have hdescent : baseEnd_5640316 < baseStart_5640316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640339 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 3]
def baseStart_5640339 : Nat := 118140960795 + 5640339 * 2 ^ 59
def prefixEnd_5640339 : Nat := 4983230072969 + 3 ^ 40 * 5640339 * 2
def baseEnd_5640339 : Nat := 2896204961299912881423059

theorem tailTrace_5640339 : CollatzResearch.WordTrace tailWord_5640339 prefixEnd_5640339 2896204961299912881423059 := by
  unfold tailWord_5640339
  simp only [CollatzResearch.WordTrace]
  refine ⟨205720063913022571054620071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137146709275348380703080047 205720063913022571054620071)
  ·
    refine ⟨308580095869533856581930107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205720063913022571054620071 308580095869533856581930107)
    ·
      refine ⟨462870143804300784872895161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308580095869533856581930107 462870143804300784872895161)
      ·
        refine ⟨347152607853225588654671371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462870143804300784872895161 347152607853225588654671371)
        ·
          refine ⟨520728911779838382982007057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347152607853225588654671371 520728911779838382982007057)
          ·
            refine ⟨390546683834878787236505293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520728911779838382982007057 390546683834878787236505293)
            ·
              refine ⟨146455006438079545213689485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390546683834878787236505293 146455006438079545213689485)
              ·
                refine ⟨54920627414279829455133557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146455006438079545213689485 54920627414279829455133557)
                ·
                  refine ⟨5148808820088734011418771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54920627414279829455133557 5148808820088734011418771)
                  ·
                    refine ⟨7723213230133101017128157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5148808820088734011418771 7723213230133101017128157)
                    ·
                      refine ⟨2896204961299912881423059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723213230133101017128157 2896204961299912881423059)
                      ·
                        rfl

theorem cell23_5640339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_5640339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640339 prefixEnd_5640339 := by exact prefixLift 5640339
  have htrace : WordTrace (prefixWord ++ tailWord_5640339) baseStart_5640339 baseEnd_5640339 := by
    simpa [prefixWord, tailWord_5640339, baseEnd_5640339] using wordTrace_append hprefix tailTrace_5640339
  have hstable : (prefixWord ++ tailWord_5640339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640339).length < 2 ^ (prefixWord ++ tailWord_5640339).sum := by decide
  have hdescent : baseEnd_5640339 < baseStart_5640339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640399 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_5640399 : Nat := 118140960795 + 5640399 * 2 ^ 59
def prefixEnd_5640399 : Nat := 4983230072969 + 3 ^ 40 * 5640399 * 2
def baseEnd_5640399 : Nat := 2896235770139182646672783

theorem tailTrace_5640399 : CollatzResearch.WordTrace tailWord_5640399 prefixEnd_5640399 2896235770139182646672783 := by
  unfold tailWord_5640399
  simp only [CollatzResearch.WordTrace]
  refine ⟨205722252292805201301804251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137148168195203467534536167 205722252292805201301804251)
  ·
    refine ⟨308583378439207801952706377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205722252292805201301804251 308583378439207801952706377)
    ·
      refine ⟨231437533829405851464529783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308583378439207801952706377 231437533829405851464529783)
      ·
        refine ⟨347156300744108777196794675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231437533829405851464529783 347156300744108777196794675)
        ·
          refine ⟨520734451116163165795192013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347156300744108777196794675 520734451116163165795192013)
          ·
            refine ⟨195275419168561187173197005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 520734451116163165795192013 195275419168561187173197005)
            ·
              refine ⟨73228282188210445189948877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195275419168561187173197005 73228282188210445189948877)
              ·
                refine ⟨27460605820578916946230829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73228282188210445189948877 27460605820578916946230829)
                ·
                  refine ⟨10297727182717093854836561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27460605820578916946230829 10297727182717093854836561)
                  ·
                    refine ⟨7723295387037820391127421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10297727182717093854836561 7723295387037820391127421)
                    ·
                      refine ⟨2896235770139182646672783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723295387037820391127421 2896235770139182646672783)
                      ·
                        rfl

theorem cell23_5640399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_5640399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640399 prefixEnd_5640399 := by exact prefixLift 5640399
  have htrace : WordTrace (prefixWord ++ tailWord_5640399) baseStart_5640399 baseEnd_5640399 := by
    simpa [prefixWord, tailWord_5640399, baseEnd_5640399] using wordTrace_append hprefix tailTrace_5640399
  have hstable : (prefixWord ++ tailWord_5640399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640399).length < 2 ^ (prefixWord ++ tailWord_5640399).sum := by decide
  have hdescent : baseEnd_5640399 < baseStart_5640399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640409 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_5640409 : Nat := 118140960795 + 5640409 * 2 ^ 59
def prefixEnd_5640409 : Nat := 4983230072969 + 3 ^ 40 * 5640409 * 2
def baseEnd_5640409 : Nat := 2896240904945727607547737

theorem tailTrace_5640409 : CollatzResearch.WordTrace tailWord_5640409 prefixEnd_5640409 2896240904945727607547737 := by
  unfold tailWord_5640409
  simp only [CollatzResearch.WordTrace]
  refine ⟨205722617022768973009668281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137148411348512648673112187 205722617022768973009668281)
  ·
    refine ⟨154291962767076729757251211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205722617022768973009668281 154291962767076729757251211)
    ·
      refine ⟨231437944150615094635876817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154291962767076729757251211 231437944150615094635876817)
      ·
        refine ⟨173578458112961320976907613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231437944150615094635876817 173578458112961320976907613)
        ·
          refine ⟨65091921792360495366340355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173578458112961320976907613 65091921792360495366340355)
          ·
            refine ⟨97637882688540743049510533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65091921792360495366340355 97637882688540743049510533)
            ·
              refine ⟨18307103004101389321783225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97637882688540743049510533 18307103004101389321783225)
              ·
                refine ⟨13730327253076041991337419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18307103004101389321783225 13730327253076041991337419)
                ·
                  refine ⟨20595490879614062987006129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13730327253076041991337419 20595490879614062987006129)
                  ·
                    refine ⟨15446618159710547240254597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20595490879614062987006129 15446618159710547240254597)
                    ·
                      refine ⟨2896240904945727607547737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15446618159710547240254597 2896240904945727607547737)
                      ·
                        rfl

theorem cell23_5640409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_5640409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640409 prefixEnd_5640409 := by exact prefixLift 5640409
  have htrace : WordTrace (prefixWord ++ tailWord_5640409) baseStart_5640409 baseEnd_5640409 := by
    simpa [prefixWord, tailWord_5640409, baseEnd_5640409] using wordTrace_append hprefix tailTrace_5640409
  have hstable : (prefixWord ++ tailWord_5640409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640409).length < 2 ^ (prefixWord ++ tailWord_5640409).sum := by decide
  have hdescent : baseEnd_5640409 < baseStart_5640409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640413 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5640413 : Nat := 118140960795 + 5640413 * 2 ^ 59
def prefixEnd_5640413 : Nat := 4983230072969 + 3 ^ 40 * 5640413 * 2
def baseEnd_5640413 : Nat := 2896242958868345591897719

theorem tailTrace_5640413 : CollatzResearch.WordTrace tailWord_5640413 prefixEnd_5640413 2896242958868345591897719 := by
  unfold tailWord_5640413
  simp only [CollatzResearch.WordTrace]
  refine ⟨205722762914754481692813893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137148508609836321128542595 205722762914754481692813893)
  ·
    refine ⟨38573018046516465317402605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205722762914754481692813893 38573018046516465317402605)
    ·
      refine ⟨14464881767443674494025977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38573018046516465317402605 14464881767443674494025977)
      ·
        refine ⟨10848661325582755870519483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14464881767443674494025977 10848661325582755870519483)
        ·
          refine ⟨16272991988374133805779225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10848661325582755870519483 16272991988374133805779225)
          ·
            refine ⟨12204743991280600354334419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16272991988374133805779225 12204743991280600354334419)
            ·
              refine ⟨18307115986920900531501629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12204743991280600354334419 18307115986920900531501629)
              ·
                refine ⟨6865168495095337699313111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18307115986920900531501629 6865168495095337699313111)
                ·
                  refine ⟨10297752742643006548969667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865168495095337699313111 10297752742643006548969667)
                  ·
                    refine ⟨15446629113964509823454501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10297752742643006548969667 15446629113964509823454501)
                    ·
                      refine ⟨2896242958868345591897719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15446629113964509823454501 2896242958868345591897719)
                      ·
                        rfl

theorem cell23_5640413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5640413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640413 prefixEnd_5640413 := by exact prefixLift 5640413
  have htrace : WordTrace (prefixWord ++ tailWord_5640413) baseStart_5640413 baseEnd_5640413 := by
    simpa [prefixWord, tailWord_5640413, baseEnd_5640413] using wordTrace_append hprefix tailTrace_5640413
  have hstable : (prefixWord ++ tailWord_5640413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640413).length < 2 ^ (prefixWord ++ tailWord_5640413).sum := by decide
  have hdescent : baseEnd_5640413 < baseStart_5640413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640416 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3]
def baseStart_5640416 : Nat := 118140960795 + 5640416 * 2 ^ 59
def prefixEnd_5640416 : Nat := 4983230072969 + 3 ^ 40 * 5640416 * 2
def baseEnd_5640416 : Nat := 2896244499310309080160205

theorem tailTrace_5640416 : CollatzResearch.WordTrace tailWord_5640416 prefixEnd_5640416 2896244499310309080160205 := by
  unfold tailWord_5640416
  simp only [CollatzResearch.WordTrace]
  refine ⟨102861436166871806602586551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137148581555829075470115401 102861436166871806602586551)
  ·
    refine ⟨154292154250307709903879827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102861436166871806602586551 154292154250307709903879827)
    ·
      refine ⟨231438231375461564855819741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154292154250307709903879827 231438231375461564855819741)
      ·
        refine ⟨86789336765798086820932403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231438231375461564855819741 86789336765798086820932403)
        ·
          refine ⟨130184005148697130231398605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86789336765798086820932403 130184005148697130231398605)
          ·
            refine ⟨48819001930761423836774477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130184005148697130231398605 48819001930761423836774477)
            ·
              refine ⟨18307125724035533938790429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48819001930761423836774477 18307125724035533938790429)
              ·
                refine ⟨6865172146513325227046411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18307125724035533938790429 6865172146513325227046411)
                ·
                  refine ⟨10297758219769987840569617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865172146513325227046411 10297758219769987840569617)
                  ·
                    refine ⟨7723318664827490880427213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10297758219769987840569617 7723318664827490880427213)
                    ·
                      refine ⟨2896244499310309080160205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723318664827490880427213 2896244499310309080160205)
                      ·
                        rfl

theorem cell23_5640416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_5640416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640416 prefixEnd_5640416 := by exact prefixLift 5640416
  have htrace : WordTrace (prefixWord ++ tailWord_5640416) baseStart_5640416 baseEnd_5640416 := by
    simpa [prefixWord, tailWord_5640416, baseEnd_5640416] using wordTrace_append hprefix tailTrace_5640416
  have hstable : (prefixWord ++ tailWord_5640416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640416).length < 2 ^ (prefixWord ++ tailWord_5640416).sum := by decide
  have hdescent : baseEnd_5640416 < baseStart_5640416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640423 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 2, 4]
def baseStart_5640423 : Nat := 118140960795 + 5640423 * 2 ^ 59
def prefixEnd_5640423 : Nat := 4983230072969 + 3 ^ 40 * 5640423 * 2
def baseEnd_5640423 : Nat := 965416031224963517590891

theorem tailTrace_5640423 : CollatzResearch.WordTrace tailWord_5640423 prefixEnd_5640423 965416031224963517590891 := by
  unfold tailWord_5640423
  simp only [CollatzResearch.WordTrace]
  refine ⟨205723127644718253400677923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137148751763145502267118615 205723127644718253400677923)
  ·
    refine ⟨308584691467077380101016885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205723127644718253400677923 308584691467077380101016885)
    ·
      refine ⟨28929814825038504384470333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308584691467077380101016885 28929814825038504384470333)
      ·
        refine ⟨10848680559389439144176375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28929814825038504384470333 10848680559389439144176375)
        ·
          refine ⟨16273020839084158716264563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10848680559389439144176375 16273020839084158716264563)
          ·
            refine ⟨24409531258626238074396845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16273020839084158716264563 24409531258626238074396845)
            ·
              refine ⟨9153574221984839277898817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24409531258626238074396845 9153574221984839277898817)
              ·
                refine ⟨6865180666488629458424113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9153574221984839277898817 6865180666488629458424113)
                ·
                  refine ⟨5148885499866472093818085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6865180666488629458424113 5148885499866472093818085)
                  ·
                    refine ⟨965416031224963517590891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148885499866472093818085 965416031224963517590891)
                    ·
                      rfl

theorem cell23_5640423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_5640423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640423 prefixEnd_5640423 := by exact prefixLift 5640423
  have htrace : WordTrace (prefixWord ++ tailWord_5640423) baseStart_5640423 baseEnd_5640423 := by
    simpa [prefixWord, tailWord_5640423, baseEnd_5640423] using wordTrace_append hprefix tailTrace_5640423
  have hstable : (prefixWord ++ tailWord_5640423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640423).length < 2 ^ (prefixWord ++ tailWord_5640423).sum := by decide
  have hdescent : baseEnd_5640423 < baseStart_5640423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640432 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_5640432 : Nat := 118140960795 + 5640432 * 2 ^ 59
def prefixEnd_5640432 : Nat := 4983230072969 + 3 ^ 40 * 5640432 * 2
def baseEnd_5640432 : Nat := 965417571666927005853377

theorem tailTrace_5640432 : CollatzResearch.WordTrace tailWord_5640432 prefixEnd_5640432 965417571666927005853377 := by
  unfold tailWord_5640432
  simp only [CollatzResearch.WordTrace]
  refine ⟨102861727950842823968877775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137148970601123765291837033 102861727950842823968877775)
  ·
    refine ⟨154292591926264235953316663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102861727950842823968877775 154292591926264235953316663)
    ·
      refine ⟨231438887889396353929974995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154292591926264235953316663 231438887889396353929974995)
      ·
        refine ⟨347158331834094530894962493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231438887889396353929974995 347158331834094530894962493)
        ·
          refine ⟨130184374437785449085610935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347158331834094530894962493 130184374437785449085610935)
          ·
            refine ⟨195276561656678173628416403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130184374437785449085610935 195276561656678173628416403)
            ·
              refine ⟨292914842485017260442624605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195276561656678173628416403 292914842485017260442624605)
              ·
                refine ⟨109843065931881472665984227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292914842485017260442624605 109843065931881472665984227)
                ·
                  refine ⟨164764598897822208998976341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109843065931881472665984227 164764598897822208998976341)
                  ·
                    refine ⟨965417571666927005853377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 164764598897822208998976341 965417571666927005853377)
                    ·
                      rfl

theorem cell23_5640432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_5640432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640432 prefixEnd_5640432 := by exact prefixLift 5640432
  have htrace : WordTrace (prefixWord ++ tailWord_5640432) baseStart_5640432 baseEnd_5640432 := by
    simpa [prefixWord, tailWord_5640432, baseEnd_5640432] using wordTrace_append hprefix tailTrace_5640432
  have hstable : (prefixWord ++ tailWord_5640432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640432).length < 2 ^ (prefixWord ++ tailWord_5640432).sum := by decide
  have hdescent : baseEnd_5640432 < baseStart_5640432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640450 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_5640450 : Nat := 118140960795 + 5640450 * 2 ^ 59
def prefixEnd_5640450 : Nat := 4983230072969 + 3 ^ 40 * 5640450 * 2
def baseEnd_5640450 : Nat := 2896261957652561947135049

theorem tailTrace_5640450 : CollatzResearch.WordTrace tailWord_5640450 prefixEnd_5640450 2896261957652561947135049 := by
  unfold tailWord_5640450
  simp only [CollatzResearch.WordTrace]
  refine ⟨51431028103905109252977701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137149408277080291341273869 51431028103905109252977701)
  ·
    refine ⟨9643317769482207984933319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51431028103905109252977701 9643317769482207984933319)
    ·
      refine ⟨14464976654223311977399979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9643317769482207984933319 14464976654223311977399979)
      ·
        refine ⟨21697464981334967966099969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14464976654223311977399979 21697464981334967966099969)
        ·
          refine ⟨16273098736001225974574977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21697464981334967966099969 16273098736001225974574977)
          ·
            refine ⟨12204824052000919480931233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16273098736001225974574977 12204824052000919480931233)
            ·
              refine ⟨9153618039000689610698425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12204824052000919480931233 9153618039000689610698425)
              ·
                refine ⟨6865213529250517208023819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9153618039000689610698425 6865213529250517208023819)
                ·
                  refine ⟨10297820293875775812035729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865213529250517208023819 10297820293875775812035729)
                  ·
                    refine ⟨7723365220406831859026797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10297820293875775812035729 7723365220406831859026797)
                    ·
                      refine ⟨2896261957652561947135049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723365220406831859026797 2896261957652561947135049)
                      ·
                        rfl

theorem cell23_5640450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_5640450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640450 prefixEnd_5640450 := by exact prefixLift 5640450
  have htrace : WordTrace (prefixWord ++ tailWord_5640450) baseStart_5640450 baseEnd_5640450 := by
    simpa [prefixWord, tailWord_5640450, baseEnd_5640450] using wordTrace_append hprefix tailTrace_5640450
  have hstable : (prefixWord ++ tailWord_5640450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640450).length < 2 ^ (prefixWord ++ tailWord_5640450).sum := by decide
  have hdescent : baseEnd_5640450 < baseStart_5640450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640497 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 2, 1, 3]
def baseStart_5640497 : Nat := 118140960795 + 5640497 * 2 ^ 59
def prefixEnd_5640497 : Nat := 4983230072969 + 3 ^ 40 * 5640497 * 2
def baseEnd_5640497 : Nat := 2896286091243323263247333

theorem tailTrace_5640497 : CollatzResearch.WordTrace tailWord_5640497 prefixEnd_5640497 2896286091243323263247333 := by
  unfold tailWord_5640497
  simp only [CollatzResearch.WordTrace]
  refine ⟨205725826646450164038871745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137150551097633442692581163 205725826646450164038871745)
  ·
    refine ⟨154294369984837623029153809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205725826646450164038871745 154294369984837623029153809)
    ·
      refine ⟨115720777488628217271865357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154294369984837623029153809 115720777488628217271865357)
      ·
        refine ⟨43395291558235581476949509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115720777488628217271865357 43395291558235581476949509)
        ·
          refine ⟨8136617167169171526928033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43395291558235581476949509 8136617167169171526928033)
          ·
            refine ⟨6102462875376878645196025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8136617167169171526928033 6102462875376878645196025)
            ·
              refine ⟨4576847156532658983897019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102462875376878645196025 4576847156532658983897019)
              ·
                refine ⟨6865270734798988475845529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576847156532658983897019 6865270734798988475845529)
                ·
                  refine ⟨5148953051099241356884147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6865270734798988475845529 5148953051099241356884147)
                  ·
                    refine ⟨7723429576648862035326221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5148953051099241356884147 7723429576648862035326221)
                    ·
                      refine ⟨2896286091243323263247333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723429576648862035326221 2896286091243323263247333)
                      ·
                        rfl

theorem cell23_5640497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_5640497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640497 prefixEnd_5640497 := by exact prefixLift 5640497
  have htrace : WordTrace (prefixWord ++ tailWord_5640497) baseStart_5640497 baseEnd_5640497 := by
    simpa [prefixWord, tailWord_5640497, baseEnd_5640497] using wordTrace_append hprefix tailTrace_5640497
  have hstable : (prefixWord ++ tailWord_5640497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640497).length < 2 ^ (prefixWord ++ tailWord_5640497).sum := by decide
  have hdescent : baseEnd_5640497 < baseStart_5640497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640499 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4]
def baseStart_5640499 : Nat := 118140960795 + 5640499 * 2 ^ 59
def prefixEnd_5640499 : Nat := 4983230072969 + 3 ^ 40 * 5640499 * 2
def baseEnd_5640499 : Nat := 2896287118204632255422323

theorem tailTrace_5640499 : CollatzResearch.WordTrace tailWord_5640499 prefixEnd_5640499 2896287118204632255422323 := by
  unfold tailWord_5640499
  simp only [CollatzResearch.WordTrace]
  refine ⟨205725899592442918380444551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137150599728295278920296367 205725899592442918380444551)
  ·
    refine ⟨308588849388664377570666827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205725899592442918380444551 308588849388664377570666827)
    ·
      refine ⟨462883274082996566356000241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308588849388664377570666827 462883274082996566356000241)
      ·
        refine ⟨347162455562247424767000181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462883274082996566356000241 347162455562247424767000181)
        ·
          refine ⟨32546480208960696071906267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 347162455562247424767000181 32546480208960696071906267)
          ·
            refine ⟨48819720313441044107859401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32546480208960696071906267 48819720313441044107859401)
            ·
              refine ⟨36614790235080783080894551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48819720313441044107859401 36614790235080783080894551)
              ·
                refine ⟨54922185352621174621341827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36614790235080783080894551 54922185352621174621341827)
                ·
                  refine ⟨82383278028931761932012741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54922185352621174621341827 82383278028931761932012741)
                  ·
                    refine ⟨15446864630424705362252389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82383278028931761932012741 15446864630424705362252389)
                    ·
                      refine ⟨2896287118204632255422323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15446864630424705362252389 2896287118204632255422323)
                      ·
                        rfl

theorem cell23_5640499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_5640499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640499 prefixEnd_5640499 := by exact prefixLift 5640499
  have htrace : WordTrace (prefixWord ++ tailWord_5640499) baseStart_5640499 baseEnd_5640499 := by
    simpa [prefixWord, tailWord_5640499, baseEnd_5640499] using wordTrace_append hprefix tailTrace_5640499
  have hstable : (prefixWord ++ tailWord_5640499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640499).length < 2 ^ (prefixWord ++ tailWord_5640499).sum := by decide
  have hdescent : baseEnd_5640499 < baseStart_5640499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640543 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 5]
def baseStart_5640543 : Nat := 118140960795 + 5640543 * 2 ^ 59
def prefixEnd_5640543 : Nat := 4983230072969 + 3 ^ 40 * 5640543 * 2
def baseEnd_5640543 : Nat := 321812190150381120363569

theorem tailTrace_5640543 : CollatzResearch.WordTrace tailWord_5640543 prefixEnd_5640543 321812190150381120363569 := by
  unfold tailWord_5640543
  simp only [CollatzResearch.WordTrace]
  refine ⟨205727504404283513895046283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137151669602855675930030855 205727504404283513895046283)
  ·
    refine ⟨308591256606425270842569425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205727504404283513895046283 308591256606425270842569425)
    ·
      refine ⟨231443442454818953131927069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308591256606425270842569425 231443442454818953131927069)
      ·
        refine ⟨86791290920557107424472651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231443442454818953131927069 86791290920557107424472651)
        ·
          refine ⟨130186936380835661136708977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86791290920557107424472651 130186936380835661136708977)
          ·
            refine ⟨97640202285626745852531733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130186936380835661136708977 97640202285626745852531733)
            ·
              refine ⟨4576884482138753711837425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97640202285626745852531733 4576884482138753711837425)
              ·
                refine ⟨3432663361604065283878069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576884482138753711837425 3432663361604065283878069)
                ·
                  refine ⟨321812190150381120363569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432663361604065283878069 321812190150381120363569)
                  ·
                    rfl

theorem cell23_5640543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 5].length) (baseStart_5640543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640543 prefixEnd_5640543 := by exact prefixLift 5640543
  have htrace : WordTrace (prefixWord ++ tailWord_5640543) baseStart_5640543 baseEnd_5640543 := by
    simpa [prefixWord, tailWord_5640543, baseEnd_5640543] using wordTrace_append hprefix tailTrace_5640543
  have hstable : (prefixWord ++ tailWord_5640543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640543).length < 2 ^ (prefixWord ++ tailWord_5640543).sum := by decide
  have hdescent : baseEnd_5640543 < baseStart_5640543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640573 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_5640573 : Nat := 118140960795 + 5640573 * 2 ^ 59
def prefixEnd_5640573 : Nat := 4983230072969 + 3 ^ 40 * 5640573 * 2
def baseEnd_5640573 : Nat := 965441705257688321965661

theorem tailTrace_5640573 : CollatzResearch.WordTrace tailWord_5640573 prefixEnd_5640573 965441705257688321965661 := by
  unfold tailWord_5640573
  simp only [CollatzResearch.WordTrace]
  refine ⟨205728598594174829018638373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137152399062783219345758915 205728598594174829018638373)
  ·
    refine ⟨38574112236407780440994695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205728598594174829018638373 38574112236407780440994695)
    ·
      refine ⟨57861168354611670661492043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38574112236407780440994695 57861168354611670661492043)
      ·
        refine ⟨86791752531917505992238065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57861168354611670661492043 86791752531917505992238065)
        ·
          refine ⟨65093814398938129494178549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86791752531917505992238065 65093814398938129494178549)
          ·
            refine ⟨6102545099900449640079239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65093814398938129494178549 6102545099900449640079239)
            ·
              refine ⟨9153817649850674460118859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102545099900449640079239 9153817649850674460118859)
              ·
                refine ⟨13730726474776011690178289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9153817649850674460118859 13730726474776011690178289)
                ·
                  refine ⟨10298044856082008767633717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13730726474776011690178289 10298044856082008767633717)
                  ·
                    refine ⟨965441705257688321965661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10298044856082008767633717 965441705257688321965661)
                    ·
                      rfl

theorem cell23_5640573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_5640573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640573 prefixEnd_5640573 := by exact prefixLift 5640573
  have htrace : WordTrace (prefixWord ++ tailWord_5640573) baseStart_5640573 baseEnd_5640573 := by
    simpa [prefixWord, tailWord_5640573, baseEnd_5640573] using wordTrace_append hprefix tailTrace_5640573
  have hstable : (prefixWord ++ tailWord_5640573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640573).length < 2 ^ (prefixWord ++ tailWord_5640573).sum := by decide
  have hdescent : baseEnd_5640573 < baseStart_5640573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640626 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_5640626 : Nat := 118140960795 + 5640626 * 2 ^ 59
def prefixEnd_5640626 : Nat := 4983230072969 + 3 ^ 40 * 5640626 * 2
def baseEnd_5640626 : Nat := 2896352330247753258534239

theorem tailTrace_5640626 : CollatzResearch.WordTrace tailWord_5640626 prefixEnd_5640626 2896352330247753258534239 := by
  unfold tailWord_5640626
  simp only [CollatzResearch.WordTrace]
  refine ⟨51432632915745704767579433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137153687775321879380211821 51432632915745704767579433)
  ·
    refine ⟨38574474686809278575684575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51432632915745704767579433 38574474686809278575684575)
    ·
      refine ⟨57861712030213917863526863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38574474686809278575684575 57861712030213917863526863)
      ·
        refine ⟨86792568045320876795290295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57861712030213917863526863 86792568045320876795290295)
        ·
          refine ⟨130188852067981315192935443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86792568045320876795290295 130188852067981315192935443)
          ·
            refine ⟨195283278101971972789403165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130188852067981315192935443 195283278101971972789403165)
            ·
              refine ⟨73231229288239489796026187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195283278101971972789403165 73231229288239489796026187)
              ·
                refine ⟨109846843932359234694039281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73231229288239489796026187 109846843932359234694039281)
                ·
                  refine ⟨82385132949269426020529461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109846843932359234694039281 82385132949269426020529461)
                  ·
                    refine ⟨7723606213994008689424637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82385132949269426020529461 7723606213994008689424637)
                    ·
                      refine ⟨2896352330247753258534239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723606213994008689424637 2896352330247753258534239)
                      ·
                        rfl

theorem cell23_5640626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_5640626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640626 prefixEnd_5640626 := by exact prefixLift 5640626
  have htrace : WordTrace (prefixWord ++ tailWord_5640626) baseStart_5640626 baseEnd_5640626 := by
    simpa [prefixWord, tailWord_5640626, baseEnd_5640626] using wordTrace_append hprefix tailTrace_5640626
  have hstable : (prefixWord ++ tailWord_5640626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640626).length < 2 ^ (prefixWord ++ tailWord_5640626).sum := by decide
  have hdescent : baseEnd_5640626 < baseStart_5640626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640637 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_5640637 : Nat := 118140960795 + 5640637 * 2 ^ 59
def prefixEnd_5640637 : Nat := 4983230072969 + 3 ^ 40 * 5640637 * 2
def baseEnd_5640637 : Nat := 965452659511650905165563

theorem tailTrace_5640637 : CollatzResearch.WordTrace tailWord_5640637 prefixEnd_5640637 965452659511650905165563 := by
  unfold tailWord_5640637
  simp only [CollatzResearch.WordTrace]
  refine ⟨205730932865942967948968165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137153955243961978632645443 205730932865942967948968165)
  ·
    refine ⟨38574549912364306490431531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205730932865942967948968165 38574549912364306490431531)
    ·
      refine ⟨57861824868546459735647297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38574549912364306490431531 57861824868546459735647297)
      ·
        refine ⟨43396368651409844801735473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57861824868546459735647297 43396368651409844801735473)
        ·
          refine ⟨32547276488557383601301605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43396368651409844801735473 32547276488557383601301605)
          ·
            refine ⟨6102614341604509425244051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32547276488557383601301605 6102614341604509425244051)
            ·
              refine ⟨9153921512406764137866077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102614341604509425244051 9153921512406764137866077)
              ·
                refine ⟨3432720567152536551699779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9153921512406764137866077 3432720567152536551699779)
                ·
                  refine ⟨5149080850728804827549669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432720567152536551699779 5149080850728804827549669)
                  ·
                    refine ⟨965452659511650905165563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149080850728804827549669 965452659511650905165563)
                    ·
                      rfl

theorem cell23_5640637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_5640637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640637 prefixEnd_5640637 := by exact prefixLift 5640637
  have htrace : WordTrace (prefixWord ++ tailWord_5640637) baseStart_5640637 baseEnd_5640637 := by
    simpa [prefixWord, tailWord_5640637, baseEnd_5640637] using wordTrace_append hprefix tailTrace_5640637
  have hstable : (prefixWord ++ tailWord_5640637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640637).length < 2 ^ (prefixWord ++ tailWord_5640637).sum := by decide
  have hdescent : baseEnd_5640637 < baseStart_5640637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640680 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5640680 : Nat := 118140960795 + 5640680 * 2 ^ 59
def prefixEnd_5640680 : Nat := 4983230072969 + 3 ^ 40 * 5640680 * 2
def baseEnd_5640680 : Nat := 965460019401032015752997

theorem tailTrace_5640680 : CollatzResearch.WordTrace tailWord_5640680 prefixEnd_5640680 965460019401032015752997 := by
  unfold tailWord_5640680
  simp only [CollatzResearch.WordTrace]
  refine ⟨102866250602393593146391747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137155000803191457528522329 102866250602393593146391747)
  ·
    refine ⟨154299375903590389719587621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102866250602393593146391747 154299375903590389719587621)
    ·
      refine ⟨28931132981923198072422679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154299375903590389719587621 28931132981923198072422679)
      ·
        refine ⟨43396699472884797108634019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28931132981923198072422679 43396699472884797108634019)
        ·
          refine ⟨65095049209327195662951029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43396699472884797108634019 65095049209327195662951029)
          ·
            refine ⟨6102660863374424593401659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65095049209327195662951029 6102660863374424593401659)
            ·
              refine ⟨9153991295061636890102489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102660863374424593401659 9153991295061636890102489)
              ·
                refine ⟨6865493471296227667576867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9153991295061636890102489 6865493471296227667576867)
                ·
                  refine ⟨10298240206944341501365301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865493471296227667576867 10298240206944341501365301)
                  ·
                    refine ⟨965460019401032015752997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10298240206944341501365301 965460019401032015752997)
                    ·
                      rfl

theorem cell23_5640680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5640680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640680 prefixEnd_5640680 := by exact prefixLift 5640680
  have htrace : WordTrace (prefixWord ++ tailWord_5640680) baseStart_5640680 baseEnd_5640680 := by
    simpa [prefixWord, tailWord_5640680, baseEnd_5640680] using wordTrace_append hprefix tailTrace_5640680
  have hstable : (prefixWord ++ tailWord_5640680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640680).length < 2 ^ (prefixWord ++ tailWord_5640680).sum := by decide
  have hdescent : baseEnd_5640680 < baseStart_5640680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640711 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_5640711 : Nat := 118140960795 + 5640711 * 2 ^ 59
def prefixEnd_5640711 : Nat := 4983230072969 + 3 ^ 40 * 5640711 * 2
def baseEnd_5640711 : Nat := 2896395976103385425971349

theorem tailTrace_5640711 : CollatzResearch.WordTrace tailWord_5640711 prefixEnd_5640711 2896395976103385425971349 := by
  unfold tailWord_5640711
  simp only [CollatzResearch.WordTrace]
  refine ⟨205733631867674878587161987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137155754578449919058107991 205733631867674878587161987)
  ·
    refine ⟨308600447801512317880742981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205733631867674878587161987 308600447801512317880742981)
    ·
      refine ⟨57862583962783559602639309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308600447801512317880742981 57862583962783559602639309)
      ·
        refine ⟨21698468986043834850989741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57862583962783559602639309 21698468986043834850989741)
        ·
          refine ⟨8136925869766438069121153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21698468986043834850989741 8136925869766438069121153)
          ·
            refine ⟨6102694402324828551840865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8136925869766438069121153 6102694402324828551840865)
            ·
              refine ⟨4577020801743621413880649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102694402324828551840865 4577020801743621413880649)
              ·
                refine ⟨3432765601307716060410487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4577020801743621413880649 3432765601307716060410487)
                ·
                  refine ⟨5149148401961574090615731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432765601307716060410487 5149148401961574090615731)
                  ·
                    refine ⟨7723722602942361135923597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149148401961574090615731 7723722602942361135923597)
                    ·
                      refine ⟨2896395976103385425971349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723722602942361135923597 2896395976103385425971349)
                      ·
                        rfl

theorem cell23_5640711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_5640711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640711 prefixEnd_5640711 := by exact prefixLift 5640711
  have htrace : WordTrace (prefixWord ++ tailWord_5640711) baseStart_5640711 baseEnd_5640711 := by
    simpa [prefixWord, tailWord_5640711, baseEnd_5640711] using wordTrace_append hprefix tailTrace_5640711
  have hstable : (prefixWord ++ tailWord_5640711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640711).length < 2 ^ (prefixWord ++ tailWord_5640711).sum := by decide
  have hdescent : baseEnd_5640711 < baseStart_5640711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640717 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5640717 : Nat := 118140960795 + 5640717 * 2 ^ 59
def prefixEnd_5640717 : Nat := 4983230072969 + 3 ^ 40 * 5640717 * 2
def baseEnd_5640717 : Nat := 2896399056987312402496321

theorem tailTrace_5640717 : CollatzResearch.WordTrace tailWord_5640717 prefixEnd_5640717 2896399056987312402496321 := by
  unfold tailWord_5640717
  simp only [CollatzResearch.WordTrace]
  refine ⟨205733850705653141611880405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137155900470435427741253603 205733850705653141611880405)
  ·
    refine ⟨4821887125913745506528447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 205733850705653141611880405 4821887125913745506528447)
    ·
      refine ⟨7232830688870618259792671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821887125913745506528447 7232830688870618259792671)
      ·
        refine ⟨10849246033305927389689007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7232830688870618259792671 10849246033305927389689007)
        ·
          refine ⟨16273869049958891084533511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849246033305927389689007 16273869049958891084533511)
          ·
            refine ⟨24410803574938336626800267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16273869049958891084533511 24410803574938336626800267)
            ·
              refine ⟨36616205362407504940200401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24410803574938336626800267 36616205362407504940200401)
              ·
                refine ⟨27462154021805628705150301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36616205362407504940200401 27462154021805628705150301)
                ·
                  refine ⟨10298307758177110764431363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27462154021805628705150301 10298307758177110764431363)
                  ·
                    refine ⟨15447461637265666146647045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10298307758177110764431363 15447461637265666146647045)
                    ·
                      refine ⟨2896399056987312402496321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15447461637265666146647045 2896399056987312402496321)
                      ·
                        rfl

theorem cell23_5640717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5640717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640717 prefixEnd_5640717 := by exact prefixLift 5640717
  have htrace : WordTrace (prefixWord ++ tailWord_5640717) baseStart_5640717 baseEnd_5640717 := by
    simpa [prefixWord, tailWord_5640717, baseEnd_5640717] using wordTrace_append hprefix tailTrace_5640717
  have hstable : (prefixWord ++ tailWord_5640717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640717).length < 2 ^ (prefixWord ++ tailWord_5640717).sum := by decide
  have hdescent : baseEnd_5640717 < baseStart_5640717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640823 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_5640823 : Nat := 118140960795 + 5640823 * 2 ^ 59
def prefixEnd_5640823 : Nat := 4983230072969 + 3 ^ 40 * 5640823 * 2
def baseEnd_5640823 : Nat := 2896453485936688987770833

theorem tailTrace_5640823 : CollatzResearch.WordTrace tailWord_5640823 prefixEnd_5640823 2896453485936688987770833 := by
  unfold tailWord_5640823
  simp only [CollatzResearch.WordTrace]
  refine ⟨205737716843269121715239123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137158477895512747810159415 205737716843269121715239123)
  ·
    refine ⟨308606575264903682572858685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205737716843269121715239123 308606575264903682572858685)
    ·
      refine ⟨115727465724338880964822007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308606575264903682572858685 115727465724338880964822007)
      ·
        refine ⟨173591198586508321447233011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115727465724338880964822007 173591198586508321447233011)
        ·
          refine ⟨260386797879762482170849517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173591198586508321447233011 260386797879762482170849517)
          ·
            refine ⟨97645049204910930814068569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260386797879762482170849517 97645049204910930814068569)
            ·
              refine ⟨73233786903683198110551427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97645049204910930814068569 73233786903683198110551427)
              ·
                refine ⟨109850680355524797165827141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73233786903683198110551427 109850680355524797165827141)
                ·
                  refine ⟨20597002566660899468592589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109850680355524797165827141 20597002566660899468592589)
                  ·
                    refine ⟨7723875962497837300722221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20597002566660899468592589 7723875962497837300722221)
                    ·
                      refine ⟨2896453485936688987770833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7723875962497837300722221 2896453485936688987770833)
                      ·
                        rfl

theorem cell23_5640823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_5640823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640823 prefixEnd_5640823 := by exact prefixLift 5640823
  have htrace : WordTrace (prefixWord ++ tailWord_5640823) baseStart_5640823 baseEnd_5640823 := by
    simpa [prefixWord, tailWord_5640823, baseEnd_5640823] using wordTrace_append hprefix tailTrace_5640823
  have hstable : (prefixWord ++ tailWord_5640823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640823).length < 2 ^ (prefixWord ++ tailWord_5640823).sum := by decide
  have hdescent : baseEnd_5640823 < baseStart_5640823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640860 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_5640860 : Nat := 118140960795 + 5640860 * 2 ^ 59
def prefixEnd_5640860 : Nat := 4983230072969 + 3 ^ 40 * 5640860 * 2
def baseEnd_5640860 : Nat := 965490828240301781002721

theorem tailTrace_5640860 : CollatzResearch.WordTrace tailWord_5640860 prefixEnd_5640860 965490828240301781002721 := by
  unfold tailWord_5640860
  simp only [CollatzResearch.WordTrace]
  refine ⟨102869533172067538517168017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137159377562756718022890689 102869533172067538517168017)
  ·
    refine ⟨77152149879050653887876013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102869533172067538517168017 77152149879050653887876013)
    ·
      refine ⟨28932056204643995207953505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77152149879050653887876013 28932056204643995207953505)
      ·
        refine ⟨21699042153482996405965129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28932056204643995207953505 21699042153482996405965129)
        ·
          refine ⟨16274281615112247304473847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21699042153482996405965129 16274281615112247304473847)
          ·
            refine ⟨24411422422668370956710771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16274281615112247304473847 24411422422668370956710771)
            ·
              refine ⟨36617133634002556435066157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24411422422668370956710771 36617133634002556435066157)
              ·
                refine ⟨13731425112750958663149809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36617133634002556435066157 13731425112750958663149809)
                ·
                  refine ⟨10298568834563218997362357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13731425112750958663149809 10298568834563218997362357)
                  ·
                    refine ⟨965490828240301781002721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10298568834563218997362357 965490828240301781002721)
                    ·
                      rfl

theorem cell23_5640860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_5640860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640860 prefixEnd_5640860 := by exact prefixLift 5640860
  have htrace : WordTrace (prefixWord ++ tailWord_5640860) baseStart_5640860 baseEnd_5640860 := by
    simpa [prefixWord, tailWord_5640860, baseEnd_5640860] using wordTrace_append hprefix tailTrace_5640860
  have hstable : (prefixWord ++ tailWord_5640860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640860).length < 2 ^ (prefixWord ++ tailWord_5640860).sum := by decide
  have hdescent : baseEnd_5640860 < baseStart_5640860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640880 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 2, 4, 2]
def baseStart_5640880 : Nat := 118140960795 + 5640880 * 2 ^ 59
def prefixEnd_5640880 : Nat := 4983230072969 + 3 ^ 40 * 5640880 * 2
def baseEnd_5640880 : Nat := 2896482754333995264758071

theorem tailTrace_5640880 : CollatzResearch.WordTrace tailWord_5640880 prefixEnd_5640880 2896482754333995264758071 := by
  unfold tailWord_5640880
  simp only [CollatzResearch.WordTrace]
  refine ⟨102869897902031310225032047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137159863869375080300042729 102869897902031310225032047)
  ·
    refine ⟨154304846853046965337548071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102869897902031310225032047 154304846853046965337548071)
    ·
      refine ⟨231457270279570448006322107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154304846853046965337548071 231457270279570448006322107)
      ·
        refine ⟨347185905419355672009483161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231457270279570448006322107 347185905419355672009483161)
        ·
          refine ⟨260389429064516754007112371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347185905419355672009483161 260389429064516754007112371)
          ·
            refine ⟨390584143596775131010668557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260389429064516754007112371 390584143596775131010668557)
            ·
              refine ⟨146469053848790674129000709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390584143596775131010668557 146469053848790674129000709)
              ·
                refine ⟨27462947596648251399187633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146469053848790674129000709 27462947596648251399187633)
                ·
                  refine ⟨20597210697486188549390725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27462947596648251399187633 20597210697486188549390725)
                  ·
                    refine ⟨3861977005778660353010761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20597210697486188549390725 3861977005778660353010761)
                    ·
                      refine ⟨2896482754333995264758071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3861977005778660353010761 2896482754333995264758071)
                      ·
                        rfl

theorem cell23_5640880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 4, 2].length) (baseStart_5640880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640880 prefixEnd_5640880 := by exact prefixLift 5640880
  have htrace : WordTrace (prefixWord ++ tailWord_5640880) baseStart_5640880 baseEnd_5640880 := by
    simpa [prefixWord, tailWord_5640880, baseEnd_5640880] using wordTrace_append hprefix tailTrace_5640880
  have hstable : (prefixWord ++ tailWord_5640880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640880).length < 2 ^ (prefixWord ++ tailWord_5640880).sum := by decide
  have hdescent : baseEnd_5640880 < baseStart_5640880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640881 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 5]
def baseStart_5640881 : Nat := 118140960795 + 5640881 * 2 ^ 59
def prefixEnd_5640881 : Nat := 4983230072969 + 3 ^ 40 * 5640881 * 2
def baseEnd_5640881 : Nat := 321831474201627751205063

theorem tailTrace_5640881 : CollatzResearch.WordTrace tailWord_5640881 prefixEnd_5640881 321831474201627751205063 := by
  unfold tailWord_5640881
  simp only [CollatzResearch.WordTrace]
  refine ⟨205739832277058997620850497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137159888184705998413900331 205739832277058997620850497)
  ·
    refine ⟨154304874207794248215637873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205739832277058997620850497 154304874207794248215637873)
    ·
      refine ⟨115728655655845686161728405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154304874207794248215637873 115728655655845686161728405)
      ·
        refine ⟨5424780733867766538831019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115728655655845686161728405 5424780733867766538831019)
        ·
          refine ⟨8137171100801649808246529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5424780733867766538831019 8137171100801649808246529)
          ·
            refine ⟨6102878325601237356184897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8137171100801649808246529 6102878325601237356184897)
            ·
              refine ⟨4577158744200928017138673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102878325601237356184897 4577158744200928017138673)
              ·
                refine ⟨3432869058150696012854005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4577158744200928017138673 3432869058150696012854005)
                ·
                  refine ⟨321831474201627751205063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432869058150696012854005 321831474201627751205063)
                  ·
                    rfl

theorem cell23_5640881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 5].length) (baseStart_5640881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640881 prefixEnd_5640881 := by exact prefixLift 5640881
  have htrace : WordTrace (prefixWord ++ tailWord_5640881) baseStart_5640881 baseEnd_5640881 := by
    simpa [prefixWord, tailWord_5640881, baseEnd_5640881] using wordTrace_append hprefix tailTrace_5640881
  have hstable : (prefixWord ++ tailWord_5640881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640881).length < 2 ^ (prefixWord ++ tailWord_5640881).sum := by decide
  have hdescent : baseEnd_5640881 < baseStart_5640881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640890 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_5640890 : Nat := 118140960795 + 5640890 * 2 ^ 59
def prefixEnd_5640890 : Nat := 4983230072969 + 3 ^ 40 * 5640890 * 2
def baseEnd_5640890 : Nat := 965495963046846741877675

theorem tailTrace_5640890 : CollatzResearch.WordTrace tailWord_5640890 prefixEnd_5640890 965495963046846741877675 := by
  unfold tailWord_5640890
  simp only [CollatzResearch.WordTrace]
  refine ⟨51435040133506598039482031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137160107022684261438618749 51435040133506598039482031)
  ·
    refine ⟨77152560200259897059223047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51435040133506598039482031 77152560200259897059223047)
    ·
      refine ⟨115728840300389845588834571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77152560200259897059223047 115728840300389845588834571)
      ·
        refine ⟨173593260450584768383251857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115728840300389845588834571 173593260450584768383251857)
        ·
          refine ⟨130194945337938576287438893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173593260450584768383251857 130194945337938576287438893)
          ·
            refine ⟨48823104501726966107789585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130194945337938576287438893 48823104501726966107789585)
            ·
              refine ⟨36617328376295224580842189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48823104501726966107789585 36617328376295224580842189)
              ·
                refine ⟨13731498141110709217815821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36617328376295224580842189 13731498141110709217815821)
                ·
                  refine ⟨5149311802916515956680933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13731498141110709217815821 5149311802916515956680933)
                  ·
                    refine ⟨965495963046846741877675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149311802916515956680933 965495963046846741877675)
                    ·
                      rfl

theorem cell23_5640890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_5640890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640890 prefixEnd_5640890 := by exact prefixLift 5640890
  have htrace : WordTrace (prefixWord ++ tailWord_5640890) baseStart_5640890 baseEnd_5640890 := by
    simpa [prefixWord, tailWord_5640890, baseEnd_5640890] using wordTrace_append hprefix tailTrace_5640890
  have hstable : (prefixWord ++ tailWord_5640890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640890).length < 2 ^ (prefixWord ++ tailWord_5640890).sum := by decide
  have hdescent : baseEnd_5640890 < baseStart_5640890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640914 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5640914 : Nat := 118140960795 + 5640914 * 2 ^ 59
def prefixEnd_5640914 : Nat := 4983230072969 + 3 ^ 40 * 5640914 * 2
def baseEnd_5640914 : Nat := 2896500212676248131732915

theorem tailTrace_5640914 : CollatzResearch.WordTrace tailWord_5640914 prefixEnd_5640914 2896500212676248131732915 := by
  unfold tailWord_5640914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51435258971484861064200449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137160690590626296171201197 51435258971484861064200449)
  ·
    refine ⟨38576444228613645798150337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51435258971484861064200449 38576444228613645798150337)
    ·
      refine ⟨28932333171460234348612753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38576444228613645798150337 28932333171460234348612753)
      ·
        refine ⟨21699249878595175761459565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28932333171460234348612753 21699249878595175761459565)
        ·
          refine ⟨8137218704473190910547337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21699249878595175761459565 8137218704473190910547337)
          ·
            refine ⟨6102914028354893182910503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8137218704473190910547337 6102914028354893182910503)
            ·
              refine ⟨9154371042532339774365755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102914028354893182910503 9154371042532339774365755)
              ·
                refine ⟨13731556563798509661548633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154371042532339774365755 13731556563798509661548633)
                ·
                  refine ⟨10298667422848882246161475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13731556563798509661548633 10298667422848882246161475)
                  ·
                    refine ⟨15448001134273323369242213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10298667422848882246161475 15448001134273323369242213)
                    ·
                      refine ⟨2896500212676248131732915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15448001134273323369242213 2896500212676248131732915)
                      ·
                        rfl

theorem cell23_5640914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5640914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640914 prefixEnd_5640914 := by exact prefixLift 5640914
  have htrace : WordTrace (prefixWord ++ tailWord_5640914) baseStart_5640914 baseEnd_5640914 := by
    simpa [prefixWord, tailWord_5640914, baseEnd_5640914] using wordTrace_append hprefix tailTrace_5640914
  have hstable : (prefixWord ++ tailWord_5640914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640914).length < 2 ^ (prefixWord ++ tailWord_5640914).sum := by decide
  have hdescent : baseEnd_5640914 < baseStart_5640914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640967 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 1, 5]
def baseStart_5640967 : Nat := 118140960795 + 5640967 * 2 ^ 59
def prefixEnd_5640967 : Nat := 4983230072969 + 3 ^ 40 * 5640967 * 2
def baseEnd_5640967 : Nat := 965509142383645474790057

theorem tailTrace_5640967 : CollatzResearch.WordTrace tailWord_5640967 prefixEnd_5640967 965509142383645474790057 := by
  unfold tailWord_5640967
  simp only [CollatzResearch.WordTrace]
  refine ⟨205742968954747434308481155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137161979303164956205654103 205742968954747434308481155)
  ·
    refine ⟨308614453432121151462721733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205742968954747434308481155 308614453432121151462721733)
    ·
      refine ⟨57865210018522715899260325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308614453432121151462721733 57865210018522715899260325)
      ·
        refine ⟨10849726878473009231111311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57865210018522715899260325 10849726878473009231111311)
        ·
          refine ⟨16274590317709513846666967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849726878473009231111311 16274590317709513846666967)
          ·
            refine ⟨24411885476564270770000451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16274590317709513846666967 24411885476564270770000451)
            ·
              refine ⟨36617828214846406155000677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24411885476564270770000451 36617828214846406155000677)
              ·
                refine ⟨6865842790283701154062627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36617828214846406155000677 6865842790283701154062627)
                ·
                  refine ⟨10298764185425551731093941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865842790283701154062627 10298764185425551731093941)
                  ·
                    refine ⟨965509142383645474790057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10298764185425551731093941 965509142383645474790057)
                    ·
                      rfl

theorem cell23_5640967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_5640967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640967 prefixEnd_5640967 := by exact prefixLift 5640967
  have htrace : WordTrace (prefixWord ++ tailWord_5640967) baseStart_5640967 baseEnd_5640967 := by
    simpa [prefixWord, tailWord_5640967, baseEnd_5640967] using wordTrace_append hprefix tailTrace_5640967
  have hstable : (prefixWord ++ tailWord_5640967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640967).length < 2 ^ (prefixWord ++ tailWord_5640967).sum := by decide
  have hdescent : baseEnd_5640967 < baseStart_5640967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5640997 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_5640997 : Nat := 118140960795 + 5640997 * 2 ^ 59
def prefixEnd_5640997 : Nat := 4983230072969 + 3 ^ 40 * 5640997 * 2
def baseEnd_5640997 : Nat := 965514277190190435665011

theorem tailTrace_5640997 : CollatzResearch.WordTrace tailWord_5640997 prefixEnd_5640997 965514277190190435665011 := by
  unfold tailWord_5640997
  simp only [CollatzResearch.WordTrace]
  refine ⟨205744063144638749432073245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137162708763092499621382163 205744063144638749432073245)
  ·
    refine ⟨77154023679239531037027467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205744063144638749432073245 77154023679239531037027467)
    ·
      refine ⟨115731035518859296555541201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77154023679239531037027467 115731035518859296555541201)
      ·
        refine ⟨86798276639144472416655901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115731035518859296555541201 86798276639144472416655901)
        ·
          refine ⟨32549353739679177156245963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86798276639144472416655901 32549353739679177156245963)
          ·
            refine ⟨48824030609518765734368945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32549353739679177156245963 48824030609518765734368945)
            ·
              refine ⟨36618022957139074300776709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48824030609518765734368945 36618022957139074300776709)
              ·
                refine ⟨6865879304463576431395633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36618022957139074300776709 6865879304463576431395633)
                ·
                  refine ⟨5149409478347682323546725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6865879304463576431395633 5149409478347682323546725)
                  ·
                    refine ⟨965514277190190435665011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149409478347682323546725 965514277190190435665011)
                    ·
                      rfl

theorem cell23_5640997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_5640997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5640997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5640997 prefixEnd_5640997 := by exact prefixLift 5640997
  have htrace : WordTrace (prefixWord ++ tailWord_5640997) baseStart_5640997 baseEnd_5640997 := by
    simpa [prefixWord, tailWord_5640997, baseEnd_5640997] using wordTrace_append hprefix tailTrace_5640997
  have hstable : (prefixWord ++ tailWord_5640997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5640997).length < 2 ^ (prefixWord ++ tailWord_5640997).sum := by decide
  have hdescent : baseEnd_5640997 < baseStart_5640997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5640997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641000 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5641000 : Nat := 118140960795 + 5641000 * 2 ^ 59
def prefixEnd_5641000 : Nat := 4983230072969 + 3 ^ 40 * 5641000 * 2
def baseEnd_5641000 : Nat := 2896544372012534795257519

theorem tailTrace_5641000 : CollatzResearch.WordTrace tailWord_5641000 prefixEnd_5641000 2896544372012534795257519 := by
  unfold tailWord_5641000
  simp only [CollatzResearch.WordTrace]
  refine ⟨102872086281813940472216227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137162781709085253962954969 102872086281813940472216227)
  ·
    refine ⟨154308129422720910708324341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102872086281813940472216227 154308129422720910708324341)
    ·
      refine ⟨14466387133380085378905407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154308129422720910708324341 14466387133380085378905407)
      ·
        refine ⟨21699580700070128068358111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14466387133380085378905407 21699580700070128068358111)
        ·
          refine ⟨32549371050105192102537167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21699580700070128068358111 32549371050105192102537167)
          ·
            refine ⟨48824056575157788153805751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32549371050105192102537167 48824056575157788153805751)
            ·
              refine ⟨73236084862736682230708627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48824056575157788153805751 73236084862736682230708627)
              ·
                refine ⟨109854127294105023346062941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73236084862736682230708627 109854127294105023346062941)
                ·
                  refine ⟨41195297735289383754773603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109854127294105023346062941 41195297735289383754773603)
                  ·
                    refine ⟨61792946602934075632160405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41195297735289383754773603 61792946602934075632160405)
                    ·
                      refine ⟨2896544372012534795257519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61792946602934075632160405 2896544372012534795257519)
                      ·
                        rfl

theorem cell23_5641000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5641000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641000 prefixEnd_5641000 := by exact prefixLift 5641000
  have htrace : WordTrace (prefixWord ++ tailWord_5641000) baseStart_5641000 baseEnd_5641000 := by
    simpa [prefixWord, tailWord_5641000, baseEnd_5641000] using wordTrace_append hprefix tailTrace_5641000
  have hstable : (prefixWord ++ tailWord_5641000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641000).length < 2 ^ (prefixWord ++ tailWord_5641000).sum := by decide
  have hdescent : baseEnd_5641000 < baseStart_5641000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641003 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_5641003 : Nat := 118140960795 + 5641003 * 2 ^ 59
def prefixEnd_5641003 : Nat := 4983230072969 + 3 ^ 40 * 5641003 * 2
def baseEnd_5641003 : Nat := 2896545912454498283520005

theorem tailTrace_5641003 : CollatzResearch.WordTrace tailWord_5641003 prefixEnd_5641003 2896545912454498283520005 := by
  unfold tailWord_5641003
  simp only [CollatzResearch.WordTrace]
  refine ⟨205744281982617012456791663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137162854655078008304527775 205744281982617012456791663)
  ·
    refine ⟨308616422973925518685187495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205744281982617012456791663 308616422973925518685187495)
    ·
      refine ⟨462924634460888278027781243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308616422973925518685187495 462924634460888278027781243)
      ·
        refine ⟨694386951691332417041671865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462924634460888278027781243 694386951691332417041671865)
        ·
          refine ⟨520790213768499312781253899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694386951691332417041671865 520790213768499312781253899)
          ·
            refine ⟨781185320652748969171880849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520790213768499312781253899 781185320652748969171880849)
            ·
              refine ⟨585888990489561726878910637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781185320652748969171880849 585888990489561726878910637)
              ·
                refine ⟨219708371433585647579591489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 585888990489561726878910637 219708371433585647579591489)
                ·
                  refine ⟨164781278575189235684693617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219708371433585647579591489 164781278575189235684693617)
                  ·
                    refine ⟨123585958931391926763520213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164781278575189235684693617 123585958931391926763520213)
                    ·
                      refine ⟨2896545912454498283520005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123585958931391926763520213 2896545912454498283520005)
                      ·
                        rfl

theorem cell23_5641003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_5641003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641003 prefixEnd_5641003 := by exact prefixLift 5641003
  have htrace : WordTrace (prefixWord ++ tailWord_5641003) baseStart_5641003 baseEnd_5641003 := by
    simpa [prefixWord, tailWord_5641003, baseEnd_5641003] using wordTrace_append hprefix tailTrace_5641003
  have hstable : (prefixWord ++ tailWord_5641003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641003).length < 2 ^ (prefixWord ++ tailWord_5641003).sum := by decide
  have hdescent : baseEnd_5641003 < baseStart_5641003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641010 : List Nat := [3, 2, 1, 1, 3, 1, 4, 8]
def baseStart_5641010 : Nat := 118140960795 + 5641010 * 2 ^ 59
def prefixEnd_5641010 : Nat := 4983230072969 + 3 ^ 40 * 5641010 * 2
def baseEnd_5641010 : Nat := 107279611363669620597499

theorem tailTrace_5641010 : CollatzResearch.WordTrace tailWord_5641010 prefixEnd_5641010 107279611363669620597499 := by
  unfold tailWord_5641010
  simp only [CollatzResearch.WordTrace]
  refine ⟨51436134323397913163074121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137163024862394435101530989 51436134323397913163074121)
  ·
    refine ⟨38577100742548434872305591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51436134323397913163074121 38577100742548434872305591)
    ·
      refine ⟨57865651113822652308458387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38577100742548434872305591 57865651113822652308458387)
      ·
        refine ⟨86798476670733978462687581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57865651113822652308458387 86798476670733978462687581)
        ·
          refine ⟨32549428751525241923507843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86798476670733978462687581 32549428751525241923507843)
          ·
            refine ⟨48824143127287862885261765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32549428751525241923507843 48824143127287862885261765)
            ·
              refine ⟨9154526836366474290986581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48824143127287862885261765 9154526836366474290986581)
              ·
                refine ⟨107279611363669620597499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9154526836366474290986581 107279611363669620597499)
                ·
                  rfl

theorem cell23_5641010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_5641010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641010 prefixEnd_5641010 := by exact prefixLift 5641010
  have htrace : WordTrace (prefixWord ++ tailWord_5641010) baseStart_5641010 baseEnd_5641010 := by
    simpa [prefixWord, tailWord_5641010, baseEnd_5641010] using wordTrace_append hprefix tailTrace_5641010
  have hstable : (prefixWord ++ tailWord_5641010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641010).length < 2 ^ (prefixWord ++ tailWord_5641010).sum := by decide
  have hdescent : baseEnd_5641010 < baseStart_5641010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641021 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5641021 : Nat := 118140960795 + 5641021 * 2 ^ 59
def prefixEnd_5641021 : Nat := 4983230072969 + 3 ^ 40 * 5641021 * 2
def baseEnd_5641021 : Nat := 2896555155106279213094923

theorem tailTrace_5641021 : CollatzResearch.WordTrace tailWord_5641021 prefixEnd_5641021 2896555155106279213094923 := by
  unfold tailWord_5641021
  simp only [CollatzResearch.WordTrace]
  refine ⟨205744938496551801530946917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137163292331034534353964611 205744938496551801530946917)
  ·
    refine ⟨38577175968103462787052547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205744938496551801530946917 38577175968103462787052547)
    ·
      refine ⟨57865763952155194180578821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38577175968103462787052547 57865763952155194180578821)
      ·
        refine ⟨10849830741029098908858529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57865763952155194180578821 10849830741029098908858529)
        ·
          refine ⟨8137373055771824181643897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10849830741029098908858529 8137373055771824181643897)
          ·
            refine ⟨6103029791828868136232923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8137373055771824181643897 6103029791828868136232923)
            ·
              refine ⟨9154544687743302204349385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103029791828868136232923 9154544687743302204349385)
              ·
                refine ⟨6865908515807476653262039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9154544687743302204349385 6865908515807476653262039)
                ·
                  refine ⟨10298862773711214979893059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865908515807476653262039 10298862773711214979893059)
                  ·
                    refine ⟨15448294160566822469839589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10298862773711214979893059 15448294160566822469839589)
                    ·
                      refine ⟨2896555155106279213094923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15448294160566822469839589 2896555155106279213094923)
                      ·
                        rfl

theorem cell23_5641021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5641021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641021 prefixEnd_5641021 := by exact prefixLift 5641021
  have htrace : WordTrace (prefixWord ++ tailWord_5641021) baseStart_5641021 baseEnd_5641021 := by
    simpa [prefixWord, tailWord_5641021, baseEnd_5641021] using wordTrace_append hprefix tailTrace_5641021
  have hstable : (prefixWord ++ tailWord_5641021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641021).length < 2 ^ (prefixWord ++ tailWord_5641021).sum := by decide
  have hdescent : baseEnd_5641021 < baseStart_5641021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641041 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 1, 2, 3]
def baseStart_5641041 : Nat := 118140960795 + 5641041 * 2 ^ 59
def prefixEnd_5641041 : Nat := 4983230072969 + 3 ^ 40 * 5641041 * 2
def baseEnd_5641041 : Nat := 2896565424719369134844831

theorem tailTrace_5641041 : CollatzResearch.WordTrace tailWord_5641041 prefixEnd_5641041 2896565424719369134844831 := by
  unfold tailWord_5641041
  simp only [CollatzResearch.WordTrace]
  refine ⟨205745667956479344946674977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137163778637652896631116651 205745667956479344946674977)
  ·
    refine ⟨154309250967359508710006233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205745667956479344946674977 154309250967359508710006233)
    ·
      refine ⟨115731938225519631532504675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154309250967359508710006233 115731938225519631532504675)
      ·
        refine ⟨173597907338279447298757013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115731938225519631532504675 173597907338279447298757013)
        ·
          refine ⟨8137401906481849092129235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173597907338279447298757013 8137401906481849092129235)
          ·
            refine ⟨12206102859722773638193853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137401906481849092129235 12206102859722773638193853)
            ·
              refine ⟨4577288572396040114322695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12206102859722773638193853 4577288572396040114322695)
              ·
                refine ⟨6865932858594060171484043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577288572396040114322695 6865932858594060171484043)
                ·
                  refine ⟨10298899287891090257226065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865932858594060171484043 10298899287891090257226065)
                  ·
                    refine ⟨7724174465918317692919549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10298899287891090257226065 7724174465918317692919549)
                    ·
                      refine ⟨2896565424719369134844831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724174465918317692919549 2896565424719369134844831)
                      ·
                        rfl

theorem cell23_5641041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_5641041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641041 prefixEnd_5641041 := by exact prefixLift 5641041
  have htrace : WordTrace (prefixWord ++ tailWord_5641041) baseStart_5641041 baseEnd_5641041 := by
    simpa [prefixWord, tailWord_5641041, baseEnd_5641041] using wordTrace_append hprefix tailTrace_5641041
  have hstable : (prefixWord ++ tailWord_5641041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641041).length < 2 ^ (prefixWord ++ tailWord_5641041).sum := by decide
  have hdescent : baseEnd_5641041 < baseStart_5641041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641064 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5641064 : Nat := 118140960795 + 5641064 * 2 ^ 59
def prefixEnd_5641064 : Nat := 4983230072969 + 3 ^ 40 * 5641064 * 2
def baseEnd_5641064 : Nat := 2896577234774422544857225

theorem tailTrace_5641064 : CollatzResearch.WordTrace tailWord_5641064 prefixEnd_5641064 2896577234774422544857225 := by
  unfold tailWord_5641064
  simp only [CollatzResearch.WordTrace]
  refine ⟨102873253417698009937381123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137164337890264013249841497 102873253417698009937381123)
  ·
    refine ⟨154309880126547014906071685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102873253417698009937381123 154309880126547014906071685)
    ·
      refine ⟨28933102523727565294888441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154309880126547014906071685 28933102523727565294888441)
      ·
        refine ⟨21699826892795673971166331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28933102523727565294888441 21699826892795673971166331)
        ·
          refine ⟨32549740339193510956749497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21699826892795673971166331 32549740339193510956749497)
          ·
            refine ⟨24412305254395133217562123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32549740339193510956749497 24412305254395133217562123)
            ·
              refine ⟨36618457881592699826343185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24412305254395133217562123 36618457881592699826343185)
              ·
                refine ⟨27463843411194524869757389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36618457881592699826343185 27463843411194524869757389)
                ·
                  refine ⟨10298941279197946826159021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27463843411194524869757389 10298941279197946826159021)
                  ·
                    refine ⟨3862102979699230059809633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10298941279197946826159021 3862102979699230059809633)
                    ·
                      refine ⟨2896577234774422544857225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862102979699230059809633 2896577234774422544857225)
                      ·
                        rfl

theorem cell23_5641064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5641064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641064 prefixEnd_5641064 := by exact prefixLift 5641064
  have htrace : WordTrace (prefixWord ++ tailWord_5641064) baseStart_5641064 baseEnd_5641064 := by
    simpa [prefixWord, tailWord_5641064, baseEnd_5641064] using wordTrace_append hprefix tailTrace_5641064
  have hstable : (prefixWord ++ tailWord_5641064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641064).length < 2 ^ (prefixWord ++ tailWord_5641064).sum := by decide
  have hdescent : baseEnd_5641064 < baseStart_5641064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641080 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_5641080 : Nat := 118140960795 + 5641080 * 2 ^ 59
def prefixEnd_5641080 : Nat := 4983230072969 + 3 ^ 40 * 5641080 * 2
def baseEnd_5641080 : Nat := 2896585450464894482257151

theorem tailTrace_5641080 : CollatzResearch.WordTrace tailWord_5641080 prefixEnd_5641080 2896585450464894482257151 := by
  unfold tailWord_5641080
  simp only [CollatzResearch.WordTrace]
  refine ⟨102873545201669027303672347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137164726935558703071563129 102873545201669027303672347)
  ·
    refine ⟨154310317802503540955508521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102873545201669027303672347 154310317802503540955508521)
    ·
      refine ⟨115732738351877655716631391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154310317802503540955508521 115732738351877655716631391)
      ·
        refine ⟨173599107527816483574947087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115732738351877655716631391 173599107527816483574947087)
        ·
          refine ⟨260398661291724725362420631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173599107527816483574947087 260398661291724725362420631)
          ·
            refine ⟨390597991937587088043630947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260398661291724725362420631 390597991937587088043630947)
            ·
              refine ⟨585896987906380632065446421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390597991937587088043630947 585896987906380632065446421)
              ·
                refine ⟨27463921308111592128067801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 585896987906380632065446421 27463921308111592128067801)
                ·
                  refine ⟨20597940981083694096050851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27463921308111592128067801 20597940981083694096050851)
                  ·
                    refine ⟨30896911471625541144076277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20597940981083694096050851 30896911471625541144076277)
                    ·
                      refine ⟨2896585450464894482257151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30896911471625541144076277 2896585450464894482257151)
                      ·
                        rfl

theorem cell23_5641080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_5641080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641080 prefixEnd_5641080 := by exact prefixLift 5641080
  have htrace : WordTrace (prefixWord ++ tailWord_5641080) baseStart_5641080 baseEnd_5641080 := by
    simpa [prefixWord, tailWord_5641080, baseEnd_5641080] using wordTrace_append hprefix tailTrace_5641080
  have hstable : (prefixWord ++ tailWord_5641080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641080).length < 2 ^ (prefixWord ++ tailWord_5641080).sum := by decide
  have hdescent : baseEnd_5641080 < baseStart_5641080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641098 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5641098 : Nat := 118140960795 + 5641098 * 2 ^ 59
def prefixEnd_5641098 : Nat := 4983230072969 + 3 ^ 40 * 5641098 * 2
def baseEnd_5641098 : Nat := 2896594693116675411832069

theorem tailTrace_5641098 : CollatzResearch.WordTrace tailWord_5641098 prefixEnd_5641098 2896594693116675411832069 := by
  unfold tailWord_5641098
  simp only [CollatzResearch.WordTrace]
  refine ⟨51436936729318210920374987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137165164611515229120999965 51436936729318210920374987)
  ·
    refine ⟨77155405093977316380562481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51436936729318210920374987 77155405093977316380562481)
    ·
      refine ⟨57866553820482987285421861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77155405093977316380562481 57866553820482987285421861)
      ·
        refine ⟨10849978841340560116016599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57866553820482987285421861 10849978841340560116016599)
        ·
          refine ⟨16274968262010840174024899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849978841340560116016599 16274968262010840174024899)
          ·
            refine ⟨24412452393016260261037349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16274968262010840174024899 24412452393016260261037349)
            ·
              refine ⟨4577334823690548798944503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24412452393016260261037349 4577334823690548798944503)
              ·
                refine ⟨6866002235535823198416755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577334823690548798944503 6866002235535823198416755)
                ·
                  refine ⟨10299003353303734797625133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6866002235535823198416755 10299003353303734797625133)
                  ·
                    refine ⟨3862126257488900549109425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10299003353303734797625133 3862126257488900549109425)
                    ·
                      refine ⟨2896594693116675411832069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862126257488900549109425 2896594693116675411832069)
                      ·
                        rfl

theorem cell23_5641098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5641098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641098 prefixEnd_5641098 := by exact prefixLift 5641098
  have htrace : WordTrace (prefixWord ++ tailWord_5641098) baseStart_5641098 baseEnd_5641098 := by
    simpa [prefixWord, tailWord_5641098, baseEnd_5641098] using wordTrace_append hprefix tailTrace_5641098
  have hstable : (prefixWord ++ tailWord_5641098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641098).length < 2 ^ (prefixWord ++ tailWord_5641098).sum := by decide
  have hdescent : baseEnd_5641098 < baseStart_5641098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641117 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 7]
def baseStart_5641117 : Nat := 118140960795 + 5641117 * 2 ^ 59
def prefixEnd_5641117 : Nat := 4983230072969 + 3 ^ 40 * 5641117 * 2
def baseEnd_5641117 : Nat := 321844938805456759721609

theorem tailTrace_5641117 : CollatzResearch.WordTrace tailWord_5641117 prefixEnd_5641117 321844938805456759721609 := by
  unfold tailWord_5641117
  simp only [CollatzResearch.WordTrace]
  refine ⟨205748439904204009926441605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137165626602802673284294403 205748439904204009926441605)
  ·
    refine ⟨38577832482038251861207801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205748439904204009926441605 38577832482038251861207801)
    ·
      refine ⟨28933374361528688895905851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38577832482038251861207801 28933374361528688895905851)
      ·
        refine ⟨43400061542293033343858777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28933374361528688895905851 43400061542293033343858777)
        ·
          refine ⟨32550046156719775007894083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43400061542293033343858777 32550046156719775007894083)
          ·
            refine ⟨48825069235079662511841125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32550046156719775007894083 48825069235079662511841125)
            ·
              refine ⟨9154700481577436720970211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48825069235079662511841125 9154700481577436720970211)
              ·
                refine ⟨13732050722366155081455317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154700481577436720970211 13732050722366155081455317)
                ·
                  refine ⟨321844938805456759721609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13732050722366155081455317 321844938805456759721609)
                  ·
                    rfl

theorem cell23_5641117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_5641117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641117 prefixEnd_5641117 := by exact prefixLift 5641117
  have htrace : WordTrace (prefixWord ++ tailWord_5641117) baseStart_5641117 baseEnd_5641117 := by
    simpa [prefixWord, tailWord_5641117, baseEnd_5641117] using wordTrace_append hprefix tailTrace_5641117
  have hstable : (prefixWord ++ tailWord_5641117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641117).length < 2 ^ (prefixWord ++ tailWord_5641117).sum := by decide
  have hdescent : baseEnd_5641117 < baseStart_5641117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641167 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_5641167 : Nat := 118140960795 + 5641167 * 2 ^ 59
def prefixEnd_5641167 : Nat := 4983230072969 + 3 ^ 40 * 5641167 * 2
def baseEnd_5641167 : Nat := 2896630123281835641869251

theorem tailTrace_5641167 : CollatzResearch.WordTrace tailWord_5641167 prefixEnd_5641167 2896630123281835641869251 := by
  unfold tailWord_5641167
  simp only [CollatzResearch.WordTrace]
  refine ⟨205750263554022868465761755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137166842369348578977174503 205750263554022868465761755)
  ·
    refine ⟨308625395331034302698642633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205750263554022868465761755 308625395331034302698642633)
    ·
      refine ⟨231469046498275727023981975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308625395331034302698642633 231469046498275727023981975)
      ·
        refine ⟨347203569747413590535972963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231469046498275727023981975 347203569747413590535972963)
        ·
          refine ⟨520805354621120385803959445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347203569747413590535972963 520805354621120385803959445)
          ·
            refine ⟨24412750997865018084560599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 520805354621120385803959445 24412750997865018084560599)
            ·
              refine ⟨36619126496797527126840899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24412750997865018084560599 36619126496797527126840899)
              ·
                refine ⟨54928689745196290690261349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36619126496797527126840899 54928689745196290690261349)
                ·
                  refine ⟨10299129327224304504424003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54928689745196290690261349 10299129327224304504424003)
                  ·
                    refine ⟨15448693990836456756636005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10299129327224304504424003 15448693990836456756636005)
                    ·
                      refine ⟨2896630123281835641869251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15448693990836456756636005 2896630123281835641869251)
                      ·
                        rfl

theorem cell23_5641167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_5641167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641167 prefixEnd_5641167 := by exact prefixLift 5641167
  have htrace : WordTrace (prefixWord ++ tailWord_5641167) baseStart_5641167 baseEnd_5641167 := by
    simpa [prefixWord, tailWord_5641167, baseEnd_5641167] using wordTrace_append hprefix tailTrace_5641167
  have hstable : (prefixWord ++ tailWord_5641167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641167).length < 2 ^ (prefixWord ++ tailWord_5641167).sum := by decide
  have hdescent : baseEnd_5641167 < baseStart_5641167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641174 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5641174 : Nat := 118140960795 + 5641174 * 2 ^ 59
def prefixEnd_5641174 : Nat := 4983230072969 + 3 ^ 40 * 5641174 * 2
def baseEnd_5641174 : Nat := 2896633717646417114481719

theorem tailTrace_5641174 : CollatzResearch.WordTrace tailWord_5641174 prefixEnd_5641174 2896633717646417114481719 := by
  unfold tailWord_5641174
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859407429062344291329161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137167012576665005774177717 12859407429062344291329161)
  ·
    refine ⟨9644555571796758218496871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12859407429062344291329161 9644555571796758218496871)
    ·
      refine ⟨14466833357695137327745307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9644555571796758218496871 14466833357695137327745307)
      ·
        refine ⟨21700250036542705991617961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14466833357695137327745307 21700250036542705991617961)
        ·
          refine ⟨16275187527407029493713471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21700250036542705991617961 16275187527407029493713471)
          ·
            refine ⟨24412781291110544240570207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16275187527407029493713471 24412781291110544240570207)
            ·
              refine ⟨36619171936665816360855311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24412781291110544240570207 36619171936665816360855311)
              ·
                refine ⟨54928757904998724541282967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36619171936665816360855311 54928757904998724541282967)
                ·
                  refine ⟨82393136857498086811924451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54928757904998724541282967 82393136857498086811924451)
                  ·
                    refine ⟨123589705286247130217886677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82393136857498086811924451 123589705286247130217886677)
                    ·
                      refine ⟨2896633717646417114481719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123589705286247130217886677 2896633717646417114481719)
                      ·
                        rfl

theorem cell23_5641174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5641174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641174 prefixEnd_5641174 := by exact prefixLift 5641174
  have htrace : WordTrace (prefixWord ++ tailWord_5641174) baseStart_5641174 baseEnd_5641174 := by
    simpa [prefixWord, tailWord_5641174, baseEnd_5641174] using wordTrace_append hprefix tailTrace_5641174
  have hstable : (prefixWord ++ tailWord_5641174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641174).length < 2 ^ (prefixWord ++ tailWord_5641174).sum := by decide
  have hdescent : baseEnd_5641174 < baseStart_5641174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641224 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 6]
def baseStart_5641224 : Nat := 118140960795 + 5641224 * 2 ^ 59
def prefixEnd_5641224 : Nat := 4983230072969 + 3 ^ 40 * 5641224 * 2
def baseEnd_5641224 : Nat := 321851043519904657650721

theorem tailTrace_5641224 : CollatzResearch.WordTrace tailWord_5641224 prefixEnd_5641224 321851043519904657650721 := by
  unfold tailWord_5641224
  simp only [CollatzResearch.WordTrace]
  refine ⟨102876171257408183600293363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137168228343210911467057817 102876171257408183600293363)
  ·
    refine ⟨154314256886112275400440045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102876171257408183600293363 154314256886112275400440045)
    ·
      refine ⟨57867846332292103275165017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154314256886112275400440045 57867846332292103275165017)
      ·
        refine ⟨43400884749219077456373763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57867846332292103275165017 43400884749219077456373763)
        ·
          refine ⟨65101327123828616184560645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43400884749219077456373763 65101327123828616184560645)
          ·
            refine ⟨12206498835717865534605121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65101327123828616184560645 12206498835717865534605121)
            ·
              refine ⟨9154874126788399150953841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12206498835717865534605121 9154874126788399150953841)
              ·
                refine ⟨6866155595091299363215381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9154874126788399150953841 6866155595091299363215381)
                ·
                  refine ⟨321851043519904657650721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6866155595091299363215381 321851043519904657650721)
                  ·
                    rfl

theorem cell23_5641224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 6].length) (baseStart_5641224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641224 prefixEnd_5641224 := by exact prefixLift 5641224
  have htrace : WordTrace (prefixWord ++ tailWord_5641224) baseStart_5641224 baseEnd_5641224 := by
    simpa [prefixWord, tailWord_5641224, baseEnd_5641224] using wordTrace_append hprefix tailTrace_5641224
  have hstable : (prefixWord ++ tailWord_5641224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641224).length < 2 ^ (prefixWord ++ tailWord_5641224).sum := by decide
  have hdescent : baseEnd_5641224 < baseStart_5641224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641228 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_5641228 : Nat := 118140960795 + 5641228 * 2 ^ 59
def prefixEnd_5641228 : Nat := 4983230072969 + 3 ^ 40 * 5641228 * 2
def baseEnd_5641228 : Nat := 965553815200586634402157

theorem tailTrace_5641228 : CollatzResearch.WordTrace tailWord_5641228 prefixEnd_5641228 965553815200586634402157 := by
  unfold tailWord_5641228
  simp only [CollatzResearch.WordTrace]
  refine ⟨102876244203400937941866169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137168325604534583922488225 102876244203400937941866169)
  ·
    refine ⟨77157183152550703456399627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102876244203400937941866169 77157183152550703456399627)
    ·
      refine ⟨115735774728826055184599441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77157183152550703456399627 115735774728826055184599441)
      ·
        refine ⟨86801831046619541388449581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115735774728826055184599441 86801831046619541388449581)
        ·
          refine ⟨32550686642482328020668593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86801831046619541388449581 32550686642482328020668593)
          ·
            refine ⟨24413014981861746015501445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32550686642482328020668593 24413014981861746015501445)
            ·
              refine ⟨4577440309099077377906521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24413014981861746015501445 4577440309099077377906521)
              ·
                refine ⟨3433080231824308033429891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4577440309099077377906521 3433080231824308033429891)
                ·
                  refine ⟨5149620347736462050144837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433080231824308033429891 5149620347736462050144837)
                  ·
                    refine ⟨965553815200586634402157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149620347736462050144837 965553815200586634402157)
                    ·
                      rfl

theorem cell23_5641228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_5641228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641228 prefixEnd_5641228 := by exact prefixLift 5641228
  have htrace : WordTrace (prefixWord ++ tailWord_5641228) baseStart_5641228 baseEnd_5641228 := by
    simpa [prefixWord, tailWord_5641228, baseEnd_5641228] using wordTrace_append hprefix tailTrace_5641228
  have hstable : (prefixWord ++ tailWord_5641228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641228).length < 2 ^ (prefixWord ++ tailWord_5641228).sum := by decide
  have hdescent : baseEnd_5641228 < baseStart_5641228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641251 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 3]
def baseStart_5641251 : Nat := 118140960795 + 5641251 * 2 ^ 59
def prefixEnd_5641251 : Nat := 4983230072969 + 3 ^ 40 * 5641251 * 2
def baseEnd_5641251 : Nat := 2896673255656813313218865

theorem tailTrace_5641251 : CollatzResearch.WordTrace tailWord_5641251 prefixEnd_5641251 2896673255656813313218865 := by
  unfold tailWord_5641251
  simp only [CollatzResearch.WordTrace]
  refine ⟨205753327285718550811819607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137168884857145700541213071 205753327285718550811819607)
  ·
    refine ⟨308629990928577826217729411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205753327285718550811819607 308629990928577826217729411)
    ·
      refine ⟨462944986392866739326594117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308629990928577826217729411 462944986392866739326594117)
      ·
        refine ⟨86802184948662513623736397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 462944986392866739326594117 86802184948662513623736397)
        ·
          refine ⟨32550819355748442608901149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86802184948662513623736397 32550819355748442608901149)
          ·
            refine ⟨12206557258405665978337931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32550819355748442608901149 12206557258405665978337931)
            ·
              refine ⟨18309835887608498967506897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12206557258405665978337931 18309835887608498967506897)
              ·
                refine ⟨13732376915706374225630173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18309835887608498967506897 13732376915706374225630173)
                ·
                  refine ⟨5149641343389890334611315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13732376915706374225630173 5149641343389890334611315)
                  ·
                    refine ⟨7724462015084835501916973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149641343389890334611315 7724462015084835501916973)
                    ·
                      refine ⟨2896673255656813313218865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724462015084835501916973 2896673255656813313218865)
                      ·
                        rfl

theorem cell23_5641251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_5641251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641251 prefixEnd_5641251 := by exact prefixLift 5641251
  have htrace : WordTrace (prefixWord ++ tailWord_5641251) baseStart_5641251 baseEnd_5641251 := by
    simpa [prefixWord, tailWord_5641251, baseEnd_5641251] using wordTrace_append hprefix tailTrace_5641251
  have hstable : (prefixWord ++ tailWord_5641251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641251).length < 2 ^ (prefixWord ++ tailWord_5641251).sum := by decide
  have hdescent : baseEnd_5641251 < baseStart_5641251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641294 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_5641294 : Nat := 118140960795 + 5641294 * 2 ^ 59
def prefixEnd_5641294 : Nat := 4983230072969 + 3 ^ 40 * 5641294 * 2
def baseEnd_5641294 : Nat := 2896695335324956644981167

theorem tailTrace_5641294 : CollatzResearch.WordTrace tailWord_5641294 prefixEnd_5641294 2896695335324956644981167 := by
  unfold tailWord_5641294
  simp only [CollatzResearch.WordTrace]
  refine ⟨25719361953070346144454367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137169930416375179437089957 25719361953070346144454367)
  ·
    refine ⟨38579042929605519216681551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25719361953070346144454367 38579042929605519216681551)
    ·
      refine ⟨57868564394408278825022327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38579042929605519216681551 57868564394408278825022327)
      ·
        refine ⟨86802846591612418237533491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57868564394408278825022327 86802846591612418237533491)
        ·
          refine ⟨130204269887418627356300237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86802846591612418237533491 130204269887418627356300237)
          ·
            refine ⟨48826601207781985258612589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130204269887418627356300237 48826601207781985258612589)
            ·
              refine ⟨18309975452918244471979721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48826601207781985258612589 18309975452918244471979721)
              ·
                refine ⟨13732481589688683353984791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18309975452918244471979721 13732481589688683353984791)
                ·
                  refine ⟨20598722384533025030977187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13732481589688683353984791 20598722384533025030977187)
                  ·
                    refine ⟨30898083576799537546465781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20598722384533025030977187 30898083576799537546465781)
                    ·
                      refine ⟨2896695335324956644981167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30898083576799537546465781 2896695335324956644981167)
                      ·
                        rfl

theorem cell23_5641294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_5641294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641294 prefixEnd_5641294 := by exact prefixLift 5641294
  have htrace : WordTrace (prefixWord ++ tailWord_5641294) baseStart_5641294 baseEnd_5641294 := by
    simpa [prefixWord, tailWord_5641294, baseEnd_5641294] using wordTrace_append hprefix tailTrace_5641294
  have hstable : (prefixWord ++ tailWord_5641294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641294).length < 2 ^ (prefixWord ++ tailWord_5641294).sum := by decide
  have hdescent : baseEnd_5641294 < baseStart_5641294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641308 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_5641308 : Nat := 118140960795 + 5641308 * 2 ^ 59
def prefixEnd_5641308 : Nat := 4983230072969 + 3 ^ 40 * 5641308 * 2
def baseEnd_5641308 : Nat := 2896702524054119590206103

theorem tailTrace_5641308 : CollatzResearch.WordTrace tailWord_5641308 prefixEnd_5641308 2896702524054119590206103 := by
  unfold tailWord_5641308
  simp only [CollatzResearch.WordTrace]
  refine ⟨102877703123256024773322289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137170270831008033031096385 102877703123256024773322289)
  ·
    refine ⟨77158277342442018579991717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102877703123256024773322289 77158277342442018579991717)
    ·
      refine ⟨14467177001707878483748447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77158277342442018579991717 14467177001707878483748447)
      ·
        refine ⟨21700765502561817725622671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14467177001707878483748447 21700765502561817725622671)
        ·
          refine ⟨32551148253842726588434007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21700765502561817725622671 32551148253842726588434007)
          ·
            refine ⟨48826722380764089882651011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32551148253842726588434007 48826722380764089882651011)
            ·
              refine ⟨73240083571146134823976517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48826722380764089882651011 73240083571146134823976517)
              ·
                refine ⟨13732515669589900279495597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73240083571146134823976517 13732515669589900279495597)
                ·
                  refine ⟨5149693376096212604810849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13732515669589900279495597 5149693376096212604810849)
                  ·
                    refine ⟨3862270032072159453608137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5149693376096212604810849 3862270032072159453608137)
                    ·
                      refine ⟨2896702524054119590206103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862270032072159453608137 2896702524054119590206103)
                      ·
                        rfl

theorem cell23_5641308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_5641308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641308 prefixEnd_5641308 := by exact prefixLift 5641308
  have htrace : WordTrace (prefixWord ++ tailWord_5641308) baseStart_5641308 baseEnd_5641308 := by
    simpa [prefixWord, tailWord_5641308, baseEnd_5641308] using wordTrace_append hprefix tailTrace_5641308
  have hstable : (prefixWord ++ tailWord_5641308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641308).length < 2 ^ (prefixWord ++ tailWord_5641308).sum := by decide
  have hdescent : baseEnd_5641308 < baseStart_5641308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641311 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 3]
def baseStart_5641311 : Nat := 118140960795 + 5641311 * 2 ^ 59
def prefixEnd_5641311 : Nat := 4983230072969 + 3 ^ 40 * 5641311 * 2
def baseEnd_5641311 : Nat := 2896704064496083078468589

theorem tailTrace_5641311 : CollatzResearch.WordTrace tailWord_5641311 prefixEnd_5641311 2896704064496083078468589 := by
  unfold tailWord_5641311
  simp only [CollatzResearch.WordTrace]
  refine ⟨205755515665501181059003787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137170343777000787372669191 205755515665501181059003787)
  ·
    refine ⟨308633273498251771588505681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205755515665501181059003787 308633273498251771588505681)
    ·
      refine ⟨231474955123688828691379261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308633273498251771588505681 231474955123688828691379261)
      ·
        refine ⟨86803108171383310759267223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231474955123688828691379261 86803108171383310759267223)
        ·
          refine ⟨130204662257074966138900835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86803108171383310759267223 130204662257074966138900835)
          ·
            refine ⟨195306993385612449208351253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130204662257074966138900835 195306993385612449208351253)
            ·
              refine ⟨9155015314950583556641465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195306993385612449208351253 9155015314950583556641465)
              ·
                refine ⟨6866261486212937667481099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9155015314950583556641465 6866261486212937667481099)
                ·
                  refine ⟨10299392229319406501221649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6866261486212937667481099 10299392229319406501221649)
                  ·
                    refine ⟨7724544171989554875916237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10299392229319406501221649 7724544171989554875916237)
                    ·
                      refine ⟨2896704064496083078468589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724544171989554875916237 2896704064496083078468589)
                      ·
                        rfl

theorem cell23_5641311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_5641311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641311 prefixEnd_5641311 := by exact prefixLift 5641311
  have htrace : WordTrace (prefixWord ++ tailWord_5641311) baseStart_5641311 baseEnd_5641311 := by
    simpa [prefixWord, tailWord_5641311, baseEnd_5641311] using wordTrace_append hprefix tailTrace_5641311
  have hstable : (prefixWord ++ tailWord_5641311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641311).length < 2 ^ (prefixWord ++ tailWord_5641311).sum := by decide
  have hdescent : baseEnd_5641311 < baseStart_5641311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641324 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_5641324 : Nat := 118140960795 + 5641324 * 2 ^ 59
def prefixEnd_5641324 : Nat := 4983230072969 + 3 ^ 40 * 5641324 * 2
def baseEnd_5641324 : Nat := 2896710739744591527606029

theorem tailTrace_5641324 : CollatzResearch.WordTrace tailWord_5641324 prefixEnd_5641324 2896710739744591527606029 := by
  unfold tailWord_5641324
  simp only [CollatzResearch.WordTrace]
  refine ⟨102877994907227042139613513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137170659876302722852818017 102877994907227042139613513)
  ·
    refine ⟨77158496180420281604710135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102877994907227042139613513 77158496180420281604710135)
    ·
      refine ⟨115737744270630422407065203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77158496180420281604710135 115737744270630422407065203)
      ·
        refine ⟨173606616405945633610597805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115737744270630422407065203 173606616405945633610597805)
        ·
          refine ⟨65102481152229612603974177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173606616405945633610597805 65102481152229612603974177)
          ·
            refine ⟨48826860864172209452980633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65102481152229612603974177 48826860864172209452980633)
            ·
              refine ⟨36620145648129157089735475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48826860864172209452980633 36620145648129157089735475)
              ·
                refine ⟨54930218472193735634603213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36620145648129157089735475 54930218472193735634603213)
                ·
                  refine ⟨20598831927072650862976205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54930218472193735634603213 20598831927072650862976205)
                  ·
                    refine ⟨7724561972652244073616077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20598831927072650862976205 7724561972652244073616077)
                    ·
                      refine ⟨2896710739744591527606029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724561972652244073616077 2896710739744591527606029)
                      ·
                        rfl

theorem cell23_5641324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_5641324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641324 prefixEnd_5641324 := by exact prefixLift 5641324
  have htrace : WordTrace (prefixWord ++ tailWord_5641324) baseStart_5641324 baseEnd_5641324 := by
    simpa [prefixWord, tailWord_5641324, baseEnd_5641324] using wordTrace_append hprefix tailTrace_5641324
  have hstable : (prefixWord ++ tailWord_5641324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641324).length < 2 ^ (prefixWord ++ tailWord_5641324).sum := by decide
  have hdescent : baseEnd_5641324 < baseStart_5641324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641341 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_5641341 : Nat := 118140960795 + 5641341 * 2 ^ 59
def prefixEnd_5641341 : Nat := 4983230072969 + 3 ^ 40 * 5641341 * 2
def baseEnd_5641341 : Nat := 2896719468915717961093451

theorem tailTrace_5641341 : CollatzResearch.WordTrace tailWord_5641341 prefixEnd_5641341 2896719468915717961093451 := by
  unfold tailWord_5641341
  simp only [CollatzResearch.WordTrace]
  refine ⟨205756609855392496182595877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137171073236928330788397251 205756609855392496182595877)
  ·
    refine ⟨38579364347886093034236727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205756609855392496182595877 38579364347886093034236727)
    ·
      refine ⟨57869046521829139551355091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38579364347886093034236727 57869046521829139551355091)
      ·
        refine ⟨86803569782743709327032637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57869046521829139551355091 86803569782743709327032637)
        ·
          refine ⟨32551338668528890997637239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86803569782743709327032637 32551338668528890997637239)
          ·
            refine ⟨48827008002793336496455859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32551338668528890997637239 48827008002793336496455859)
            ·
              refine ⟨73240512004190004744683789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48827008002793336496455859 73240512004190004744683789)
              ·
                refine ⟨27465192001571251779256421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73240512004190004744683789 27465192001571251779256421)
                ·
                  refine ⟨5149723500294609708610579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27465192001571251779256421 5149723500294609708610579)
                  ·
                    refine ⟨7724585250441914562915869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149723500294609708610579 7724585250441914562915869)
                    ·
                      refine ⟨2896719468915717961093451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724585250441914562915869 2896719468915717961093451)
                      ·
                        rfl

theorem cell23_5641341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_5641341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641341 prefixEnd_5641341 := by exact prefixLift 5641341
  have htrace : WordTrace (prefixWord ++ tailWord_5641341) baseStart_5641341 baseEnd_5641341 := by
    simpa [prefixWord, tailWord_5641341, baseEnd_5641341] using wordTrace_append hprefix tailTrace_5641341
  have hstable : (prefixWord ++ tailWord_5641341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641341).length < 2 ^ (prefixWord ++ tailWord_5641341).sum := by decide
  have hdescent : baseEnd_5641341 < baseStart_5641341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641351 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_5641351 : Nat := 118140960795 + 5641351 * 2 ^ 59
def prefixEnd_5641351 : Nat := 4983230072969 + 3 ^ 40 * 5641351 * 2
def baseEnd_5641351 : Nat := 2896724603722262921968405

theorem tailTrace_5641351 : CollatzResearch.WordTrace tailWord_5641351 prefixEnd_5641351 2896724603722262921968405 := by
  unfold tailWord_5641351
  simp only [CollatzResearch.WordTrace]
  refine ⟨205756974585356267890459907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137171316390237511926973271 205756974585356267890459907)
  ·
    refine ⟨308635461878034401835689861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205756974585356267890459907 308635461878034401835689861)
    ·
      refine ⟨57869149102131450344191849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308635461878034401835689861 57869149102131450344191849)
      ·
        refine ⟨43401861826598587758143887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57869149102131450344191849 43401861826598587758143887)
        ·
          refine ⟨65102792739897881637215831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43401861826598587758143887 65102792739897881637215831)
          ·
            refine ⟨97654189109846822455823747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65102792739897881637215831 97654189109846822455823747)
            ·
              refine ⟨146481283664770233683735621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97654189109846822455823747 146481283664770233683735621)
              ·
                refine ⟨27465240687144418815700429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146481283664770233683735621 27465240687144418815700429)
                ·
                  refine ⟨10299465257679157055887661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27465240687144418815700429 10299465257679157055887661)
                  ·
                    refine ⟨3862299471629683895957873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10299465257679157055887661 3862299471629683895957873)
                    ·
                      refine ⟨2896724603722262921968405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862299471629683895957873 2896724603722262921968405)
                      ·
                        rfl

theorem cell23_5641351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_5641351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641351 prefixEnd_5641351 := by exact prefixLift 5641351
  have htrace : WordTrace (prefixWord ++ tailWord_5641351) baseStart_5641351 baseEnd_5641351 := by
    simpa [prefixWord, tailWord_5641351, baseEnd_5641351] using wordTrace_append hprefix tailTrace_5641351
  have hstable : (prefixWord ++ tailWord_5641351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641351).length < 2 ^ (prefixWord ++ tailWord_5641351).sum := by decide
  have hdescent : baseEnd_5641351 < baseStart_5641351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641352 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 2, 4]
def baseStart_5641352 : Nat := 118140960795 + 5641352 * 2 ^ 59
def prefixEnd_5641352 : Nat := 4983230072969 + 3 ^ 40 * 5641352 * 2
def baseEnd_5641352 : Nat := 965575039067639139351967

theorem tailTrace_5641352 : CollatzResearch.WordTrace tailWord_5641352 prefixEnd_5641352 965575039067639139351967 := by
  unfold tailWord_5641352
  simp only [CollatzResearch.WordTrace]
  refine ⟨102878505529176322530623155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137171340705568430040830873 102878505529176322530623155)
  ·
    refine ⟨154317758293764483795934733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102878505529176322530623155 154317758293764483795934733)
    ·
      refine ⟨57869159360161681423475525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154317758293764483795934733 57869159360161681423475525)
      ·
        refine ⟨10850467380030315266901661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57869159360161681423475525 10850467380030315266901661)
        ·
          refine ⟨4068925267511368225088123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10850467380030315266901661 4068925267511368225088123)
          ·
            refine ⟨6103387901267052337632185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068925267511368225088123 6103387901267052337632185)
            ·
              refine ⟨4577540925950289253224139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6103387901267052337632185 4577540925950289253224139)
              ·
                refine ⟨6866311388925433879836209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577540925950289253224139 6866311388925433879836209)
                ·
                  refine ⟨5149733541694075409877157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6866311388925433879836209 5149733541694075409877157)
                  ·
                    refine ⟨965575039067639139351967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149733541694075409877157 965575039067639139351967)
                    ·
                      rfl

theorem cell23_5641352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_5641352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641352 prefixEnd_5641352 := by exact prefixLift 5641352
  have htrace : WordTrace (prefixWord ++ tailWord_5641352) baseStart_5641352 baseEnd_5641352 := by
    simpa [prefixWord, tailWord_5641352, baseEnd_5641352] using wordTrace_append hprefix tailTrace_5641352
  have hstable : (prefixWord ++ tailWord_5641352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641352).length < 2 ^ (prefixWord ++ tailWord_5641352).sum := by decide
  have hdescent : baseEnd_5641352 < baseStart_5641352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641368 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 3, 3, 2]
def baseStart_5641368 : Nat := 118140960795 + 5641368 * 2 ^ 59
def prefixEnd_5641368 : Nat := 4983230072969 + 3 ^ 40 * 5641368 * 2
def baseEnd_5641368 : Nat := 2896733332893389355455827

theorem tailTrace_5641368 : CollatzResearch.WordTrace tailWord_5641368 prefixEnd_5641368 2896733332893389355455827 := by
  unfold tailWord_5641368
  simp only [CollatzResearch.WordTrace]
  refine ⟨102878797313147339896914379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137171729750863119862552505 102878797313147339896914379)
  ·
    refine ⟨154318195969721009845371569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102878797313147339896914379 154318195969721009845371569)
    ·
      refine ⟨115738646977290757384028677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154318195969721009845371569 115738646977290757384028677)
      ·
        refine ⟨21700996308242017009505377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115738646977290757384028677 21700996308242017009505377)
        ·
          refine ⟨16275747231181512757129033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21700996308242017009505377 16275747231181512757129033)
          ·
            refine ⟨12206810423386134567846775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16275747231181512757129033 12206810423386134567846775)
            ·
              refine ⟨18310215635079201851770163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12206810423386134567846775 18310215635079201851770163)
              ·
                refine ⟨27465323452618802777655245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18310215635079201851770163 27465323452618802777655245)
                ·
                  refine ⟨10299496294732051041620717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27465323452618802777655245 10299496294732051041620717)
                  ·
                    refine ⟨3862311110524519140607769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10299496294732051041620717 3862311110524519140607769)
                    ·
                      refine ⟨2896733332893389355455827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862311110524519140607769 2896733332893389355455827)
                      ·
                        rfl

theorem cell23_5641368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_5641368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641368 prefixEnd_5641368 := by exact prefixLift 5641368
  have htrace : WordTrace (prefixWord ++ tailWord_5641368) baseStart_5641368 baseEnd_5641368 := by
    simpa [prefixWord, tailWord_5641368, baseEnd_5641368] using wordTrace_append hprefix tailTrace_5641368
  have hstable : (prefixWord ++ tailWord_5641368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641368).length < 2 ^ (prefixWord ++ tailWord_5641368).sum := by decide
  have hdescent : baseEnd_5641368 < baseStart_5641368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641381 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 3, 4, 2]
def baseStart_5641381 : Nat := 118140960795 + 5641381 * 2 ^ 59
def prefixEnd_5641381 : Nat := 4983230072969 + 3 ^ 40 * 5641381 * 2
def baseEnd_5641381 : Nat := 2896740008141897804593267

theorem tailTrace_5641381 : CollatzResearch.WordTrace tailWord_5641381 prefixEnd_5641381 2896740008141897804593267 := by
  unfold tailWord_5641381
  simp only [CollatzResearch.WordTrace]
  refine ⟨205758068775247583014051997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137172045850165055342701331 205758068775247583014051997)
  ·
    refine ⟨77159275790717843630269499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205758068775247583014051997 77159275790717843630269499)
    ·
      refine ⟨115738913686076765445404249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77159275790717843630269499 115738913686076765445404249)
      ·
        refine ⟨86804185264557574084053187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115738913686076765445404249 86804185264557574084053187)
        ·
          refine ⟨130206277896836361126079781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86804185264557574084053187 130206277896836361126079781)
          ·
            refine ⟨24413677105656817711139959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130206277896836361126079781 24413677105656817711139959)
            ·
              refine ⟨36620515658485226566709939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24413677105656817711139959 36620515658485226566709939)
              ·
                refine ⟨54930773487727839850064909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36620515658485226566709939 54930773487727839850064909)
                ·
                  refine ⟨20599040057897939943774341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54930773487727839850064909 20599040057897939943774341)
                  ·
                    refine ⟨3862320010855863739457689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20599040057897939943774341 3862320010855863739457689)
                    ·
                      refine ⟨2896740008141897804593267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862320010855863739457689 2896740008141897804593267)
                      ·
                        rfl

theorem cell23_5641381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_5641381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641381 prefixEnd_5641381 := by exact prefixLift 5641381
  have htrace : WordTrace (prefixWord ++ tailWord_5641381) baseStart_5641381 baseEnd_5641381 := by
    simpa [prefixWord, tailWord_5641381, baseEnd_5641381] using wordTrace_append hprefix tailTrace_5641381
  have hstable : (prefixWord ++ tailWord_5641381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641381).length < 2 ^ (prefixWord ++ tailWord_5641381).sum := by decide
  have hdescent : baseEnd_5641381 < baseStart_5641381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641444 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_5641444 : Nat := 118140960795 + 5641444 * 2 ^ 59
def prefixEnd_5641444 : Nat := 4983230072969 + 3 ^ 40 * 5641444 * 2
def baseEnd_5641444 : Nat := 2896772357423131058105477

theorem tailTrace_5641444 : CollatzResearch.WordTrace tailWord_5641444 prefixEnd_5641444 2896772357423131058105477 := by
  unfold tailWord_5641444
  simp only [CollatzResearch.WordTrace]
  refine ⟨102880183287009672386797693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137173577716012896515730257 102880183287009672386797693)
  ·
    refine ⟨38580068732628627145049135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102880183287009672386797693 38580068732628627145049135)
    ·
      refine ⟨57870103098942940717573703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38580068732628627145049135 57870103098942940717573703)
      ·
        refine ⟨86805154648414411076360555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57870103098942940717573703 86805154648414411076360555)
        ·
          refine ⟨130207731972621616614540833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86805154648414411076360555 130207731972621616614540833)
          ·
            refine ⟨97655798979466212460905625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130207731972621616614540833 97655798979466212460905625)
            ·
              refine ⟨73241849234599659345679219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97655798979466212460905625 73241849234599659345679219)
              ·
                refine ⟨109862773851899489018518829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73241849234599659345679219 109862773851899489018518829)
                ·
                  refine ⟨41198540194462308381944561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109862773851899489018518829 41198540194462308381944561)
                  ·
                    refine ⟨30898905145846731286458421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41198540194462308381944561 30898905145846731286458421)
                    ·
                      refine ⟨2896772357423131058105477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30898905145846731286458421 2896772357423131058105477)
                      ·
                        rfl

theorem cell23_5641444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_5641444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641444 prefixEnd_5641444 := by exact prefixLift 5641444
  have htrace : WordTrace (prefixWord ++ tailWord_5641444) baseStart_5641444 baseEnd_5641444 := by
    simpa [prefixWord, tailWord_5641444, baseEnd_5641444] using wordTrace_append hprefix tailTrace_5641444
  have hstable : (prefixWord ++ tailWord_5641444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641444).length < 2 ^ (prefixWord ++ tailWord_5641444).sum := by decide
  have hdescent : baseEnd_5641444 < baseStart_5641444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641481 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 3, 4]
def baseStart_5641481 : Nat := 118140960795 + 5641481 * 2 ^ 59
def prefixEnd_5641481 : Nat := 4983230072969 + 3 ^ 40 * 5641481 * 2
def baseEnd_5641481 : Nat := 965597118735782471114269

theorem tailTrace_5641481 : CollatzResearch.WordTrace tailWord_5641481 prefixEnd_5641481 965597118735782471114269 := by
  unfold tailWord_5641481
  simp only [CollatzResearch.WordTrace]
  refine ⟨205761716074885300092692297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137174477383256866728461531 205761716074885300092692297)
  ·
    refine ⟨154321287056163975069519223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205761716074885300092692297 154321287056163975069519223)
    ·
      refine ⟨231481930584245962604278835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154321287056163975069519223 231481930584245962604278835)
      ·
        refine ⟨347222895876368943906418253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231481930584245962604278835 347222895876368943906418253)
        ·
          refine ⟨130208585953638353964906845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347222895876368943906418253 130208585953638353964906845)
          ·
            refine ⟨48828219732614382736840067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130208585953638353964906845 48828219732614382736840067)
            ·
              refine ⟨73242329598921574105260101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48828219732614382736840067 73242329598921574105260101)
              ·
                refine ⟨13732936799797795144736269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73242329598921574105260101 13732936799797795144736269)
                ·
                  refine ⟨5149851299924173179276101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13732936799797795144736269 5149851299924173179276101)
                  ·
                    refine ⟨965597118735782471114269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149851299924173179276101 965597118735782471114269)
                    ·
                      rfl

theorem cell23_5641481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_5641481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641481 prefixEnd_5641481 := by exact prefixLift 5641481
  have htrace : WordTrace (prefixWord ++ tailWord_5641481) baseStart_5641481 baseEnd_5641481 := by
    simpa [prefixWord, tailWord_5641481, baseEnd_5641481] using wordTrace_append hprefix tailTrace_5641481
  have hstable : (prefixWord ++ tailWord_5641481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641481).length < 2 ^ (prefixWord ++ tailWord_5641481).sum := by decide
  have hdescent : baseEnd_5641481 < baseStart_5641481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641508 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_5641508 : Nat := 118140960795 + 5641508 * 2 ^ 59
def prefixEnd_5641508 : Nat := 4983230072969 + 3 ^ 40 * 5641508 * 2
def baseEnd_5641508 : Nat := 2896805220185018807705183

theorem tailTrace_5641508 : CollatzResearch.WordTrace tailWord_5641508 prefixEnd_5641508 2896805220185018807705183 := by
  unfold tailWord_5641508
  simp only [CollatzResearch.WordTrace]
  refine ⟨102881350422893741851962589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137175133897191655802616785 102881350422893741851962589)
  ·
    refine ⟨38580506408585153194485971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102881350422893741851962589 38580506408585153194485971)
    ·
      refine ⟨57870759612877729791728957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38580506408585153194485971 57870759612877729791728957)
      ·
        refine ⟨21701534854829148671898359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57870759612877729791728957 21701534854829148671898359)
        ·
          refine ⟨32552302282243723007847539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21701534854829148671898359 32552302282243723007847539)
          ·
            refine ⟨48828453423365584511771309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32552302282243723007847539 48828453423365584511771309)
            ·
              refine ⟨18310670033762094191914241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48828453423365584511771309 18310670033762094191914241)
              ·
                refine ⟨13733002525321570643935681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18310670033762094191914241 13733002525321570643935681)
                ·
                  refine ⟨10299751893991177982951761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13733002525321570643935681 10299751893991177982951761)
                  ·
                    refine ⟨7724813920493383487213821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10299751893991177982951761 7724813920493383487213821)
                    ·
                      refine ⟨2896805220185018807705183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724813920493383487213821 2896805220185018807705183)
                      ·
                        rfl

theorem cell23_5641508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_5641508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641508 prefixEnd_5641508 := by exact prefixLift 5641508
  have htrace : WordTrace (prefixWord ++ tailWord_5641508) baseStart_5641508 baseEnd_5641508 := by
    simpa [prefixWord, tailWord_5641508, baseEnd_5641508] using wordTrace_append hprefix tailTrace_5641508
  have hstable : (prefixWord ++ tailWord_5641508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641508).length < 2 ^ (prefixWord ++ tailWord_5641508).sum := by decide
  have hdescent : baseEnd_5641508 < baseStart_5641508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641555 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 1, 1, 3]
def baseStart_5641555 : Nat := 118140960795 + 5641555 * 2 ^ 59
def prefixEnd_5641555 : Nat := 4983230072969 + 3 ^ 40 * 5641555 * 2
def baseEnd_5641555 : Nat := 2896829353775780123817467

theorem tailTrace_5641555 : CollatzResearch.WordTrace tailWord_5641555 prefixEnd_5641555 2896829353775780123817467 := by
  unfold tailWord_5641555
  simp only [CollatzResearch.WordTrace]
  refine ⟨205764415076617210730886119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137176276717744807153924079 205764415076617210730886119)
  ·
    refine ⟨308646622614925816096329179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205764415076617210730886119 308646622614925816096329179)
    ·
      refine ⟨462969933922388724144493769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308646622614925816096329179 462969933922388724144493769)
      ·
        refine ⟨347227450441791543108370327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462969933922388724144493769 347227450441791543108370327)
        ·
          refine ⟨520841175662687314662555491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347227450441791543108370327 520841175662687314662555491)
          ·
            refine ⟨781261763494030971993833237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520841175662687314662555491 781261763494030971993833237)
            ·
              refine ⟨36621645163782701812210933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 781261763494030971993833237 36621645163782701812210933)
              ·
                refine ⟨3433279234104628294894775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36621645163782701812210933 3433279234104628294894775)
                ·
                  refine ⟨5149918851156942442342163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433279234104628294894775 5149918851156942442342163)
                  ·
                    refine ⟨7724878276735413663513245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149918851156942442342163 7724878276735413663513245)
                    ·
                      refine ⟨2896829353775780123817467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724878276735413663513245 2896829353775780123817467)
                      ·
                        rfl

theorem cell23_5641555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 1, 3].length) (baseStart_5641555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641555 prefixEnd_5641555 := by exact prefixLift 5641555
  have htrace : WordTrace (prefixWord ++ tailWord_5641555) baseStart_5641555 baseEnd_5641555 := by
    simpa [prefixWord, tailWord_5641555, baseEnd_5641555] using wordTrace_append hprefix tailTrace_5641555
  have hstable : (prefixWord ++ tailWord_5641555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641555).length < 2 ^ (prefixWord ++ tailWord_5641555).sum := by decide
  have hdescent : baseEnd_5641555 < baseStart_5641555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641572 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_5641572 : Nat := 118140960795 + 5641572 * 2 ^ 59
def prefixEnd_5641572 : Nat := 4983230072969 + 3 ^ 40 * 5641572 * 2
def baseEnd_5641572 : Nat := 2896838082946906557304889

theorem tailTrace_5641572 : CollatzResearch.WordTrace tailWord_5641572 prefixEnd_5641572 2896838082946906557304889 := by
  unfold tailWord_5641572
  simp only [CollatzResearch.WordTrace]
  refine ⟨102882517558777811317127485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137176690078370415089503313 102882517558777811317127485)
  ·
    refine ⟨38580944084541679243922807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102882517558777811317127485 38580944084541679243922807)
    ·
      refine ⟨57871416126812518865884211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38580944084541679243922807 57871416126812518865884211)
      ·
        refine ⟨86807124190218778298826317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57871416126812518865884211 86807124190218778298826317)
        ·
          refine ⟨32552671571332041862059869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86807124190218778298826317 32552671571332041862059869)
          ·
            refine ⟨12207251839249515698272451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32552671571332041862059869 12207251839249515698272451)
            ·
              refine ⟨18310877758874273547408677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12207251839249515698272451 18310877758874273547408677)
              ·
                refine ⟨3433289579788926290139127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18310877758874273547408677 3433289579788926290139127)
                ·
                  refine ⟨5149934369683389435208691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433289579788926290139127 5149934369683389435208691)
                  ·
                    refine ⟨7724901554525084152813037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149934369683389435208691 7724901554525084152813037)
                    ·
                      refine ⟨2896838082946906557304889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7724901554525084152813037 2896838082946906557304889)
                      ·
                        rfl

theorem cell23_5641572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_5641572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641572 prefixEnd_5641572 := by exact prefixLift 5641572
  have htrace : WordTrace (prefixWord ++ tailWord_5641572) baseStart_5641572 baseEnd_5641572 := by
    simpa [prefixWord, tailWord_5641572, baseEnd_5641572] using wordTrace_append hprefix tailTrace_5641572
  have hstable : (prefixWord ++ tailWord_5641572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641572).length < 2 ^ (prefixWord ++ tailWord_5641572).sum := by decide
  have hdescent : baseEnd_5641572 < baseStart_5641572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641595 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 3, 2, 2]
def baseStart_5641595 : Nat := 118140960795 + 5641595 * 2 ^ 59
def prefixEnd_5641595 : Nat := 4983230072969 + 3 ^ 40 * 5641595 * 2
def baseEnd_5641595 : Nat := 2896849893001959967317283

theorem tailTrace_5641595 : CollatzResearch.WordTrace tailWord_5641595 prefixEnd_5641595 2896849893001959967317283 := by
  unfold tailWord_5641595
  simp only [CollatzResearch.WordTrace]
  refine ⟨205765873996472297562342239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137177249330981531708228159 205765873996472297562342239)
  ·
    refine ⟨308648810994708446343513359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205765873996472297562342239 308648810994708446343513359)
    ·
      refine ⟨462973216492062669515270039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308648810994708446343513359 462973216492062669515270039)
      ·
        refine ⟨694459824738094004272905059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462973216492062669515270039 694459824738094004272905059)
        ·
          refine ⟨1041689737107141006409357589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694459824738094004272905059 1041689737107141006409357589)
          ·
            refine ⟨48829206426897234675438637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1041689737107141006409357589 48829206426897234675438637)
            ·
              refine ⟨18310952410086463003289489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48829206426897234675438637 18310952410086463003289489)
              ·
                refine ⟨13733214307564847252467117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18310952410086463003289489 13733214307564847252467117)
                ·
                  refine ⟨5149955365336817719675169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13733214307564847252467117 5149955365336817719675169)
                  ·
                    refine ⟨3862466524002613289756377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5149955365336817719675169 3862466524002613289756377)
                    ·
                      refine ⟨2896849893001959967317283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862466524002613289756377 2896849893001959967317283)
                      ·
                        rfl

theorem cell23_5641595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 2, 2].length) (baseStart_5641595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641595 prefixEnd_5641595 := by exact prefixLift 5641595
  have htrace : WordTrace (prefixWord ++ tailWord_5641595) baseStart_5641595 baseEnd_5641595 := by
    simpa [prefixWord, tailWord_5641595, baseEnd_5641595] using wordTrace_append hprefix tailTrace_5641595
  have hstable : (prefixWord ++ tailWord_5641595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641595).length < 2 ^ (prefixWord ++ tailWord_5641595).sum := by decide
  have hdescent : baseEnd_5641595 < baseStart_5641595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641608 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5641608 : Nat := 118140960795 + 5641608 * 2 ^ 59
def prefixEnd_5641608 : Nat := 4983230072969 + 3 ^ 40 * 5641608 * 2
def baseEnd_5641608 : Nat := 2896856568250468416454723

theorem tailTrace_5641608 : CollatzResearch.WordTrace tailWord_5641608 prefixEnd_5641608 2896856568250468416454723 := by
  unfold tailWord_5641608
  simp only [CollatzResearch.WordTrace]
  refine ⟨102883174072712600391282739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137177565430283467188376985 102883174072712600391282739)
  ·
    refine ⟨154324761109068900586924109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102883174072712600391282739 154324761109068900586924109)
    ·
      refine ⟨57871785415900837720096541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154324761109068900586924109 57871785415900837720096541)
      ·
        refine ⟨21701919530962814145036203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57871785415900837720096541 21701919530962814145036203)
        ·
          refine ⟨32552879296444221217554305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21701919530962814145036203 32552879296444221217554305)
          ·
            refine ⟨24414659472333165913165729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32552879296444221217554305 24414659472333165913165729)
            ·
              refine ⟨18310994604249874434874297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24414659472333165913165729 18310994604249874434874297)
              ·
                refine ⟨13733245953187405826155723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18310994604249874434874297 13733245953187405826155723)
                ·
                  refine ⟨20599868929781108739233585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13733245953187405826155723 20599868929781108739233585)
                  ·
                    refine ⟨15449901697335831554425189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20599868929781108739233585 15449901697335831554425189)
                    ·
                      refine ⟨2896856568250468416454723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15449901697335831554425189 2896856568250468416454723)
                      ·
                        rfl

theorem cell23_5641608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5641608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641608 prefixEnd_5641608 := by exact prefixLift 5641608
  have htrace : WordTrace (prefixWord ++ tailWord_5641608) baseStart_5641608 baseEnd_5641608 := by
    simpa [prefixWord, tailWord_5641608, baseEnd_5641608] using wordTrace_append hprefix tailTrace_5641608
  have hstable : (prefixWord ++ tailWord_5641608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641608).length < 2 ^ (prefixWord ++ tailWord_5641608).sum := by decide
  have hdescent : baseEnd_5641608 < baseStart_5641608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641629 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_5641629 : Nat := 118140960795 + 5641629 * 2 ^ 59
def prefixEnd_5641629 : Nat := 4983230072969 + 3 ^ 40 * 5641629 * 2
def baseEnd_5641629 : Nat := 2896867351344212834292127

theorem tailTrace_5641629 : CollatzResearch.WordTrace tailWord_5641629 prefixEnd_5641629 2896867351344212834292127 := by
  unfold tailWord_5641629
  simp only [CollatzResearch.WordTrace]
  refine ⟨205767114078349121369079941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137178076052232747579386627 205767114078349121369079941)
  ·
    refine ⟨38581333889690460256702489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205767114078349121369079941 38581333889690460256702489)
    ·
      refine ⟨28936000417267845192526867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38581333889690460256702489 28936000417267845192526867)
      ·
        refine ⟨43404000625901767788790301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28936000417267845192526867 43404000625901767788790301)
        ·
          refine ⟨16276500234713162920796363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43404000625901767788790301 16276500234713162920796363)
          ·
            refine ⟨24414750352069744381194545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16276500234713162920796363 24414750352069744381194545)
            ·
              refine ⟨18311062764052308285895909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24414750352069744381194545 18311062764052308285895909)
              ·
                refine ⟨3433324268259807803605483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18311062764052308285895909 3433324268259807803605483)
                ·
                  refine ⟨5149986402389711705408225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433324268259807803605483 5149986402389711705408225)
                  ·
                    refine ⟨3862489801792283779056169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5149986402389711705408225 3862489801792283779056169)
                    ·
                      refine ⟨2896867351344212834292127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862489801792283779056169 2896867351344212834292127)
                      ·
                        rfl

theorem cell23_5641629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_5641629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641629 prefixEnd_5641629 := by exact prefixLift 5641629
  have htrace : WordTrace (prefixWord ++ tailWord_5641629) baseStart_5641629 baseEnd_5641629 := by
    simpa [prefixWord, tailWord_5641629, baseEnd_5641629] using wordTrace_append hprefix tailTrace_5641629
  have hstable : (prefixWord ++ tailWord_5641629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641629).length < 2 ^ (prefixWord ++ tailWord_5641629).sum := by decide
  have hdescent : baseEnd_5641629 < baseStart_5641629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641651 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4]
def baseStart_5641651 : Nat := 118140960795 + 5641651 * 2 ^ 59
def prefixEnd_5641651 : Nat := 4983230072969 + 3 ^ 40 * 5641651 * 2
def baseEnd_5641651 : Nat := 2896878647918611748217025

theorem tailTrace_5641651 : CollatzResearch.WordTrace tailWord_5641651 prefixEnd_5641651 2896878647918611748217025 := by
  unfold tailWord_5641651
  simp only [CollatzResearch.WordTrace]
  refine ⟨205767916484269419126380807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137178610989512946084253871 205767916484269419126380807)
  ·
    refine ⟨308651874726404128689571211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205767916484269419126380807 308651874726404128689571211)
    ·
      refine ⟨462977812089606193034356817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308651874726404128689571211 462977812089606193034356817)
      ·
        refine ⟨347233359067204644775767613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462977812089606193034356817 347233359067204644775767613)
        ·
          refine ⟨130212509650201741790912855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347233359067204644775767613 130212509650201741790912855)
          ·
            refine ⟨195318764475302612686369283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130212509650201741790912855 195318764475302612686369283)
            ·
              refine ⟨292978146712953919029553925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195318764475302612686369283 292978146712953919029553925)
              ·
                refine ⟨54933402508678859818041361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292978146712953919029553925 54933402508678859818041361)
                ·
                  refine ⟨41200051881509144863531021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54933402508678859818041361 41200051881509144863531021)
                  ·
                    refine ⟨15450019455565929323824133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41200051881509144863531021 15450019455565929323824133)
                    ·
                      refine ⟨2896878647918611748217025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15450019455565929323824133 2896878647918611748217025)
                      ·
                        rfl

theorem cell23_5641651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_5641651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641651 prefixEnd_5641651 := by exact prefixLift 5641651
  have htrace : WordTrace (prefixWord ++ tailWord_5641651) baseStart_5641651 baseEnd_5641651 := by
    simpa [prefixWord, tailWord_5641651, baseEnd_5641651] using wordTrace_append hprefix tailTrace_5641651
  have hstable : (prefixWord ++ tailWord_5641651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641651).length < 2 ^ (prefixWord ++ tailWord_5641651).sum := by decide
  have hdescent : baseEnd_5641651 < baseStart_5641651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641666 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5641666 : Nat := 118140960795 + 5641666 * 2 ^ 59
def prefixEnd_5641666 : Nat := 4983230072969 + 3 ^ 40 * 5641666 * 2
def baseEnd_5641666 : Nat := 2896886350128429189529457

theorem tailTrace_5641666 : CollatzResearch.WordTrace tailWord_5641666 prefixEnd_5641666 2896886350128429189529457 := by
  unfold tailWord_5641666
  simp only [CollatzResearch.WordTrace]
  refine ⟨51442115894803769172044213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137178975719476717792117901 51442115894803769172044213)
  ·
    refine ⟨4822698365137853359879145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51442115894803769172044213 4822698365137853359879145)
    ·
      refine ⟨3617023773853390019909359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4822698365137853359879145 3617023773853390019909359)
      ·
        refine ⟨5425535660780085029864039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3617023773853390019909359 5425535660780085029864039)
        ·
          refine ⟨8138303491170127544796059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425535660780085029864039 8138303491170127544796059)
          ·
            refine ⟨12207455236755191317194089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8138303491170127544796059 12207455236755191317194089)
            ·
              refine ⟨9155591427566393487895567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12207455236755191317194089 9155591427566393487895567)
              ·
                refine ⟨13733387141349590231843351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9155591427566393487895567 13733387141349590231843351)
                ·
                  refine ⟨20600080712024385347765027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13733387141349590231843351 20600080712024385347765027)
                  ·
                    refine ⟨30900121068036578021647541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20600080712024385347765027 30900121068036578021647541)
                    ·
                      refine ⟨2896886350128429189529457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30900121068036578021647541 2896886350128429189529457)
                      ·
                        rfl

theorem cell23_5641666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5641666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641666 prefixEnd_5641666 := by exact prefixLift 5641666
  have htrace : WordTrace (prefixWord ++ tailWord_5641666) baseStart_5641666 baseEnd_5641666 := by
    simpa [prefixWord, tailWord_5641666, baseEnd_5641666] using wordTrace_append hprefix tailTrace_5641666
  have hstable : (prefixWord ++ tailWord_5641666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641666).length < 2 ^ (prefixWord ++ tailWord_5641666).sum := by decide
  have hdescent : baseEnd_5641666 < baseStart_5641666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641706 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_5641706 : Nat := 118140960795 + 5641706 * 2 ^ 59
def prefixEnd_5641706 : Nat := 4983230072969 + 3 ^ 40 * 5641706 * 2
def baseEnd_5641706 : Nat := 2896906889354609033029273

theorem tailTrace_5641706 : CollatzResearch.WordTrace tailWord_5641706 prefixEnd_5641706 2896906889354609033029273 := by
  unfold tailWord_5641706
  simp only [CollatzResearch.WordTrace]
  refine ⟨51442480624767540879908243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137179948332713442346421981 51442480624767540879908243)
  ·
    refine ⟨77163720937151311319862365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51442480624767540879908243 77163720937151311319862365)
    ·
      refine ⟨28936395351431741744948387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77163720937151311319862365 28936395351431741744948387)
      ·
        refine ⟨43404593027147612617422581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28936395351431741744948387 43404593027147612617422581)
        ·
          refine ⟨4069180596295088682883367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43404593027147612617422581 4069180596295088682883367)
          ·
            refine ⟨6103770894442633024325051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069180596295088682883367 6103770894442633024325051)
            ·
              refine ⟨9155656341663949536487577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103770894442633024325051 9155656341663949536487577)
              ·
                refine ⟨6866742256247962152365683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9155656341663949536487577 6866742256247962152365683)
                ·
                  refine ⟨10300113384371943228548525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6866742256247962152365683 10300113384371943228548525)
                  ·
                    refine ⟨3862542519139478710705697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10300113384371943228548525 3862542519139478710705697)
                    ·
                      refine ⟨2896906889354609033029273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862542519139478710705697 2896906889354609033029273)
                      ·
                        rfl

theorem cell23_5641706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_5641706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641706 prefixEnd_5641706 := by exact prefixLift 5641706
  have htrace : WordTrace (prefixWord ++ tailWord_5641706) baseStart_5641706 baseEnd_5641706 := by
    simpa [prefixWord, tailWord_5641706, baseEnd_5641706] using wordTrace_append hprefix tailTrace_5641706
  have hstable : (prefixWord ++ tailWord_5641706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641706).length < 2 ^ (prefixWord ++ tailWord_5641706).sum := by decide
  have hdescent : baseEnd_5641706 < baseStart_5641706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
