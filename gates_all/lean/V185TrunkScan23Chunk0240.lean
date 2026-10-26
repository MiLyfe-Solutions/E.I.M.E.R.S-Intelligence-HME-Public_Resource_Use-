import V185TrunkScan23Chunk0239

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1419958 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1419958 : Nat := 118140960795 + 1419958 * 2 ^ 59
def prefixEnd_1419958 : Nat := 4983230072969 + 3 ^ 40 * 1419958 * 2
def baseEnd_1419958 : Nat := 729120963197060641494739

theorem tailTrace_1419958 : CollatzResearch.WordTrace tailWord_1419958 prefixEnd_1419958 729120963197060641494739 := by
  unfold tailWord_1419958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236882686858884397771283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34526748659828100242893685 3236882686858884397771283)
  ·
    refine ⟨4855324030288326596656925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3236882686858884397771283 4855324030288326596656925)
    ·
      refine ⟨1820746511358122473746347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4855324030288326596656925 1820746511358122473746347)
      ·
        refine ⟨2731119767037183710619521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820746511358122473746347 2731119767037183710619521)
        ·
          refine ⟨2048339825277887782964641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731119767037183710619521 2048339825277887782964641)
          ·
            refine ⟨1536254868958415837223481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2048339825277887782964641 1536254868958415837223481)
            ·
              refine ⟨1152191151718811877917611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536254868958415837223481 1152191151718811877917611)
              ·
                refine ⟨1728286727578217816876417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152191151718811877917611 1728286727578217816876417)
                ·
                  refine ⟨1296215045683663362657313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1728286727578217816876417 1296215045683663362657313)
                  ·
                    refine ⟨972161284262747521992985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1296215045683663362657313 972161284262747521992985)
                    ·
                      refine ⟨729120963197060641494739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972161284262747521992985 729120963197060641494739)
                      ·
                        rfl

theorem cell23_1419958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1419958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419958 prefixEnd_1419958 := by exact prefixLift 1419958
  have htrace : WordTrace (prefixWord ++ tailWord_1419958) baseStart_1419958 baseEnd_1419958 := by
    simpa [prefixWord, tailWord_1419958, baseEnd_1419958] using wordTrace_append hprefix tailTrace_1419958
  have hstable : (prefixWord ++ tailWord_1419958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419958).length < 2 ^ (prefixWord ++ tailWord_1419958).sum := by decide
  have hdescent : baseEnd_1419958 < baseStart_1419958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419980 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1419980 : Nat := 118140960795 + 1419980 * 2 ^ 59
def prefixEnd_1419980 : Nat := 4983230072969 + 3 ^ 40 * 1419980 * 2
def baseEnd_1419980 : Nat := 729132259771459555419637

theorem tailTrace_1419980 : CollatzResearch.WordTrace tailWord_1419980 prefixEnd_1419980 729132259771459555419637 := by
  unfold tailWord_1419980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895462697831224060820697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34527283597108298747760929 25895462697831224060820697)
  ·
    refine ⟨19421597023373418045615523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25895462697831224060820697 19421597023373418045615523)
    ·
      refine ⟨29132395535060127068423285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19421597023373418045615523 29132395535060127068423285)
      ·
        refine ⟨2731162081411886912664683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29132395535060127068423285 2731162081411886912664683)
        ·
          refine ⟨4096743122117830368997025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731162081411886912664683 4096743122117830368997025)
          ·
            refine ⟨3072557341588372776747769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4096743122117830368997025 3072557341588372776747769)
            ·
              refine ⟨2304418006191279582560827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3072557341588372776747769 2304418006191279582560827)
              ·
                refine ⟨3456627009286919373841241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304418006191279582560827 3456627009286919373841241)
                ·
                  refine ⟨2592470256965189530380931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3456627009286919373841241 2592470256965189530380931)
                  ·
                    refine ⟨3888705385447784295571397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2592470256965189530380931 3888705385447784295571397)
                    ·
                      refine ⟨729132259771459555419637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3888705385447784295571397 729132259771459555419637)
                      ·
                        rfl

theorem cell23_1419980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1419980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419980 prefixEnd_1419980 := by exact prefixLift 1419980
  have htrace : WordTrace (prefixWord ++ tailWord_1419980) baseStart_1419980 baseEnd_1419980 := by
    simpa [prefixWord, tailWord_1419980, baseEnd_1419980] using wordTrace_append hprefix tailTrace_1419980
  have hstable : (prefixWord ++ tailWord_1419980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419980).length < 2 ^ (prefixWord ++ tailWord_1419980).sum := by decide
  have hdescent : baseEnd_1419980 < baseStart_1419980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420003 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 6]
def baseStart_1420003 : Nat := 118140960795 + 1420003 * 2 ^ 59
def prefixEnd_1420003 : Nat := 4983230072969 + 3 ^ 40 * 1420003 * 2
def baseEnd_1420003 : Nat := 81016007758501440603559

theorem tailTrace_1420003 : CollatzResearch.WordTrace tailWord_1420003 prefixEnd_1420003 81016007758501440603559 := by
  unfold tailWord_1420003
  simp only [CollatzResearch.WordTrace]
  refine ⟨51791764274579123049728663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34527842849719415366485775 51791764274579123049728663)
  ·
    refine ⟨77687646411868684574592995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51791764274579123049728663 77687646411868684574592995)
    ·
      refine ⟨116531469617803026861889493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77687646411868684574592995 116531469617803026861889493)
      ·
        refine ⟨2731206319167258442075535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 116531469617803026861889493 2731206319167258442075535)
        ·
          refine ⟨4096809478750887663113303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731206319167258442075535 4096809478750887663113303)
          ·
            refine ⟨6145214218126331494669955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096809478750887663113303 6145214218126331494669955)
            ·
              refine ⟨9217821327189497242004933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145214218126331494669955 9217821327189497242004933)
              ·
                refine ⟨1728341498848030732875925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9217821327189497242004933 1728341498848030732875925)
                ·
                  refine ⟨81016007758501440603559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1728341498848030732875925 81016007758501440603559)
                  ·
                    rfl

theorem cell23_1420003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 6].length) (baseStart_1420003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420003 prefixEnd_1420003 := by exact prefixLift 1420003
  have htrace : WordTrace (prefixWord ++ tailWord_1420003) baseStart_1420003 baseEnd_1420003 := by
    simpa [prefixWord, tailWord_1420003, baseEnd_1420003] using wordTrace_append hprefix tailTrace_1420003
  have hstable : (prefixWord ++ tailWord_1420003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420003).length < 2 ^ (prefixWord ++ tailWord_1420003).sum := by decide
  have hdescent : baseEnd_1420003 < baseStart_1420003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420016 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_1420016 : Nat := 118140960795 + 1420016 * 2 ^ 59
def prefixEnd_1420016 : Nat := 4983230072969 + 3 ^ 40 * 1420016 * 2
def baseEnd_1420016 : Nat := 243050248358340471523157

theorem tailTrace_1420016 : CollatzResearch.WordTrace tailWord_1420016 prefixEnd_1420016 243050248358340471523157 := by
  unfold tailWord_1420016
  simp only [CollatzResearch.WordTrace]
  refine ⟨25896119211766013134975951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34528158949021350846634601 25896119211766013134975951)
  ·
    refine ⟨38844178817649019702463927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25896119211766013134975951 38844178817649019702463927)
    ·
      refine ⟨58266268226473529553695891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38844178817649019702463927 58266268226473529553695891)
      ·
        refine ⟨87399402339710294330543837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58266268226473529553695891 87399402339710294330543837)
        ·
          refine ⟨32774775877391360373953939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87399402339710294330543837 32774775877391360373953939)
          ·
            refine ⟨49162163816087040560930909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32774775877391360373953939 49162163816087040560930909)
            ·
              refine ⟨18435811431032640210349091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49162163816087040560930909 18435811431032640210349091)
              ·
                refine ⟨27653717146548960315523637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18435811431032640210349091 27653717146548960315523637)
                ·
                  refine ⟨2592535982488965029580341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27653717146548960315523637 2592535982488965029580341)
                  ·
                    refine ⟨243050248358340471523157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2592535982488965029580341 243050248358340471523157)
                    ·
                      rfl

theorem cell23_1420016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_1420016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420016 prefixEnd_1420016 := by exact prefixLift 1420016
  have htrace : WordTrace (prefixWord ++ tailWord_1420016) baseStart_1420016 baseEnd_1420016 := by
    simpa [prefixWord, tailWord_1420016, baseEnd_1420016] using wordTrace_append hprefix tailTrace_1420016
  have hstable : (prefixWord ++ tailWord_1420016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420016).length < 2 ^ (prefixWord ++ tailWord_1420016).sum := by decide
  have hdescent : baseEnd_1420016 < baseStart_1420016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420023 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 1, 5, 2]
def baseStart_1420023 : Nat := 118140960795 + 1420023 * 2 ^ 59
def prefixEnd_1420023 : Nat := 4983230072969 + 3 ^ 40 * 1420023 * 2
def baseEnd_1420023 : Nat := 729154339439602887181939

theorem tailTrace_1420023 : CollatzResearch.WordTrace tailWord_1420023 prefixEnd_1420023 729154339439602887181939 := by
  unfold tailWord_1420023
  simp only [CollatzResearch.WordTrace]
  refine ⟨51792493734506666465456723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34528329156337777643637815 51792493734506666465456723)
  ·
    refine ⟨77688740601759999698185085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51792493734506666465456723 77688740601759999698185085)
    ·
      refine ⟨29133277725659999886819407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77688740601759999698185085 29133277725659999886819407)
      ·
        refine ⟨43699916588489999830229111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29133277725659999886819407 43699916588489999830229111)
        ·
          refine ⟨65549874882734999745343667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43699916588489999830229111 65549874882734999745343667)
          ·
            refine ⟨98324812324102499618015501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65549874882734999745343667 98324812324102499618015501)
            ·
              refine ⟨36871804621538437356755813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98324812324102499618015501 36871804621538437356755813)
              ·
                refine ⟨6913463366538457004391715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36871804621538437356755813 6913463366538457004391715)
                ·
                  refine ⟨10370195049807685506587573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913463366538457004391715 10370195049807685506587573)
                  ·
                    refine ⟨972205785919470516242585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10370195049807685506587573 972205785919470516242585)
                    ·
                      refine ⟨729154339439602887181939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972205785919470516242585 729154339439602887181939)
                      ·
                        rfl

theorem cell23_1420023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_1420023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420023 prefixEnd_1420023 := by exact prefixLift 1420023
  have htrace : WordTrace (prefixWord ++ tailWord_1420023) baseStart_1420023 baseEnd_1420023 := by
    simpa [prefixWord, tailWord_1420023, baseEnd_1420023] using wordTrace_append hprefix tailTrace_1420023
  have hstable : (prefixWord ++ tailWord_1420023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420023).length < 2 ^ (prefixWord ++ tailWord_1420023).sum := by decide
  have hdescent : baseEnd_1420023 < baseStart_1420023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420033 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1420033 : Nat := 118140960795 + 1420033 * 2 ^ 59
def prefixEnd_1420033 : Nat := 4983230072969 + 3 ^ 40 * 1420033 * 2
def baseEnd_1420033 : Nat := 243053158082049282685631

theorem tailTrace_1420033 : CollatzResearch.WordTrace tailWord_1420033 prefixEnd_1420033 243053158082049282685631 := by
  unfold tailWord_1420033
  simp only [CollatzResearch.WordTrace]
  refine ⟨51792858464470438173320753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34528572309646958782213835 51792858464470438173320753)
  ·
    refine ⟨38844643848352828629990565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51792858464470438173320753 38844643848352828629990565)
    ·
      refine ⟨7283370721566155368123231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38844643848352828629990565 7283370721566155368123231)
      ·
        refine ⟨10925056082349233052184847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283370721566155368123231 10925056082349233052184847)
        ·
          refine ⟨16387584123523849578277271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10925056082349233052184847 16387584123523849578277271)
          ·
            refine ⟨24581376185285774367415907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16387584123523849578277271 24581376185285774367415907)
            ·
              refine ⟨36872064277928661551123861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24581376185285774367415907 36872064277928661551123861)
              ·
                refine ⟨1728378013027906010208931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36872064277928661551123861 1728378013027906010208931)
                ·
                  refine ⟨2592567019541859015313397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728378013027906010208931 2592567019541859015313397)
                  ·
                    refine ⟨243053158082049282685631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2592567019541859015313397 243053158082049282685631)
                    ·
                      rfl

theorem cell23_1420033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1420033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420033 prefixEnd_1420033 := by exact prefixLift 1420033
  have htrace : WordTrace (prefixWord ++ tailWord_1420033) baseStart_1420033 baseEnd_1420033 := by
    simpa [prefixWord, tailWord_1420033, baseEnd_1420033] using wordTrace_append hprefix tailTrace_1420033
  have hstable : (prefixWord ++ tailWord_1420033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420033).length < 2 ^ (prefixWord ++ tailWord_1420033).sum := by decide
  have hdescent : baseEnd_1420033 < baseStart_1420033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420040 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_1420040 : Nat := 118140960795 + 1420040 * 2 ^ 59
def prefixEnd_1420040 : Nat := 4983230072969 + 3 ^ 40 * 1420040 * 2
def baseEnd_1420040 : Nat := 729163068610729320669361

theorem tailTrace_1420040 : CollatzResearch.WordTrace tailWord_1420040 prefixEnd_1420040 729163068610729320669361 := by
  unfold tailWord_1420040
  simp only [CollatzResearch.WordTrace]
  refine ⟨25896556887722539184412787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34528742516963385579217049 25896556887722539184412787)
  ·
    refine ⟨38844835331583808776619181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25896556887722539184412787 38844835331583808776619181)
    ·
      refine ⟨14566813249343928291232193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38844835331583808776619181 14566813249343928291232193)
      ·
        refine ⟨10925109937007946218424145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14566813249343928291232193 10925109937007946218424145)
        ·
          refine ⟨8193832452755959663818109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10925109937007946218424145 8193832452755959663818109)
          ·
            refine ⟨3072687169783484873931791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8193832452755959663818109 3072687169783484873931791)
            ·
              refine ⟨4609030754675227310897687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072687169783484873931791 4609030754675227310897687)
              ·
                refine ⟨6913546132012840966346531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609030754675227310897687 6913546132012840966346531)
                ·
                  refine ⟨10370319198019261449519797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913546132012840966346531 10370319198019261449519797)
                  ·
                    refine ⟨972217424814305760892481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10370319198019261449519797 972217424814305760892481)
                    ·
                      refine ⟨729163068610729320669361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972217424814305760892481 729163068610729320669361)
                      ·
                        rfl

theorem cell23_1420040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_1420040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420040 prefixEnd_1420040 := by exact prefixLift 1420040
  have htrace : WordTrace (prefixWord ++ tailWord_1420040) baseStart_1420040 baseEnd_1420040 := by
    simpa [prefixWord, tailWord_1420040, baseEnd_1420040] using wordTrace_append hprefix tailTrace_1420040
  have hstable : (prefixWord ++ tailWord_1420040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420040).length < 2 ^ (prefixWord ++ tailWord_1420040).sum := by decide
  have hdescent : baseEnd_1420040 < baseStart_1420040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420047 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 1, 1, 3]
def baseStart_1420047 : Nat := 118140960795 + 1420047 * 2 ^ 59
def prefixEnd_1420047 : Nat := 4983230072969 + 3 ^ 40 * 1420047 * 2
def baseEnd_1420047 : Nat := 729166662975310793281829

theorem tailTrace_1420047 : CollatzResearch.WordTrace tailWord_1420047 prefixEnd_1420047 729166662975310793281829 := by
  unfold tailWord_1420047
  simp only [CollatzResearch.WordTrace]
  refine ⟨51793369086419718564330395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34528912724279812376220263 51793369086419718564330395)
  ·
    refine ⟨77690053629629577846495593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51793369086419718564330395 77690053629629577846495593)
    ·
      refine ⟨58267540222222183384871695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77690053629629577846495593 58267540222222183384871695)
      ·
        refine ⟨87401310333333275077307543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58267540222222183384871695 87401310333333275077307543)
        ·
          refine ⟨131101965499999912615961315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87401310333333275077307543 131101965499999912615961315)
          ·
            refine ⟨196652948249999868923941973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131101965499999912615961315 196652948249999868923941973)
            ·
              refine ⟨2304526737304685963952445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 196652948249999868923941973 2304526737304685963952445)
              ·
                refine ⟨864197526489257236482167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2304526737304685963952445 864197526489257236482167)
                ·
                  refine ⟨1296296289733885854723251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864197526489257236482167 1296296289733885854723251)
                  ·
                    refine ⟨1944444434600828782084877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1296296289733885854723251 1944444434600828782084877)
                    ·
                      refine ⟨729166662975310793281829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1944444434600828782084877 729166662975310793281829)
                      ·
                        rfl

theorem cell23_1420047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 1, 3].length) (baseStart_1420047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420047 prefixEnd_1420047 := by exact prefixLift 1420047
  have htrace : WordTrace (prefixWord ++ tailWord_1420047) baseStart_1420047 baseEnd_1420047 := by
    simpa [prefixWord, tailWord_1420047, baseEnd_1420047] using wordTrace_append hprefix tailTrace_1420047
  have hstable : (prefixWord ++ tailWord_1420047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420047).length < 2 ^ (prefixWord ++ tailWord_1420047).sum := by decide
  have hdescent : baseEnd_1420047 < baseStart_1420047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420076 : List Nat := [2, 2, 1, 1, 1, 4, 2, 10]
def baseStart_1420076 : Nat := 118140960795 + 1420076 * 2 ^ 59
def prefixEnd_1420076 : Nat := 4983230072969 + 3 ^ 40 * 1420076 * 2
def baseEnd_1420076 : Nat := 27006724219047821474785

theorem tailTrace_1420076 : CollatzResearch.WordTrace tailWord_1420076 prefixEnd_1420076 27006724219047821474785 := by
  unfold tailWord_1420076
  simp only [CollatzResearch.WordTrace]
  refine ⟨25897213401657328258568041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34529617868876437678090721 25897213401657328258568041)
  ·
    refine ⟨19422910051242996193926031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25897213401657328258568041 19422910051242996193926031)
    ·
      refine ⟨29134365076864494290889047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19422910051242996193926031 29134365076864494290889047)
      ·
        refine ⟨43701547615296741436333571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29134365076864494290889047 43701547615296741436333571)
        ·
          refine ⟨65552321422945112154500357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43701547615296741436333571 65552321422945112154500357)
          ·
            refine ⟨12291060266802208528968817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65552321422945112154500357 12291060266802208528968817)
            ·
              refine ⟨9218295200101656396726613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12291060266802208528968817 9218295200101656396726613)
              ·
                refine ⟨27006724219047821474785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9218295200101656396726613 27006724219047821474785)
                ·
                  rfl

theorem cell23_1420076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 10].length) (baseStart_1420076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420076 prefixEnd_1420076 := by exact prefixLift 1420076
  have htrace : WordTrace (prefixWord ++ tailWord_1420076) baseStart_1420076 baseEnd_1420076 := by
    simpa [prefixWord, tailWord_1420076, baseEnd_1420076] using wordTrace_append hprefix tailTrace_1420076
  have hstable : (prefixWord ++ tailWord_1420076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420076).length < 2 ^ (prefixWord ++ tailWord_1420076).sum := by decide
  have hdescent : baseEnd_1420076 < baseStart_1420076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420083 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6]
def baseStart_1420083 : Nat := 118140960795 + 1420083 * 2 ^ 59
def prefixEnd_1420083 : Nat := 4983230072969 + 3 ^ 40 * 1420083 * 2
def baseEnd_1420083 : Nat := 729185148278872652431663

theorem tailTrace_1420083 : CollatzResearch.WordTrace tailWord_1420083 prefixEnd_1420083 729185148278872652431663 := by
  unfold tailWord_1420083
  simp only [CollatzResearch.WordTrace]
  refine ⟨51794682114289296712640903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34529788076192864475093935 51794682114289296712640903)
  ·
    refine ⟨77692023171433945068961355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51794682114289296712640903 77692023171433945068961355)
    ·
      refine ⟨116538034757150917603442033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77692023171433945068961355 116538034757150917603442033)
      ·
        refine ⟨87403526067863188202581525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116538034757150917603442033 87403526067863188202581525)
        ·
          refine ⟨4097040284431086946996009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87403526067863188202581525 4097040284431086946996009)
          ·
            refine ⟨3072780213323315210247007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097040284431086946996009 3072780213323315210247007)
            ·
              refine ⟨4609170319984972815370511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072780213323315210247007 4609170319984972815370511)
              ·
                refine ⟨6913755479977459223055767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609170319984972815370511 6913755479977459223055767)
                ·
                  refine ⟨10370633219966188834583651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913755479977459223055767 10370633219966188834583651)
                  ·
                    refine ⟨15555949829949283251875477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10370633219966188834583651 15555949829949283251875477)
                    ·
                      refine ⟨729185148278872652431663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15555949829949283251875477 729185148278872652431663)
                      ·
                        rfl

theorem cell23_1420083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_1420083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420083 prefixEnd_1420083 := by exact prefixLift 1420083
  have htrace : WordTrace (prefixWord ++ tailWord_1420083) baseStart_1420083 baseEnd_1420083 := by
    simpa [prefixWord, tailWord_1420083, baseEnd_1420083] using wordTrace_append hprefix tailTrace_1420083
  have hstable : (prefixWord ++ tailWord_1420083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420083).length < 2 ^ (prefixWord ++ tailWord_1420083).sum := by decide
  have hdescent : baseEnd_1420083 < baseStart_1420083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420096 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1420096 : Nat := 118140960795 + 1420096 * 2 ^ 59
def prefixEnd_1420096 : Nat := 4983230072969 + 3 ^ 40 * 1420096 * 2
def baseEnd_1420096 : Nat := 729191823527381101569103

theorem tailTrace_1420096 : CollatzResearch.WordTrace tailWord_1420096 prefixEnd_1420096 729191823527381101569103 := by
  unfold tailWord_1420096
  simp only [CollatzResearch.WordTrace]
  refine ⟨25897578131621099966432071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34530104175494799955242761 25897578131621099966432071)
  ·
    refine ⟨38846367197431649949648107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25897578131621099966432071 38846367197431649949648107)
    ·
      refine ⟨58269550796147474924472161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38846367197431649949648107 58269550796147474924472161)
      ·
        refine ⟨43702163097110606193354121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58269550796147474924472161 43702163097110606193354121)
        ·
          refine ⟨32776622322832954645015591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43702163097110606193354121 32776622322832954645015591)
          ·
            refine ⟨49164933484249431967523387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32776622322832954645015591 49164933484249431967523387)
            ·
              refine ⟨73747400226374147951285081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49164933484249431967523387 73747400226374147951285081)
              ·
                refine ⟨55310550169780610963463811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73747400226374147951285081 55310550169780610963463811)
                ·
                  refine ⟨82965825254670916445195717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55310550169780610963463811 82965825254670916445195717)
                  ·
                    refine ⟨15556092235250796833474197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82965825254670916445195717 15556092235250796833474197)
                    ·
                      refine ⟨729191823527381101569103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15556092235250796833474197 729191823527381101569103)
                      ·
                        rfl

theorem cell23_1420096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1420096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420096 prefixEnd_1420096 := by exact prefixLift 1420096
  have htrace : WordTrace (prefixWord ++ tailWord_1420096) baseStart_1420096 baseEnd_1420096 := by
    simpa [prefixWord, tailWord_1420096, baseEnd_1420096] using wordTrace_append hprefix tailTrace_1420096
  have hstable : (prefixWord ++ tailWord_1420096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420096).length < 2 ^ (prefixWord ++ tailWord_1420096).sum := by decide
  have hdescent : baseEnd_1420096 < baseStart_1420096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420103 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1420103 : Nat := 118140960795 + 1420103 * 2 ^ 59
def prefixEnd_1420103 : Nat := 4983230072969 + 3 ^ 40 * 1420103 * 2
def baseEnd_1420103 : Nat := 729195417891962574181571

theorem tailTrace_1420103 : CollatzResearch.WordTrace tailWord_1420103 prefixEnd_1420103 729195417891962574181571 := by
  unfold tailWord_1420103
  simp only [CollatzResearch.WordTrace]
  refine ⟨51795411574216840128368963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34530274382811226752245975 51795411574216840128368963)
  ·
    refine ⟨77693117361325260192553445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51795411574216840128368963 77693117361325260192553445)
    ·
      refine ⟨14567459505248486286103771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77693117361325260192553445 14567459505248486286103771)
      ·
        refine ⟨21851189257872729429155657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14567459505248486286103771 21851189257872729429155657)
        ·
          refine ⟨16388391943404547071866743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21851189257872729429155657 16388391943404547071866743)
          ·
            refine ⟨24582587915106820607800115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16388391943404547071866743 24582587915106820607800115)
            ·
              refine ⟨36873881872660230911700173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24582587915106820607800115 36873881872660230911700173)
              ·
                refine ⟨13827705702247586591887565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36873881872660230911700173 13827705702247586591887565)
                ·
                  refine ⟨5185389638342844971957837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13827705702247586591887565 5185389638342844971957837)
                  ·
                    refine ⟨1944521114378566864484189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5185389638342844971957837 1944521114378566864484189)
                    ·
                      refine ⟨729195417891962574181571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1944521114378566864484189 729195417891962574181571)
                      ·
                        rfl

theorem cell23_1420103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1420103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420103 prefixEnd_1420103 := by exact prefixLift 1420103
  have htrace : WordTrace (prefixWord ++ tailWord_1420103) baseStart_1420103 baseEnd_1420103 := by
    simpa [prefixWord, tailWord_1420103, baseEnd_1420103] using wordTrace_append hprefix tailTrace_1420103
  have hstable : (prefixWord ++ tailWord_1420103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420103).length < 2 ^ (prefixWord ++ tailWord_1420103).sum := by decide
  have hdescent : baseEnd_1420103 < baseStart_1420103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420121 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 1, 2, 2]
def baseStart_1420121 : Nat := 118140960795 + 1420121 * 2 ^ 59
def prefixEnd_1420121 : Nat := 4983230072969 + 3 ^ 40 * 1420121 * 2
def baseEnd_1420121 : Nat := 729204660543743503756489

theorem tailTrace_1420121 : CollatzResearch.WordTrace tailWord_1420121 prefixEnd_1420121 729204660543743503756489 := by
  unfold tailWord_1420121
  simp only [CollatzResearch.WordTrace]
  refine ⟨51796068088151629202524217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34530712058767752801682811 51796068088151629202524217)
  ·
    refine ⟨38847051066113721901893163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51796068088151629202524217 38847051066113721901893163)
    ·
      refine ⟨58270576599170582852839745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38847051066113721901893163 58270576599170582852839745)
      ·
        refine ⟨43702932449377937139629809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58270576599170582852839745 43702932449377937139629809)
        ·
          refine ⟨32777199337033452854722357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43702932449377937139629809 32777199337033452854722357)
          ·
            refine ⟨3072862437846886205130221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32777199337033452854722357 3072862437846886205130221)
            ·
              refine ⟨1152323414192582326923833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3072862437846886205130221 1152323414192582326923833)
              ·
                refine ⟨864242560644436745192875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152323414192582326923833 864242560644436745192875)
                ·
                  refine ⟨1296363840966655117789313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864242560644436745192875 1296363840966655117789313)
                  ·
                    refine ⟨972272880724991338341985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1296363840966655117789313 972272880724991338341985)
                    ·
                      refine ⟨729204660543743503756489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972272880724991338341985 729204660543743503756489)
                      ·
                        rfl

theorem cell23_1420121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_1420121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420121 prefixEnd_1420121 := by exact prefixLift 1420121
  have htrace : WordTrace (prefixWord ++ tailWord_1420121) baseStart_1420121 baseEnd_1420121 := by
    simpa [prefixWord, tailWord_1420121, baseEnd_1420121] using wordTrace_append hprefix tailTrace_1420121
  have hstable : (prefixWord ++ tailWord_1420121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420121).length < 2 ^ (prefixWord ++ tailWord_1420121).sum := by decide
  have hdescent : baseEnd_1420121 < baseStart_1420121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420147 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 1, 3, 2]
def baseStart_1420147 : Nat := 118140960795 + 1420147 * 2 ^ 59
def prefixEnd_1420147 : Nat := 4983230072969 + 3 ^ 40 * 1420147 * 2
def baseEnd_1420147 : Nat := 729218011040760402031369

theorem tailTrace_1420147 : CollatzResearch.WordTrace tailWord_1420147 prefixEnd_1420147 729218011040760402031369 := by
  unfold tailWord_1420147
  simp only [CollatzResearch.WordTrace]
  refine ⟨51797016386057435642970695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34531344257371623761980463 51797016386057435642970695)
  ·
    refine ⟨77695524579086153464456043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51797016386057435642970695 77695524579086153464456043)
    ·
      refine ⟨116543286868629230196684065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77695524579086153464456043 116543286868629230196684065)
      ·
        refine ⟨87407465151471922647513049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116543286868629230196684065 87407465151471922647513049)
        ·
          refine ⟨65555598863603941985634787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87407465151471922647513049 65555598863603941985634787)
          ·
            refine ⟨98333398295405912978452181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65555598863603941985634787 98333398295405912978452181)
            ·
              refine ⟨2304689022548576085432473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98333398295405912978452181 2304689022548576085432473)
              ·
                refine ⟨1728516766911432064074355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2304689022548576085432473 1728516766911432064074355)
                ·
                  refine ⟨2592775150367148096111533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728516766911432064074355 2592775150367148096111533)
                  ·
                    refine ⟨972290681387680536041825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2592775150367148096111533 972290681387680536041825)
                    ·
                      refine ⟨729218011040760402031369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972290681387680536041825 729218011040760402031369)
                      ·
                        rfl

theorem cell23_1420147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 3, 2].length) (baseStart_1420147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420147 prefixEnd_1420147 := by exact prefixLift 1420147
  have htrace : WordTrace (prefixWord ++ tailWord_1420147) baseStart_1420147 baseEnd_1420147 := by
    simpa [prefixWord, tailWord_1420147, baseEnd_1420147] using wordTrace_append hprefix tailTrace_1420147
  have hstable : (prefixWord ++ tailWord_1420147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420147).length < 2 ^ (prefixWord ++ tailWord_1420147).sum := by decide
  have hdescent : baseEnd_1420147 < baseStart_1420147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420163 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1420163 : Nat := 118140960795 + 1420163 * 2 ^ 59
def prefixEnd_1420163 : Nat := 4983230072969 + 3 ^ 40 * 1420163 * 2
def baseEnd_1420163 : Nat := 729226226731232339431295

theorem tailTrace_1420163 : CollatzResearch.WordTrace tailWord_1420163 prefixEnd_1420163 729226226731232339431295 := by
  unfold tailWord_1420163
  simp only [CollatzResearch.WordTrace]
  refine ⟨51797599953999470375553143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34531733302666313583702095 51797599953999470375553143)
  ·
    refine ⟨77696399930999205563329715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51797599953999470375553143 77696399930999205563329715)
    ·
      refine ⟨116544599896498808344994573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77696399930999205563329715 116544599896498808344994573)
      ·
        refine ⟨43704224961187053129372965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116544599896498808344994573 43704224961187053129372965)
        ·
          refine ⟨8194542180222572461757431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43704224961187053129372965 8194542180222572461757431)
          ·
            refine ⟨12291813270333858692636147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8194542180222572461757431 12291813270333858692636147)
            ·
              refine ⟨18437719905500788038954221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12291813270333858692636147 18437719905500788038954221)
              ·
                refine ⟨6914144964562795514607833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18437719905500788038954221 6914144964562795514607833)
                ·
                  refine ⟨5185608723422096635955875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6914144964562795514607833 5185608723422096635955875)
                  ·
                    refine ⟨7778413085133144953933813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185608723422096635955875 7778413085133144953933813)
                    ·
                      refine ⟨729226226731232339431295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7778413085133144953933813 729226226731232339431295)
                      ·
                        rfl

theorem cell23_1420163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1420163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420163 prefixEnd_1420163 := by exact prefixLift 1420163
  have htrace : WordTrace (prefixWord ++ tailWord_1420163) baseStart_1420163 baseEnd_1420163 := by
    simpa [prefixWord, tailWord_1420163, baseEnd_1420163] using wordTrace_append hprefix tailTrace_1420163
  have hstable : (prefixWord ++ tailWord_1420163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420163).length < 2 ^ (prefixWord ++ tailWord_1420163).sum := by decide
  have hdescent : baseEnd_1420163 < baseStart_1420163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420180 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1420180 : Nat := 118140960795 + 1420180 * 2 ^ 59
def prefixEnd_1420180 : Nat := 4983230072969 + 3 ^ 40 * 1420180 * 2
def baseEnd_1420180 : Nat := 729234955902358772918717

theorem tailTrace_1420180 : CollatzResearch.WordTrace tailWord_1420180 prefixEnd_1420180 729234955902358772918717 := by
  unfold tailWord_1420180
  simp only [CollatzResearch.WordTrace]
  refine ⟨25899109997468941139460997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34532146663291921519281329 25899109997468941139460997)
  ·
    refine ⟨4856083124525426463648937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25899109997468941139460997 4856083124525426463648937)
    ·
      refine ⟨3642062343394069847736703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4856083124525426463648937 3642062343394069847736703)
      ·
        refine ⟨5463093515091104771605055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642062343394069847736703 5463093515091104771605055)
        ·
          refine ⟨8194640272636657157407583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5463093515091104771605055 8194640272636657157407583)
          ·
            refine ⟨12291960408954985736111375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8194640272636657157407583 12291960408954985736111375)
            ·
              refine ⟨18437940613432478604167063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12291960408954985736111375 18437940613432478604167063)
              ·
                refine ⟨27656910920148717906250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18437940613432478604167063 27656910920148717906250595)
                ·
                  refine ⟨41485366380223076859375893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27656910920148717906250595 41485366380223076859375893)
                  ·
                    refine ⟨1944626549072956727783245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41485366380223076859375893 1944626549072956727783245)
                    ·
                      refine ⟨729234955902358772918717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1944626549072956727783245 729234955902358772918717)
                      ·
                        rfl

theorem cell23_1420180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1420180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420180 prefixEnd_1420180 := by exact prefixLift 1420180
  have htrace : WordTrace (prefixWord ++ tailWord_1420180) baseStart_1420180 baseEnd_1420180 := by
    simpa [prefixWord, tailWord_1420180, baseEnd_1420180] using wordTrace_append hprefix tailTrace_1420180
  have hstable : (prefixWord ++ tailWord_1420180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420180).length < 2 ^ (prefixWord ++ tailWord_1420180).sum := by decide
  have hdescent : baseEnd_1420180 < baseStart_1420180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420183 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 7]
def baseStart_1420183 : Nat := 118140960795 + 1420183 * 2 ^ 59
def prefixEnd_1420183 : Nat := 4983230072969 + 3 ^ 40 * 1420183 * 2
def baseEnd_1420183 : Nat := 81026277371591362353467

theorem tailTrace_1420183 : CollatzResearch.WordTrace tailWord_1420183 prefixEnd_1420183 81026277371591362353467 := by
  unfold tailWord_1420183
  simp only [CollatzResearch.WordTrace]
  refine ⟨51798329413927013791281203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34532219609284675860854135 51798329413927013791281203)
  ·
    refine ⟨77697494120890520686921805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51798329413927013791281203 77697494120890520686921805)
    ·
      refine ⟨29136560295333945257595677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77697494120890520686921805 29136560295333945257595677)
      ·
        refine ⟨10926210110750229471598379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29136560295333945257595677 10926210110750229471598379)
        ·
          refine ⟨16389315166125344207397569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10926210110750229471598379 16389315166125344207397569)
          ·
            refine ⟨12291986374594008155548177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16389315166125344207397569 12291986374594008155548177)
            ·
              refine ⟨9218989780945506116661133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12291986374594008155548177 9218989780945506116661133)
              ·
                refine ⟨3457121167854564793747925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9218989780945506116661133 3457121167854564793747925)
                ·
                  refine ⟨81026277371591362353467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3457121167854564793747925 81026277371591362353467)
                  ·
                    rfl

theorem cell23_1420183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 7].length) (baseStart_1420183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420183 prefixEnd_1420183 := by exact prefixLift 1420183
  have htrace : WordTrace (prefixWord ++ tailWord_1420183) baseStart_1420183 baseEnd_1420183 := by
    simpa [prefixWord, tailWord_1420183, baseEnd_1420183] using wordTrace_append hprefix tailTrace_1420183
  have hstable : (prefixWord ++ tailWord_1420183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420183).length < 2 ^ (prefixWord ++ tailWord_1420183).sum := by decide
  have hdescent : baseEnd_1420183 < baseStart_1420183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420194 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_1420194 : Nat := 118140960795 + 1420194 * 2 ^ 59
def prefixEnd_1420194 : Nat := 4983230072969 + 3 ^ 40 * 1420194 * 2
def baseEnd_1420194 : Nat := 729242144631521718143653

theorem tailTrace_1420194 : CollatzResearch.WordTrace tailWord_1420194 prefixEnd_1420194 729242144631521718143653 := by
  unfold tailWord_1420194
  simp only [CollatzResearch.WordTrace]
  refine ⟨12949682654221790667482909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34532487077924775113287757 12949682654221790667482909)
  ·
    refine ⟨4856130995333171500306091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12949682654221790667482909 4856130995333171500306091)
    ·
      refine ⟨7284196492999757250459137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4856130995333171500306091 7284196492999757250459137)
      ·
        refine ⟨5463147369749817937844353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7284196492999757250459137 5463147369749817937844353)
        ·
          refine ⟨4097360527312363453383265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5463147369749817937844353 4097360527312363453383265)
          ·
            refine ⟨3073020395484272590037449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097360527312363453383265 3073020395484272590037449)
            ·
              refine ⟨2304765296613204442528087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073020395484272590037449 2304765296613204442528087)
              ·
                refine ⟨3457147944919806663792131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304765296613204442528087 3457147944919806663792131)
                ·
                  refine ⟨5185721917379709995688197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457147944919806663792131 5185721917379709995688197)
                  ·
                    refine ⟨972322859508695624191537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5185721917379709995688197 972322859508695624191537)
                    ·
                      refine ⟨729242144631521718143653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972322859508695624191537 729242144631521718143653)
                      ·
                        rfl

theorem cell23_1420194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_1420194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420194 prefixEnd_1420194 := by exact prefixLift 1420194
  have htrace : WordTrace (prefixWord ++ tailWord_1420194) baseStart_1420194 baseEnd_1420194 := by
    simpa [prefixWord, tailWord_1420194, baseEnd_1420194] using wordTrace_append hprefix tailTrace_1420194
  have hstable : (prefixWord ++ tailWord_1420194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420194).length < 2 ^ (prefixWord ++ tailWord_1420194).sum := by decide
  have hdescent : baseEnd_1420194 < baseStart_1420194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420217 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 5]
def baseStart_1420217 : Nat := 118140960795 + 1420217 * 2 ^ 59
def prefixEnd_1420217 : Nat := 4983230072969 + 3 ^ 40 * 1420217 * 2
def baseEnd_1420217 : Nat := 81028217187397236461783

theorem tailTrace_1420217 : CollatzResearch.WordTrace tailWord_1420217 prefixEnd_1420217 81028217187397236461783 := by
  unfold tailWord_1420217
  simp only [CollatzResearch.WordTrace]
  refine ⟨51799569495803837598018905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34533046330535891732012603 51799569495803837598018905)
  ·
    refine ⟨38849677121852878198514179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51799569495803837598018905 38849677121852878198514179)
    ·
      refine ⟨58274515682779317297771269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38849677121852878198514179 58274515682779317297771269)
      ·
        refine ⟨10926471690521121993332113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58274515682779317297771269 10926471690521121993332113)
        ·
          refine ⟨8194853767890841494999085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10926471690521121993332113 8194853767890841494999085)
          ·
            refine ⟨3073070162959065560624657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8194853767890841494999085 3073070162959065560624657)
            ·
              refine ⟨2304802622219299170468493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073070162959065560624657 2304802622219299170468493)
              ·
                refine ⟨864300983332237188925685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2304802622219299170468493 864300983332237188925685)
                ·
                  refine ⟨81028217187397236461783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 864300983332237188925685 81028217187397236461783)
                  ·
                    rfl

theorem cell23_1420217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 5].length) (baseStart_1420217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420217 prefixEnd_1420217 := by exact prefixLift 1420217
  have htrace : WordTrace (prefixWord ++ tailWord_1420217) baseStart_1420217 baseEnd_1420217 := by
    simpa [prefixWord, tailWord_1420217, baseEnd_1420217] using wordTrace_append hprefix tailTrace_1420217
  have hstable : (prefixWord ++ tailWord_1420217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420217).length < 2 ^ (prefixWord ++ tailWord_1420217).sum := by decide
  have hdescent : baseEnd_1420217 < baseStart_1420217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420223 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1420223 : Nat := 118140960795 + 1420223 * 2 ^ 59
def prefixEnd_1420223 : Nat := 4983230072969 + 3 ^ 40 * 1420223 * 2
def baseEnd_1420223 : Nat := 729257035570502104681019

theorem tailTrace_1420223 : CollatzResearch.WordTrace tailWord_1420223 prefixEnd_1420223 729257035570502104681019 := by
  unfold tailWord_1420223
  simp only [CollatzResearch.WordTrace]
  refine ⟨51799788333782100622737323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34533192222521400415158215 51799788333782100622737323)
  ·
    refine ⟨77699682500673150934105985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51799788333782100622737323 77699682500673150934105985)
    ·
      refine ⟨58274761875504863200579489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77699682500673150934105985 58274761875504863200579489)
      ·
        refine ⟨43706071406628647400434617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58274761875504863200579489 43706071406628647400434617)
        ·
          refine ⟨32779553554971485550325963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43706071406628647400434617 32779553554971485550325963)
          ·
            refine ⟨49169330332457228325488945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32779553554971485550325963 49169330332457228325488945)
            ·
              refine ⟨36876997749342921244116709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49169330332457228325488945 36876997749342921244116709)
              ·
                refine ⟨6914437078001797733271883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36876997749342921244116709 6914437078001797733271883)
                ·
                  refine ⟨10371655617002696599907825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6914437078001797733271883 10371655617002696599907825)
                  ·
                    refine ⟨7778741712752022449930869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10371655617002696599907825 7778741712752022449930869)
                    ·
                      refine ⟨729257035570502104681019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7778741712752022449930869 729257035570502104681019)
                      ·
                        rfl

theorem cell23_1420223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1420223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420223 prefixEnd_1420223 := by exact prefixLift 1420223
  have htrace : WordTrace (prefixWord ++ tailWord_1420223) baseStart_1420223 baseEnd_1420223 := by
    simpa [prefixWord, tailWord_1420223, baseEnd_1420223] using wordTrace_append hprefix tailTrace_1420223
  have hstable : (prefixWord ++ tailWord_1420223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420223).length < 2 ^ (prefixWord ++ tailWord_1420223).sum := by decide
  have hdescent : baseEnd_1420223 < baseStart_1420223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420233 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_1420233 : Nat := 118140960795 + 1420233 * 2 ^ 59
def prefixEnd_1420233 : Nat := 4983230072969 + 3 ^ 40 * 1420233 * 2
def baseEnd_1420233 : Nat := 729262170377047065555973

theorem tailTrace_1420233 : CollatzResearch.WordTrace tailWord_1420233 prefixEnd_1420233 729262170377047065555973 := by
  unfold tailWord_1420233
  simp only [CollatzResearch.WordTrace]
  refine ⟨51800153063745872330601353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34533435375830581553734235 51800153063745872330601353)
  ·
    refine ⟨38850114797809404247951015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51800153063745872330601353 38850114797809404247951015)
    ·
      refine ⟨58275172196714106371926523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38850114797809404247951015 58275172196714106371926523)
      ·
        refine ⟨87412758295071159557889785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58275172196714106371926523 87412758295071159557889785)
        ·
          refine ⟨65559568721303369668417339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87412758295071159557889785 65559568721303369668417339)
          ·
            refine ⟨98339353081955054502626009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65559568721303369668417339 98339353081955054502626009)
            ·
              refine ⟨73754514811466290876969507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98339353081955054502626009 73754514811466290876969507)
              ·
                refine ⟨110631772217199436315454261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73754514811466290876969507 110631772217199436315454261)
                ·
                  refine ⟨10371728645362447154573837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110631772217199436315454261 10371728645362447154573837)
                  ·
                    refine ⟨3889398242010917682965189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10371728645362447154573837 3889398242010917682965189)
                    ·
                      refine ⟨729262170377047065555973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3889398242010917682965189 729262170377047065555973)
                      ·
                        rfl

theorem cell23_1420233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_1420233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420233 prefixEnd_1420233 := by exact prefixLift 1420233
  have htrace : WordTrace (prefixWord ++ tailWord_1420233) baseStart_1420233 baseEnd_1420233 := by
    simpa [prefixWord, tailWord_1420233, baseEnd_1420233] using wordTrace_append hprefix tailTrace_1420233
  have hstable : (prefixWord ++ tailWord_1420233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420233).length < 2 ^ (prefixWord ++ tailWord_1420233).sum := by decide
  have hdescent : baseEnd_1420233 < baseStart_1420233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420250 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1420250 : Nat := 118140960795 + 1420250 * 2 ^ 59
def prefixEnd_1420250 : Nat := 4983230072969 + 3 ^ 40 * 1420250 * 2
def baseEnd_1420250 : Nat := 729270899548173499043395

theorem tailTrace_1420250 : CollatzResearch.WordTrace tailWord_1420250 prefixEnd_1420250 729270899548173499043395 := by
  unfold tailWord_1420250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12950193276171071058492551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34533848736456189489313469 12950193276171071058492551)
  ·
    refine ⟨19425289914256606587738827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12950193276171071058492551 19425289914256606587738827)
    ·
      refine ⟨29137934871384909881608241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19425289914256606587738827 29137934871384909881608241)
      ·
        refine ⟨21853451153538682411206181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29137934871384909881608241 21853451153538682411206181)
        ·
          refine ⟨4097522091288502952101159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21853451153538682411206181 4097522091288502952101159)
          ·
            refine ⟨6146283136932754428151739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097522091288502952101159 6146283136932754428151739)
            ·
              refine ⟨9219424705399131642227609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146283136932754428151739 9219424705399131642227609)
              ·
                refine ⟨6914568529049348731670707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9219424705399131642227609 6914568529049348731670707)
                ·
                  refine ⟨10371852793574023097506061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6914568529049348731670707 10371852793574023097506061)
                  ·
                    refine ⟨3889444797590258661564773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10371852793574023097506061 3889444797590258661564773)
                    ·
                      refine ⟨729270899548173499043395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3889444797590258661564773 729270899548173499043395)
                      ·
                        rfl

theorem cell23_1420250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1420250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420250 prefixEnd_1420250 := by exact prefixLift 1420250
  have htrace : WordTrace (prefixWord ++ tailWord_1420250) baseStart_1420250 baseEnd_1420250 := by
    simpa [prefixWord, tailWord_1420250, baseEnd_1420250] using wordTrace_append hprefix tailTrace_1420250
  have hstable : (prefixWord ++ tailWord_1420250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420250).length < 2 ^ (prefixWord ++ tailWord_1420250).sum := by decide
  have hdescent : baseEnd_1420250 < baseStart_1420250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420260 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_1420260 : Nat := 118140960795 + 1420260 * 2 ^ 59
def prefixEnd_1420260 : Nat := 4983230072969 + 3 ^ 40 * 1420260 * 2
def baseEnd_1420260 : Nat := 243092011451572819972783

theorem tailTrace_1420260 : CollatzResearch.WordTrace tailWord_1420260 prefixEnd_1420260 243092011451572819972783 := by
  unfold tailWord_1420260
  simp only [CollatzResearch.WordTrace]
  refine ⟨25900568917324027970917117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34534091889765370627889489 25900568917324027970917117)
  ·
    refine ⟨9712713343996510489093919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25900568917324027970917117 9712713343996510489093919)
    ·
      refine ⟨14569070015994765733640879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9712713343996510489093919 14569070015994765733640879)
      ·
        refine ⟨21853605023992148600461319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14569070015994765733640879 21853605023992148600461319)
        ·
          refine ⟨32780407535988222900691979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21853605023992148600461319 32780407535988222900691979)
          ·
            refine ⟨49170611303982334351037969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32780407535988222900691979 49170611303982334351037969)
            ·
              refine ⟨36877958477986750763278477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49170611303982334351037969 36877958477986750763278477)
              ·
                refine ⟨13829234429245031536229429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36877958477986750763278477 13829234429245031536229429)
                ·
                  refine ⟨1296490727741721706521509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13829234429245031536229429 1296490727741721706521509)
                  ·
                    refine ⟨243092011451572819972783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1296490727741721706521509 243092011451572819972783)
                    ·
                      rfl

theorem cell23_1420260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_1420260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420260 prefixEnd_1420260 := by exact prefixLift 1420260
  have htrace : WordTrace (prefixWord ++ tailWord_1420260) baseStart_1420260 baseEnd_1420260 := by
    simpa [prefixWord, tailWord_1420260, baseEnd_1420260] using wordTrace_append hprefix tailTrace_1420260
  have hstable : (prefixWord ++ tailWord_1420260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420260).length < 2 ^ (prefixWord ++ tailWord_1420260).sum := by decide
  have hdescent : baseEnd_1420260 < baseStart_1420260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420344 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 2, 3, 2]
def baseStart_1420344 : Nat := 118140960795 + 1420344 * 2 ^ 59
def prefixEnd_1420344 : Nat := 4983230072969 + 3 ^ 40 * 1420344 * 2
def baseEnd_1420344 : Nat := 729319166729696131267963

theorem tailTrace_1420344 : CollatzResearch.WordTrace tailWord_1420344 prefixEnd_1420344 729319166729696131267963 := by
  unfold tailWord_1420344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25902100783171869143946043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34536134377562492191928057 25902100783171869143946043)
  ·
    refine ⟨38853151174757803715919065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25902100783171869143946043 38853151174757803715919065)
    ·
      refine ⟨29139863381068352786939299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38853151174757803715919065 29139863381068352786939299)
      ·
        refine ⟨43709795071602529180408949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29139863381068352786939299 43709795071602529180408949)
        ·
          refine ⟨4097793287962737110663339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43709795071602529180408949 4097793287962737110663339)
          ·
            refine ⟨6146689931944105665995009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097793287962737110663339 6146689931944105665995009)
            ·
              refine ⟨4610017448958079249496257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6146689931944105665995009 4610017448958079249496257)
              ·
                refine ⟨3457513086718559437122193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610017448958079249496257 3457513086718559437122193)
                ·
                  refine ⟨2593134815038919577841645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457513086718559437122193 2593134815038919577841645)
                  ·
                    refine ⟨972425555639594841690617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593134815038919577841645 972425555639594841690617)
                    ·
                      refine ⟨729319166729696131267963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972425555639594841690617 729319166729696131267963)
                      ·
                        rfl

theorem cell23_1420344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_1420344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420344 prefixEnd_1420344 := by exact prefixLift 1420344
  have htrace : WordTrace (prefixWord ++ tailWord_1420344) baseStart_1420344 baseEnd_1420344 := by
    simpa [prefixWord, tailWord_1420344, baseEnd_1420344] using wordTrace_append hprefix tailTrace_1420344
  have hstable : (prefixWord ++ tailWord_1420344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420344).length < 2 ^ (prefixWord ++ tailWord_1420344).sum := by decide
  have hdescent : baseEnd_1420344 < baseStart_1420344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420360 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_1420360 : Nat := 118140960795 + 1420360 * 2 ^ 59
def prefixEnd_1420360 : Nat := 4983230072969 + 3 ^ 40 * 1420360 * 2
def baseEnd_1420360 : Nat := 729327382420168068667889

theorem tailTrace_1420360 : CollatzResearch.WordTrace tailWord_1420360 prefixEnd_1420360 729327382420168068667889 := by
  unfold tailWord_1420360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25902392567142886510237267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34536523422857182013649689 25902392567142886510237267)
  ·
    refine ⟨38853588850714329765355901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25902392567142886510237267 38853588850714329765355901)
    ·
      refine ⟨14570095819017873662008463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38853588850714329765355901 14570095819017873662008463)
      ·
        refine ⟨21855143728526810493012695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14570095819017873662008463 21855143728526810493012695)
        ·
          refine ⟨32782715592790215739519043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21855143728526810493012695 32782715592790215739519043)
          ·
            refine ⟨49174073389185323609278565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32782715592790215739519043 49174073389185323609278565)
            ·
              refine ⟨9220138760472248176739731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49174073389185323609278565 9220138760472248176739731)
              ·
                refine ⟨13830208140708372265109597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9220138760472248176739731 13830208140708372265109597)
                ·
                  refine ⟨5186328052765639599416099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13830208140708372265109597 5186328052765639599416099)
                  ·
                    refine ⟨7779492079148459399124149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5186328052765639599416099 7779492079148459399124149)
                    ·
                      refine ⟨729327382420168068667889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7779492079148459399124149 729327382420168068667889)
                      ·
                        rfl

theorem cell23_1420360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_1420360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420360 prefixEnd_1420360 := by exact prefixLift 1420360
  have htrace : WordTrace (prefixWord ++ tailWord_1420360) baseStart_1420360 baseEnd_1420360 := by
    simpa [prefixWord, tailWord_1420360, baseEnd_1420360] using wordTrace_append hprefix tailTrace_1420360
  have hstable : (prefixWord ++ tailWord_1420360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420360).length < 2 ^ (prefixWord ++ tailWord_1420360).sum := by decide
  have hdescent : baseEnd_1420360 < baseStart_1420360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420391 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_1420391 : Nat := 118140960795 + 1420391 * 2 ^ 59
def prefixEnd_1420391 : Nat := 4983230072969 + 3 ^ 40 * 1420391 * 2
def baseEnd_1420391 : Nat := 729343300320457447380247

theorem tailTrace_1420391 : CollatzResearch.WordTrace tailWord_1420391 prefixEnd_1420391 729343300320457447380247 := by
  unfold tailWord_1420391
  simp only [CollatzResearch.WordTrace]
  refine ⟨51805915797173465314853027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34537277198115643543235351 51805915797173465314853027)
  ·
    refine ⟨77708873695760197972279541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51805915797173465314853027 77708873695760197972279541)
    ·
      refine ⟨7285206908977518559901207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77708873695760197972279541 7285206908977518559901207)
      ·
        refine ⟨10927810363466277839851811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285206908977518559901207 10927810363466277839851811)
        ·
          refine ⟨16391715545199416759777717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10927810363466277839851811 16391715545199416759777717)
          ·
            refine ⟨1536723332362445321229161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16391715545199416759777717 1536723332362445321229161)
            ·
              refine ⟨1152542499271833990921871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536723332362445321229161 1152542499271833990921871)
              ·
                refine ⟨1728813748907750986382807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152542499271833990921871 1728813748907750986382807)
                ·
                  refine ⟨2593220623361626479574211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728813748907750986382807 2593220623361626479574211)
                  ·
                    refine ⟨3889830935042439719361317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2593220623361626479574211 3889830935042439719361317)
                    ·
                      refine ⟨729343300320457447380247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3889830935042439719361317 729343300320457447380247)
                      ·
                        rfl

theorem cell23_1420391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_1420391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420391 prefixEnd_1420391 := by exact prefixLift 1420391
  have htrace : WordTrace (prefixWord ++ tailWord_1420391) baseStart_1420391 baseEnd_1420391 := by
    simpa [prefixWord, tailWord_1420391, baseEnd_1420391] using wordTrace_append hprefix tailTrace_1420391
  have hstable : (prefixWord ++ tailWord_1420391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420391).length < 2 ^ (prefixWord ++ tailWord_1420391).sum := by decide
  have hdescent : baseEnd_1420391 < baseStart_1420391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420421 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 1, 2, 4]
def baseStart_1420421 : Nat := 118140960795 + 1420421 * 2 ^ 59
def prefixEnd_1420421 : Nat := 4983230072969 + 3 ^ 40 * 1420421 * 2
def baseEnd_1420421 : Nat := 729358704740092330005109

theorem tailTrace_1420421 : CollatzResearch.WordTrace tailWord_1420421 prefixEnd_1420421 729358704740092330005109 := by
  unfold tailWord_1420421
  simp only [CollatzResearch.WordTrace]
  refine ⟨51807009987064780438445117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34538006658043186958963411 51807009987064780438445117)
  ·
    refine ⟨19427628745149292664416919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51807009987064780438445117 19427628745149292664416919)
    ·
      refine ⟨29141443117723938996625379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19427628745149292664416919 29141443117723938996625379)
      ·
        refine ⟨43712164676585908494938069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29141443117723938996625379 43712164676585908494938069)
        ·
          refine ⟨1024503859607482230350111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43712164676585908494938069 1024503859607482230350111)
          ·
            refine ⟨1536755789411223345525167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024503859607482230350111 1536755789411223345525167)
            ·
              refine ⟨2305133684116835018287751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536755789411223345525167 2305133684116835018287751)
              ·
                refine ⟨3457700526175252527431627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305133684116835018287751 3457700526175252527431627)
                ·
                  refine ⟨5186550789262878791147441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457700526175252527431627 5186550789262878791147441)
                  ·
                    refine ⟨3889913091947159093360581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186550789262878791147441 3889913091947159093360581)
                    ·
                      refine ⟨729358704740092330005109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3889913091947159093360581 729358704740092330005109)
                      ·
                        rfl

theorem cell23_1420421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_1420421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420421 prefixEnd_1420421 := by exact prefixLift 1420421
  have htrace : WordTrace (prefixWord ++ tailWord_1420421) baseStart_1420421 baseEnd_1420421 := by
    simpa [prefixWord, tailWord_1420421, baseEnd_1420421] using wordTrace_append hprefix tailTrace_1420421
  have hstable : (prefixWord ++ tailWord_1420421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420421).length < 2 ^ (prefixWord ++ tailWord_1420421).sum := by decide
  have hdescent : baseEnd_1420421 < baseStart_1420421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420460 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1420460 : Nat := 118140960795 + 1420460 * 2 ^ 59
def prefixEnd_1420460 : Nat := 4983230072969 + 3 ^ 40 * 1420460 * 2
def baseEnd_1420460 : Nat := 729378730485617677417429

theorem tailTrace_1420460 : CollatzResearch.WordTrace tailWord_1420460 prefixEnd_1420460 729378730485617677417429 := by
  unfold tailWord_1420460
  simp only [CollatzResearch.WordTrace]
  refine ⟨25904216216961745049557417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34538954955948993399409889 25904216216961745049557417)
  ·
    refine ⟨19428162162721308787168063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25904216216961745049557417 19428162162721308787168063)
    ·
      refine ⟨29142243244081963180752095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19428162162721308787168063 29142243244081963180752095)
      ·
        refine ⟨43713364866122944771128143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29142243244081963180752095 43713364866122944771128143)
        ·
          refine ⟨65570047299184417156692215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43713364866122944771128143 65570047299184417156692215)
          ·
            refine ⟨98355070948776625735038323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65570047299184417156692215 98355070948776625735038323)
            ·
              refine ⟨147532606423164938602557485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98355070948776625735038323 147532606423164938602557485)
              ·
                refine ⟨55324727408686851975959057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147532606423164938602557485 55324727408686851975959057)
                ·
                  refine ⟨41493545556515138981969293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55324727408686851975959057 41493545556515138981969293)
                  ·
                    refine ⟨15560079583693177118238485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41493545556515138981969293 15560079583693177118238485)
                    ·
                      refine ⟨729378730485617677417429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15560079583693177118238485 729378730485617677417429)
                      ·
                        rfl

theorem cell23_1420460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1420460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420460 prefixEnd_1420460 := by exact prefixLift 1420460
  have htrace : WordTrace (prefixWord ++ tailWord_1420460) baseStart_1420460 baseEnd_1420460 := by
    simpa [prefixWord, tailWord_1420460, baseEnd_1420460] using wordTrace_append hprefix tailTrace_1420460
  have hstable : (prefixWord ++ tailWord_1420460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420460).length < 2 ^ (prefixWord ++ tailWord_1420460).sum := by decide
  have hdescent : baseEnd_1420460 < baseStart_1420460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420477 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1420477 : Nat := 118140960795 + 1420477 * 2 ^ 59
def prefixEnd_1420477 : Nat := 4983230072969 + 3 ^ 40 * 1420477 * 2
def baseEnd_1420477 : Nat := 729387459656744110904851

theorem tailTrace_1420477 : CollatzResearch.WordTrace tailWord_1420477 prefixEnd_1420477 729387459656744110904851 := by
  unfold tailWord_1420477
  simp only [CollatzResearch.WordTrace]
  refine ⟨51809052474861902002483685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34539368316574601334989123 51809052474861902002483685)
  ·
    refine ⟨9714197339036606625465691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51809052474861902002483685 9714197339036606625465691)
    ·
      refine ⟨14571296008554909938198537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9714197339036606625465691 14571296008554909938198537)
      ·
        refine ⟨10928472006416182453648903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14571296008554909938198537 10928472006416182453648903)
        ·
          refine ⟨16392708009624273680473355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10928472006416182453648903 16392708009624273680473355)
          ·
            refine ⟨24589062014436410520710033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16392708009624273680473355 24589062014436410520710033)
            ·
              refine ⟨18441796510827307890532525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24589062014436410520710033 18441796510827307890532525)
              ·
                refine ⟨6915673691560240458949697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18441796510827307890532525 6915673691560240458949697)
                ·
                  refine ⟨5186755268670180344212273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6915673691560240458949697 5186755268670180344212273)
                  ·
                    refine ⟨3890066451502635258159205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186755268670180344212273 3890066451502635258159205)
                    ·
                      refine ⟨729387459656744110904851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3890066451502635258159205 729387459656744110904851)
                      ·
                        rfl

theorem cell23_1420477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1420477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420477 prefixEnd_1420477 := by exact prefixLift 1420477
  have htrace : WordTrace (prefixWord ++ tailWord_1420477) baseStart_1420477 baseEnd_1420477 := by
    simpa [prefixWord, tailWord_1420477, baseEnd_1420477] using wordTrace_append hprefix tailTrace_1420477
  have hstable : (prefixWord ++ tailWord_1420477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420477).length < 2 ^ (prefixWord ++ tailWord_1420477).sum := by decide
  have hdescent : baseEnd_1420477 < baseStart_1420477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420497 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_1420497 : Nat := 118140960795 + 1420497 * 2 ^ 59
def prefixEnd_1420497 : Nat := 4983230072969 + 3 ^ 40 * 1420497 * 2
def baseEnd_1420497 : Nat := 729397729269834032654759

theorem tailTrace_1420497 : CollatzResearch.WordTrace tailWord_1420497 prefixEnd_1420497 729397729269834032654759 := by
  unfold tailWord_1420497
  simp only [CollatzResearch.WordTrace]
  refine ⟨51809781934789445418211745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34539854623192963612141163 51809781934789445418211745)
  ·
    refine ⟨38857336451092084063658809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51809781934789445418211745 38857336451092084063658809)
    ·
      refine ⟨29143002338319063047744107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38857336451092084063658809 29143002338319063047744107)
      ·
        refine ⟨43714503507478594571616161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29143002338319063047744107 43714503507478594571616161)
        ·
          refine ⟨32785877630608945928712121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43714503507478594571616161 32785877630608945928712121)
          ·
            refine ⟨24589408222956709446534091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32785877630608945928712121 24589408222956709446534091)
            ·
              refine ⟨36884112334435064169801137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24589408222956709446534091 36884112334435064169801137)
              ·
                refine ⟨27663084250826298127350853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36884112334435064169801137 27663084250826298127350853)
                ·
                  refine ⟨5186828297029930898878285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27663084250826298127350853 5186828297029930898878285)
                  ·
                    refine ⟨1945060611386224087079357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5186828297029930898878285 1945060611386224087079357)
                    ·
                      refine ⟨729397729269834032654759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945060611386224087079357 729397729269834032654759)
                      ·
                        rfl

theorem cell23_1420497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_1420497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420497 prefixEnd_1420497 := by exact prefixLift 1420497
  have htrace : WordTrace (prefixWord ++ tailWord_1420497) baseStart_1420497 baseEnd_1420497 := by
    simpa [prefixWord, tailWord_1420497, baseEnd_1420497] using wordTrace_append hprefix tailTrace_1420497
  have hstable : (prefixWord ++ tailWord_1420497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420497).length < 2 ^ (prefixWord ++ tailWord_1420497).sum := by decide
  have hdescent : baseEnd_1420497 < baseStart_1420497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420502 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1420502 : Nat := 118140960795 + 1420502 * 2 ^ 59
def prefixEnd_1420502 : Nat := 4983230072969 + 3 ^ 40 * 1420502 * 2
def baseEnd_1420502 : Nat := 729400296673106513092237

theorem tailTrace_1420502 : CollatzResearch.WordTrace tailWord_1420502 prefixEnd_1420502 729400296673106513092237 := by
  unfold tailWord_1420502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3238122768735708204508985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34539976199847554181429173 3238122768735708204508985)
  ·
    refine ⟨2428592076551781153381739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3238122768735708204508985 2428592076551781153381739)
    ·
      refine ⟨3642888114827671730072609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428592076551781153381739 3642888114827671730072609)
      ·
        refine ⟨2732166086120753797554457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3642888114827671730072609 2732166086120753797554457)
        ·
          refine ⟨2049124564590565348165843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732166086120753797554457 2049124564590565348165843)
          ·
            refine ⟨3073686846885848022248765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049124564590565348165843 3073686846885848022248765)
            ·
              refine ⟨1152632567582193008343287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3073686846885848022248765 1152632567582193008343287)
              ·
                refine ⟨1728948851373289512514931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152632567582193008343287 1728948851373289512514931)
                ·
                  refine ⟨2593423277059934268772397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728948851373289512514931 2593423277059934268772397)
                  ·
                    refine ⟨972533728897475350789649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593423277059934268772397 972533728897475350789649)
                    ·
                      refine ⟨729400296673106513092237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972533728897475350789649 729400296673106513092237)
                      ·
                        rfl

theorem cell23_1420502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1420502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420502 prefixEnd_1420502 := by exact prefixLift 1420502
  have htrace : WordTrace (prefixWord ++ tailWord_1420502) baseStart_1420502 baseEnd_1420502 := by
    simpa [prefixWord, tailWord_1420502, baseEnd_1420502] using wordTrace_append hprefix tailTrace_1420502
  have hstable : (prefixWord ++ tailWord_1420502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420502).length < 2 ^ (prefixWord ++ tailWord_1420502).sum := by decide
  have hdescent : baseEnd_1420502 < baseStart_1420502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420524 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 2, 5, 2]
def baseStart_1420524 : Nat := 118140960795 + 1420524 * 2 ^ 59
def prefixEnd_1420524 : Nat := 4983230072969 + 3 ^ 40 * 1420524 * 2
def baseEnd_1420524 : Nat := 729411593247505427017135

theorem tailTrace_1420524 : CollatzResearch.WordTrace tailWord_1420524 prefixEnd_1420524 729411593247505427017135 := by
  unfold tailWord_1420524
  simp only [CollatzResearch.WordTrace]
  refine ⟨25905383352845814514722313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34540511137127752686296417 25905383352845814514722313)
  ·
    refine ⟨19429037514634360886041735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25905383352845814514722313 19429037514634360886041735)
    ·
      refine ⟨29143556271951541329062603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19429037514634360886041735 29143556271951541329062603)
      ·
        refine ⟨43715334407927311993593905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29143556271951541329062603 43715334407927311993593905)
        ·
          refine ⟨32786500805945483995195429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43715334407927311993593905 32786500805945483995195429)
          ·
            refine ⟨6147468901114778249099143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32786500805945483995195429 6147468901114778249099143)
            ·
              refine ⟨9221203351672167373648715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147468901114778249099143 9221203351672167373648715)
              ·
                refine ⟨13831805027508251060473073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9221203351672167373648715 13831805027508251060473073)
                ·
                  refine ⟨10373853770631188295354805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13831805027508251060473073 10373853770631188295354805)
                  ·
                    refine ⟨972548790996673902689513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10373853770631188295354805 972548790996673902689513)
                    ·
                      refine ⟨729411593247505427017135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972548790996673902689513 729411593247505427017135)
                      ·
                        rfl

theorem cell23_1420524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_1420524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420524 prefixEnd_1420524 := by exact prefixLift 1420524
  have htrace : WordTrace (prefixWord ++ tailWord_1420524) baseStart_1420524 baseEnd_1420524 := by
    simpa [prefixWord, tailWord_1420524, baseEnd_1420524] using wordTrace_append hprefix tailTrace_1420524
  have hstable : (prefixWord ++ tailWord_1420524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420524).length < 2 ^ (prefixWord ++ tailWord_1420524).sum := by decide
  have hdescent : baseEnd_1420524 < baseStart_1420524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420532 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1420532 : Nat := 118140960795 + 1420532 * 2 ^ 59
def prefixEnd_1420532 : Nat := 4983230072969 + 3 ^ 40 * 1420532 * 2
def baseEnd_1420532 : Nat := 729415701092741395717099

theorem tailTrace_1420532 : CollatzResearch.WordTrace tailWord_1420532 prefixEnd_1420532 729415701092741395717099 := by
  unfold tailWord_1420532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25905529244831323197867925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34540705659775097597157233 25905529244831323197867925)
  ·
    refine ⟨1214321683351468274900059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25905529244831323197867925 1214321683351468274900059)
    ·
      refine ⟨1821482525027202412350089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214321683351468274900059 1821482525027202412350089)
      ·
        refine ⟨1366111893770401809262567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1821482525027202412350089 1366111893770401809262567)
        ·
          refine ⟨2049167840655602713893851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1366111893770401809262567 2049167840655602713893851)
          ·
            refine ⟨3073751760983404070840777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049167840655602713893851 3073751760983404070840777)
            ·
              refine ⟨2305313820737553053130583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073751760983404070840777 2305313820737553053130583)
              ·
                refine ⟨3457970731106329579695875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305313820737553053130583 3457970731106329579695875)
                ·
                  refine ⟨5186956096659494369543813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457970731106329579695875 5186956096659494369543813)
                  ·
                    refine ⟨972554268123655194289465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5186956096659494369543813 972554268123655194289465)
                    ·
                      refine ⟨729415701092741395717099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972554268123655194289465 729415701092741395717099)
                      ·
                        rfl

theorem cell23_1420532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1420532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420532 prefixEnd_1420532 := by exact prefixLift 1420532
  have htrace : WordTrace (prefixWord ++ tailWord_1420532) baseStart_1420532 baseEnd_1420532 := by
    simpa [prefixWord, tailWord_1420532, baseEnd_1420532] using wordTrace_append hprefix tailTrace_1420532
  have hstable : (prefixWord ++ tailWord_1420532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420532).length < 2 ^ (prefixWord ++ tailWord_1420532).sum := by decide
  have hdescent : baseEnd_1420532 < baseStart_1420532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420537 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1420537 : Nat := 118140960795 + 1420537 * 2 ^ 59
def prefixEnd_1420537 : Nat := 4983230072969 + 3 ^ 40 * 1420537 * 2
def baseEnd_1420537 : Nat := 729418268496013876154575

theorem tailTrace_1420537 : CollatzResearch.WordTrace tailWord_1420537 prefixEnd_1420537 729418268496013876154575 := by
  unfold tailWord_1420537
  simp only [CollatzResearch.WordTrace]
  refine ⟨51811240854644532249667865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34540827236429688166445243 51811240854644532249667865)
  ·
    refine ⟨38858430640983399187250899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51811240854644532249667865 38858430640983399187250899)
    ·
      refine ⟨58287645961475098780876349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38858430640983399187250899 58287645961475098780876349)
      ·
        refine ⟨21857867235553162042828631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58287645961475098780876349 21857867235553162042828631)
        ·
          refine ⟨32786800853329743064242947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21857867235553162042828631 32786800853329743064242947)
          ·
            refine ⟨49180201279994614596364421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32786800853329743064242947 49180201279994614596364421)
            ·
              refine ⟨9221287739998990236818329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49180201279994614596364421 9221287739998990236818329)
              ·
                refine ⟨6915965804999242677613747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9221287739998990236818329 6915965804999242677613747)
                ·
                  refine ⟨10373948707498864016420621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6915965804999242677613747 10373948707498864016420621)
                  ·
                    refine ⟨3890230765312074006157733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10373948707498864016420621 3890230765312074006157733)
                    ·
                      refine ⟨729418268496013876154575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3890230765312074006157733 729418268496013876154575)
                      ·
                        rfl

theorem cell23_1420537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1420537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420537 prefixEnd_1420537 := by exact prefixLift 1420537
  have htrace : WordTrace (prefixWord ++ tailWord_1420537) baseStart_1420537 baseEnd_1420537 := by
    simpa [prefixWord, tailWord_1420537, baseEnd_1420537] using wordTrace_append hprefix tailTrace_1420537
  have hstable : (prefixWord ++ tailWord_1420537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420537).length < 2 ^ (prefixWord ++ tailWord_1420537).sum := by decide
  have hdescent : baseEnd_1420537 < baseStart_1420537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420554 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_1420554 : Nat := 118140960795 + 1420554 * 2 ^ 59
def prefixEnd_1420554 : Nat := 4983230072969 + 3 ^ 40 * 1420554 * 2
def baseEnd_1420554 : Nat := 729426997667140309641997

theorem tailTrace_1420554 : CollatzResearch.WordTrace tailWord_1420554 prefixEnd_1420554 729426997667140309641997 := by
  unfold tailWord_1420554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952965223895736038259179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34541240597055296102024477 12952965223895736038259179)
  ·
    refine ⟨19429447835843604057388769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12952965223895736038259179 19429447835843604057388769)
    ·
      refine ⟨14572085876882703043041577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19429447835843604057388769 14572085876882703043041577)
      ·
        refine ⟨10929064407662027282281183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14572085876882703043041577 10929064407662027282281183)
        ·
          refine ⟨16393596611493040923421775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10929064407662027282281183 16393596611493040923421775)
          ·
            refine ⟨24590394917239561385132663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393596611493040923421775 24590394917239561385132663)
            ·
              refine ⟨36885592375859342077698995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24590394917239561385132663 36885592375859342077698995)
              ·
                refine ⟨55328388563789013116548493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36885592375859342077698995 55328388563789013116548493)
                ·
                  refine ⟨20748145711420879918705685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55328388563789013116548493 20748145711420879918705685)
                  ·
                    refine ⟨972569330222853746189329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20748145711420879918705685 972569330222853746189329)
                    ·
                      refine ⟨729426997667140309641997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972569330222853746189329 729426997667140309641997)
                      ·
                        rfl

theorem cell23_1420554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_1420554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420554 prefixEnd_1420554 := by exact prefixLift 1420554
  have htrace : WordTrace (prefixWord ++ tailWord_1420554) baseStart_1420554 baseEnd_1420554 := by
    simpa [prefixWord, tailWord_1420554, baseEnd_1420554] using wordTrace_append hprefix tailTrace_1420554
  have hstable : (prefixWord ++ tailWord_1420554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420554).length < 2 ^ (prefixWord ++ tailWord_1420554).sum := by decide
  have hdescent : baseEnd_1420554 < baseStart_1420554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420567 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1420567 : Nat := 118140960795 + 1420567 * 2 ^ 59
def prefixEnd_1420567 : Nat := 4983230072969 + 3 ^ 40 * 1420567 * 2
def baseEnd_1420567 : Nat := 729433672915648758779437

theorem tailTrace_1420567 : CollatzResearch.WordTrace tailWord_1420567 prefixEnd_1420567 729433672915648758779437 := by
  unfold tailWord_1420567
  simp only [CollatzResearch.WordTrace]
  refine ⟨51812335044535847373259955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34541556696357231582173303 51812335044535847373259955)
  ·
    refine ⟨77718502566803771059889933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51812335044535847373259955 77718502566803771059889933)
    ·
      refine ⟨29144438462551414147458725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77718502566803771059889933 29144438462551414147458725)
      ·
        refine ⟨5464582211728390152648511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29144438462551414147458725 5464582211728390152648511)
        ·
          refine ⟨8196873317592585228972767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464582211728390152648511 8196873317592585228972767)
          ·
            refine ⟨12295309976388877843459151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196873317592585228972767 12295309976388877843459151)
            ·
              refine ⟨18442964964583316765188727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12295309976388877843459151 18442964964583316765188727)
              ·
                refine ⟨27664447446874975147783091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18442964964583316765188727 27664447446874975147783091)
                ·
                  refine ⟨41496671170312462721674637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27664447446874975147783091 41496671170312462721674637)
                  ·
                    refine ⟨15561251688867173520627989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41496671170312462721674637 15561251688867173520627989)
                    ·
                      refine ⟨729433672915648758779437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15561251688867173520627989 729433672915648758779437)
                      ·
                        rfl

theorem cell23_1420567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1420567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420567 prefixEnd_1420567 := by exact prefixLift 1420567
  have htrace : WordTrace (prefixWord ++ tailWord_1420567) baseStart_1420567 baseEnd_1420567 := by
    simpa [prefixWord, tailWord_1420567, baseEnd_1420567] using wordTrace_append hprefix tailTrace_1420567
  have hstable : (prefixWord ++ tailWord_1420567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420567).length < 2 ^ (prefixWord ++ tailWord_1420567).sum := by decide
  have hdescent : baseEnd_1420567 < baseStart_1420567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420581 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_1420581 : Nat := 118140960795 + 1420581 * 2 ^ 59
def prefixEnd_1420581 : Nat := 4983230072969 + 3 ^ 40 * 1420581 * 2
def baseEnd_1420581 : Nat := 243146953881603901334791

theorem tailTrace_1420581 : CollatzResearch.WordTrace tailWord_1420581 prefixEnd_1420581 243146953881603901334791 := by
  unfold tailWord_1420581
  simp only [CollatzResearch.WordTrace]
  refine ⟨51812845666485127764269597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34541897110990085176179731 51812845666485127764269597)
  ·
    refine ⟨19429817124931922911601099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51812845666485127764269597 19429817124931922911601099)
    ·
      refine ⟨29144725687397884367401649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19429817124931922911601099 29144725687397884367401649)
      ·
        refine ⟨21858544265548413275551237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29144725687397884367401649 21858544265548413275551237)
        ·
          refine ⟨4098477049790327489165857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21858544265548413275551237 4098477049790327489165857)
          ·
            refine ⟨3073857787342745616874393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4098477049790327489165857 3073857787342745616874393)
            ·
              refine ⟨2305393340507059212655795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073857787342745616874393 2305393340507059212655795)
              ·
                refine ⟨3458090010760588818983693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305393340507059212655795 3458090010760588818983693)
                ·
                  refine ⟨1296783754035220807118885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3458090010760588818983693 1296783754035220807118885)
                  ·
                    refine ⟨243146953881603901334791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1296783754035220807118885 243146953881603901334791)
                    ·
                      rfl

theorem cell23_1420581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_1420581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420581 prefixEnd_1420581 := by exact prefixLift 1420581
  have htrace : WordTrace (prefixWord ++ tailWord_1420581) baseStart_1420581 baseEnd_1420581 := by
    simpa [prefixWord, tailWord_1420581, baseEnd_1420581] using wordTrace_append hprefix tailTrace_1420581
  have hstable : (prefixWord ++ tailWord_1420581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420581).length < 2 ^ (prefixWord ++ tailWord_1420581).sum := by decide
  have hdescent : baseEnd_1420581 < baseStart_1420581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420624 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 1, 5]
def baseStart_1420624 : Nat := 118140960795 + 1420624 * 2 ^ 59
def prefixEnd_1420624 : Nat := 4983230072969 + 3 ^ 40 * 1420624 * 2
def baseEnd_1420624 : Nat := 243154313770985011922225

theorem tailTrace_1420624 : CollatzResearch.WordTrace tailWord_1420624 prefixEnd_1420624 243154313770985011922225 := by
  unfold tailWord_1420624
  simp only [CollatzResearch.WordTrace]
  refine ⟨25907207002664673054042463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34542942670219564072056617 25907207002664673054042463)
  ·
    refine ⟨38860810503997009581063695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25907207002664673054042463 38860810503997009581063695)
    ·
      refine ⟨58291215755995514371595543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38860810503997009581063695 58291215755995514371595543)
      ·
        refine ⟨87436823633993271557393315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58291215755995514371595543 87436823633993271557393315)
        ·
          refine ⟨131155235450989907336089973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87436823633993271557393315 131155235450989907336089973)
          ·
            refine ⟨12295803323530303812758435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131155235450989907336089973 12295803323530303812758435)
            ·
              refine ⟨18443704985295455719137653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12295803323530303812758435 18443704985295455719137653)
              ·
                refine ⟨1729097342371448973669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18443704985295455719137653 1729097342371448973669155)
                ·
                  refine ⟨2593646013557173460503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729097342371448973669155 2593646013557173460503733)
                  ·
                    refine ⟨243154313770985011922225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2593646013557173460503733 243154313770985011922225)
                    ·
                      rfl

theorem cell23_1420624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_1420624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420624 prefixEnd_1420624 := by exact prefixLift 1420624
  have htrace : WordTrace (prefixWord ++ tailWord_1420624) baseStart_1420624 baseEnd_1420624 := by
    simpa [prefixWord, tailWord_1420624, baseEnd_1420624] using wordTrace_append hprefix tailTrace_1420624
  have hstable : (prefixWord ++ tailWord_1420624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420624).length < 2 ^ (prefixWord ++ tailWord_1420624).sum := by decide
  have hdescent : baseEnd_1420624 < baseStart_1420624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420631 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 4, 3, 2]
def baseStart_1420631 : Nat := 118140960795 + 1420631 * 2 ^ 59
def prefixEnd_1420631 : Nat := 4983230072969 + 3 ^ 40 * 1420631 * 2
def baseEnd_1420631 : Nat := 729466535677536508379143

theorem tailTrace_1420631 : CollatzResearch.WordTrace tailWord_1420631 prefixEnd_1420631 729466535677536508379143 := by
  unfold tailWord_1420631
  simp only [CollatzResearch.WordTrace]
  refine ⟨51814669316303986303589747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34543112877535990869059831 51814669316303986303589747)
  ·
    refine ⟨77722003974455979455384621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51814669316303986303589747 77722003974455979455384621)
    ·
      refine ⟨29145751490420992295769233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77722003974455979455384621 29145751490420992295769233)
      ·
        refine ⟨21859313617815744221826925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29145751490420992295769233 21859313617815744221826925)
        ·
          refine ⟨8197242606680904083185097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21859313617815744221826925 8197242606680904083185097)
          ·
            refine ⟨6147931955010678062388823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8197242606680904083185097 6147931955010678062388823)
            ·
              refine ⟨9221897932516017093583235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147931955010678062388823 9221897932516017093583235)
              ·
                refine ⟨13832846898774025640374853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9221897932516017093583235 13832846898774025640374853)
                ·
                  refine ⟨2593658793520129807570285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13832846898774025640374853 2593658793520129807570285)
                  ·
                    refine ⟨972622047570048677838857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593658793520129807570285 972622047570048677838857)
                    ·
                      refine ⟨729466535677536508379143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972622047570048677838857 729466535677536508379143)
                      ·
                        rfl

theorem cell23_1420631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_1420631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420631 prefixEnd_1420631 := by exact prefixLift 1420631
  have htrace : WordTrace (prefixWord ++ tailWord_1420631) baseStart_1420631 baseEnd_1420631 := by
    simpa [prefixWord, tailWord_1420631, baseEnd_1420631] using wordTrace_append hprefix tailTrace_1420631
  have hstable : (prefixWord ++ tailWord_1420631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420631).length < 2 ^ (prefixWord ++ tailWord_1420631).sum := by decide
  have hdescent : baseEnd_1420631 < baseStart_1420631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420667 : List Nat := [1, 1, 1, 1, 1, 6, 1, 11]
def baseStart_1420667 : Nat := 118140960795 + 1420667 * 2 ^ 59
def prefixEnd_1420667 : Nat := 4983230072969 + 3 ^ 40 * 1420667 * 2
def baseEnd_1420667 : Nat := 27017963740040680278851

theorem tailTrace_1420667 : CollatzResearch.WordTrace tailWord_1420667 prefixEnd_1420667 27017963740040680278851 := by
  unfold tailWord_1420667
  simp only [CollatzResearch.WordTrace]
  refine ⟨51815982344173564451900255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34543988229449042967933503 51815982344173564451900255)
  ·
    refine ⟨77723973516260346677850383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51815982344173564451900255 77723973516260346677850383)
    ·
      refine ⟨116585960274390520016775575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77723973516260346677850383 116585960274390520016775575)
      ·
        refine ⟨174878940411585780025163363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116585960274390520016775575 174878940411585780025163363)
        ·
          refine ⟨262318410617378670037745045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174878940411585780025163363 262318410617378670037745045)
          ·
            refine ⟨12296175497689625158019299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262318410617378670037745045 12296175497689625158019299)
            ·
              refine ⟨18444263246534437737028949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12296175497689625158019299 18444263246534437737028949)
              ·
                refine ⟨27017963740040680278851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18444263246534437737028949 27017963740040680278851)
                ·
                  rfl

theorem cell23_1420667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 11].length) (baseStart_1420667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420667 prefixEnd_1420667 := by exact prefixLift 1420667
  have htrace : WordTrace (prefixWord ++ tailWord_1420667) baseStart_1420667 baseEnd_1420667 := by
    simpa [prefixWord, tailWord_1420667, baseEnd_1420667] using wordTrace_append hprefix tailTrace_1420667
  have hstable : (prefixWord ++ tailWord_1420667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420667).length < 2 ^ (prefixWord ++ tailWord_1420667).sum := by decide
  have hdescent : baseEnd_1420667 < baseStart_1420667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420687 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_1420687 : Nat := 118140960795 + 1420687 * 2 ^ 59
def prefixEnd_1420687 : Nat := 4983230072969 + 3 ^ 40 * 1420687 * 2
def baseEnd_1420687 : Nat := 729495290594188289278885

theorem tailTrace_1420687 : CollatzResearch.WordTrace tailWord_1420687 prefixEnd_1420687 729495290594188289278885 := by
  unfold tailWord_1420687
  simp only [CollatzResearch.WordTrace]
  refine ⟨51816711804101107867628315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34544474536067405245085543 51816711804101107867628315)
  ·
    refine ⟨77725067706151661801442473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51816711804101107867628315 77725067706151661801442473)
    ·
      refine ⟨58293800779613746351081855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77725067706151661801442473 58293800779613746351081855)
      ·
        refine ⟨87440701169420619526622783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58293800779613746351081855 87440701169420619526622783)
        ·
          refine ⟨131161051754130929289934175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87440701169420619526622783 131161051754130929289934175)
          ·
            refine ⟨196741577631196393934901263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131161051754130929289934175 196741577631196393934901263)
            ·
              refine ⟨295112366446794590902351895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196741577631196393934901263 295112366446794590902351895)
              ·
                refine ⟨442668549670191886353527843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295112366446794590902351895 442668549670191886353527843)
                ·
                  refine ⟨664002824505287829530291765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442668549670191886353527843 664002824505287829530291765)
                  ·
                    refine ⟨62250264797370734018464853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 664002824505287829530291765 62250264797370734018464853)
                    ·
                      refine ⟨729495290594188289278885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 62250264797370734018464853 729495290594188289278885)
                      ·
                        rfl

theorem cell23_1420687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_1420687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420687 prefixEnd_1420687 := by exact prefixLift 1420687
  have htrace : WordTrace (prefixWord ++ tailWord_1420687) baseStart_1420687 baseEnd_1420687 := by
    simpa [prefixWord, tailWord_1420687, baseEnd_1420687] using wordTrace_append hprefix tailTrace_1420687
  have hstable : (prefixWord ++ tailWord_1420687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420687).length < 2 ^ (prefixWord ++ tailWord_1420687).sum := by decide
  have hdescent : baseEnd_1420687 < baseStart_1420687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420701 : List Nat := [1, 4, 2, 1, 3, 3, 1, 8]
def baseStart_1420701 : Nat := 118140960795 + 1420701 * 2 ^ 59
def prefixEnd_1420701 : Nat := 4983230072969 + 3 ^ 40 * 1420701 * 2
def baseEnd_1420701 : Nat := 27018610345309304981623

theorem tailTrace_1420701 : CollatzResearch.WordTrace tailWord_1420701 prefixEnd_1420701 27018610345309304981623 := by
  unfold tailWord_1420701
  simp only [CollatzResearch.WordTrace]
  refine ⟨51817222426050388258637957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34544814950700258839091971 51817222426050388258637957)
  ·
    refine ⟨9715729204884447798494617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51817222426050388258637957 9715729204884447798494617)
    ·
      refine ⟨7286796903663335848870963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9715729204884447798494617 7286796903663335848870963)
      ·
        refine ⟨10930195355495003773306445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7286796903663335848870963 10930195355495003773306445)
        ·
          refine ⟨4098823258310626414989917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10930195355495003773306445 4098823258310626414989917)
          ·
            refine ⟨1537058721866484905621219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4098823258310626414989917 1537058721866484905621219)
            ·
              refine ⟨2305588082799727358431829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537058721866484905621219 2305588082799727358431829)
              ·
                refine ⟨27018610345309304981623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2305588082799727358431829 27018610345309304981623)
                ·
                  rfl

theorem cell23_1420701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 8].length) (baseStart_1420701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420701 prefixEnd_1420701 := by exact prefixLift 1420701
  have htrace : WordTrace (prefixWord ++ tailWord_1420701) baseStart_1420701 baseEnd_1420701 := by
    simpa [prefixWord, tailWord_1420701, baseEnd_1420701] using wordTrace_append hprefix tailTrace_1420701
  have hstable : (prefixWord ++ tailWord_1420701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420701).length < 2 ^ (prefixWord ++ tailWord_1420701).sum := by decide
  have hdescent : baseEnd_1420701 < baseStart_1420701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420712 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1420712 : Nat := 118140960795 + 1420712 * 2 ^ 59
def prefixEnd_1420712 : Nat := 4983230072969 + 3 ^ 40 * 1420712 * 2
def baseEnd_1420712 : Nat := 729508127610550691466271

theorem tailTrace_1420712 : CollatzResearch.WordTrace tailWord_1420712 prefixEnd_1420712 729508127610550691466271 := by
  unfold tailWord_1420712
  simp only [CollatzResearch.WordTrace]
  refine ⟨25908811814505268568644195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34545082419340358091525593 25908811814505268568644195)
  ·
    refine ⟨38863217721757902852966293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25908811814505268568644195 38863217721757902852966293)
    ·
      refine ⟨1821713330707401696232795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38863217721757902852966293 1821713330707401696232795)
      ·
        refine ⟨2732569996061102544349193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821713330707401696232795 2732569996061102544349193)
        ·
          refine ⟨2049427497045826908261895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732569996061102544349193 2049427497045826908261895)
          ·
            refine ⟨3074141245568740362392843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049427497045826908261895 3074141245568740362392843)
            ·
              refine ⟨4611211868353110543589265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3074141245568740362392843 4611211868353110543589265)
              ·
                refine ⟨3458408901264832907691949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4611211868353110543589265 3458408901264832907691949)
                ·
                  refine ⟨1296903337974312340384481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3458408901264832907691949 1296903337974312340384481)
                  ·
                    refine ⟨972677503480734255288361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1296903337974312340384481 972677503480734255288361)
                    ·
                      refine ⟨729508127610550691466271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972677503480734255288361 729508127610550691466271)
                      ·
                        rfl

theorem cell23_1420712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1420712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420712 prefixEnd_1420712 := by exact prefixLift 1420712
  have htrace : WordTrace (prefixWord ++ tailWord_1420712) baseStart_1420712 baseEnd_1420712 := by
    simpa [prefixWord, tailWord_1420712, baseEnd_1420712] using wordTrace_append hprefix tailTrace_1420712
  have hstable : (prefixWord ++ tailWord_1420712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420712).length < 2 ^ (prefixWord ++ tailWord_1420712).sum := by decide
  have hdescent : baseEnd_1420712 < baseStart_1420712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420732 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1420732 : Nat := 118140960795 + 1420732 * 2 ^ 59
def prefixEnd_1420732 : Nat := 4983230072969 + 3 ^ 40 * 1420732 * 2
def baseEnd_1420732 : Nat := 729518397223640613216179

theorem tailTrace_1420732 : CollatzResearch.WordTrace tailWord_1420732 prefixEnd_1420732 729518397223640613216179 := by
  unfold tailWord_1420732
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909176544469040276508225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34545568725958720368677633 25909176544469040276508225)
  ·
    refine ⟨19431882408351780207381169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25909176544469040276508225 19431882408351780207381169)
    ·
      refine ⟨14573911806263835155535877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19431882408351780207381169 14573911806263835155535877)
      ·
        refine ⟨2732608463674469091662977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14573911806263835155535877 2732608463674469091662977)
        ·
          refine ⟨2049456347755851818747233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732608463674469091662977 2049456347755851818747233)
          ·
            refine ⟨1537092260816888864060425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2049456347755851818747233 1537092260816888864060425)
            ·
              refine ⟨1152819195612666648045319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537092260816888864060425 1152819195612666648045319)
              ·
                refine ⟨1729228793418999972067979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152819195612666648045319 1729228793418999972067979)
                ·
                  refine ⟨2593843190128499958101969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729228793418999972067979 2593843190128499958101969)
                  ·
                    refine ⟨1945382392596374968576477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2593843190128499958101969 1945382392596374968576477)
                    ·
                      refine ⟨729518397223640613216179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945382392596374968576477 729518397223640613216179)
                      ·
                        rfl

theorem cell23_1420732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1420732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420732 prefixEnd_1420732 := by exact prefixLift 1420732
  have htrace : WordTrace (prefixWord ++ tailWord_1420732) baseStart_1420732 baseEnd_1420732 := by
    simpa [prefixWord, tailWord_1420732, baseEnd_1420732] using wordTrace_append hprefix tailTrace_1420732
  have hstable : (prefixWord ++ tailWord_1420732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420732).length < 2 ^ (prefixWord ++ tailWord_1420732).sum := by decide
  have hdescent : baseEnd_1420732 < baseStart_1420732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420744 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1420744 : Nat := 118140960795 + 1420744 * 2 ^ 59
def prefixEnd_1420744 : Nat := 4983230072969 + 3 ^ 40 * 1420744 * 2
def baseEnd_1420744 : Nat := 243174852997164855422041

theorem tailTrace_1420744 : CollatzResearch.WordTrace tailWord_1420744 prefixEnd_1420744 243174852997164855422041 := by
  unfold tailWord_1420744
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909395382447303301226643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34545860509929737734968857 25909395382447303301226643)
  ·
    refine ⟨38864093073670954951839965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25909395382447303301226643 38864093073670954951839965)
    ·
      refine ⟨14574034902626608106939987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38864093073670954951839965 14574034902626608106939987)
      ·
        refine ⟨21861052353939912160409981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14574034902626608106939987 21861052353939912160409981)
        ·
          refine ⟨8197894632727467060153743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21861052353939912160409981 8197894632727467060153743)
          ·
            refine ⟨12296841949091200590230615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8197894632727467060153743 12296841949091200590230615)
            ·
              refine ⟨18445262923636800885345923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12296841949091200590230615 18445262923636800885345923)
              ·
                refine ⟨27667894385455201328018885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18445262923636800885345923 27667894385455201328018885)
                ·
                  refine ⟨5187730197272850249003541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27667894385455201328018885 5187730197272850249003541)
                  ·
                    refine ⟨243174852997164855422041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5187730197272850249003541 243174852997164855422041)
                    ·
                      rfl

theorem cell23_1420744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1420744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420744 prefixEnd_1420744 := by exact prefixLift 1420744
  have htrace : WordTrace (prefixWord ++ tailWord_1420744) baseStart_1420744 baseEnd_1420744 := by
    simpa [prefixWord, tailWord_1420744, baseEnd_1420744] using wordTrace_append hprefix tailTrace_1420744
  have hstable : (prefixWord ++ tailWord_1420744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420744).length < 2 ^ (prefixWord ++ tailWord_1420744).sum := by decide
  have hdescent : baseEnd_1420744 < baseStart_1420744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420751 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 3, 4, 2]
def baseStart_1420751 : Nat := 118140960795 + 1420751 * 2 ^ 59
def prefixEnd_1420751 : Nat := 4983230072969 + 3 ^ 40 * 1420751 * 2
def baseEnd_1420751 : Nat := 729528153356076038878591

theorem tailTrace_1420751 : CollatzResearch.WordTrace tailWord_1420751 prefixEnd_1420751 729528153356076038878591 := by
  unfold tailWord_1420751
  simp only [CollatzResearch.WordTrace]
  refine ⟨51819046075869246797958107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34546030717246164531972071 51819046075869246797958107)
  ·
    refine ⟨77728569113803870196937161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51819046075869246797958107 77728569113803870196937161)
    ·
      refine ⟨58296426835352902647702871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77728569113803870196937161 58296426835352902647702871)
      ·
        refine ⟨87444640253029353971554307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58296426835352902647702871 87444640253029353971554307)
        ·
          refine ⟨131166960379544030957331461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87444640253029353971554307 131166960379544030957331461)
          ·
            refine ⟨24593805071164505804499649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131166960379544030957331461 24593805071164505804499649)
            ·
              refine ⟨18445353803373379353374737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24593805071164505804499649 18445353803373379353374737)
              ·
                refine ⟨13834015352530034515031053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18445353803373379353374737 13834015352530034515031053)
                ·
                  refine ⟨5187755757198762943136645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13834015352530034515031053 5187755757198762943136645)
                  ·
                    refine ⟨972704204474768051838121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187755757198762943136645 972704204474768051838121)
                    ·
                      refine ⟨729528153356076038878591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972704204474768051838121 729528153356076038878591)
                      ·
                        rfl

theorem cell23_1420751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4, 2].length) (baseStart_1420751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420751 prefixEnd_1420751 := by exact prefixLift 1420751
  have htrace : WordTrace (prefixWord ++ tailWord_1420751) baseStart_1420751 baseEnd_1420751 := by
    simpa [prefixWord, tailWord_1420751, baseEnd_1420751] using wordTrace_append hprefix tailTrace_1420751
  have hstable : (prefixWord ++ tailWord_1420751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420751).length < 2 ^ (prefixWord ++ tailWord_1420751).sum := by decide
  have hdescent : baseEnd_1420751 < baseStart_1420751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420791 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 5]
def baseStart_1420791 : Nat := 118140960795 + 1420791 * 2 ^ 59
def prefixEnd_1420791 : Nat := 4983230072969 + 3 ^ 40 * 1420791 * 2
def baseEnd_1420791 : Nat := 81060965842472875819823

theorem tailTrace_1420791 : CollatzResearch.WordTrace tailWord_1420791 prefixEnd_1420791 81060965842472875819823 := by
  unfold tailWord_1420791
  simp only [CollatzResearch.WordTrace]
  refine ⟨51820504995724333629414227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34547003330482889086276151 51820504995724333629414227)
  ·
    refine ⟨77730757493586500444121341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51820504995724333629414227 77730757493586500444121341)
    ·
      refine ⟨29149034060094937666545503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77730757493586500444121341 29149034060094937666545503)
      ·
        refine ⟨43723551090142406499818255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29149034060094937666545503 43723551090142406499818255)
        ·
          refine ⟨65585326635213609749727383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43723551090142406499818255 65585326635213609749727383)
          ·
            refine ⟨98377989952820414624591075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65585326635213609749727383 98377989952820414624591075)
            ·
              refine ⟨147566984929230621936886613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98377989952820414624591075 147566984929230621936886613)
              ·
                refine ⟨864650302319710675411445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 147566984929230621936886613 864650302319710675411445)
                ·
                  refine ⟨81060965842472875819823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 864650302319710675411445 81060965842472875819823)
                  ·
                    rfl

theorem cell23_1420791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 5].length) (baseStart_1420791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420791 prefixEnd_1420791 := by exact prefixLift 1420791
  have htrace : WordTrace (prefixWord ++ tailWord_1420791) baseStart_1420791 baseEnd_1420791 := by
    simpa [prefixWord, tailWord_1420791, baseEnd_1420791] using wordTrace_append hprefix tailTrace_1420791
  have hstable : (prefixWord ++ tailWord_1420791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420791).length < 2 ^ (prefixWord ++ tailWord_1420791).sum := by decide
  have hdescent : baseEnd_1420791 < baseStart_1420791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420802 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1420802 : Nat := 118140960795 + 1420802 * 2 ^ 59
def prefixEnd_1420802 : Nat := 4983230072969 + 3 ^ 40 * 1420802 * 2
def baseEnd_1420802 : Nat := 729554340869455339340857

theorem tailTrace_1420802 : CollatzResearch.WordTrace tailWord_1420802 prefixEnd_1420802 729554340869455339340857 := by
  unfold tailWord_1420802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12955226549671120627016165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34547270799122988338709773 12955226549671120627016165)
  ·
    refine ⟨2429104978063335117565531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12955226549671120627016165 2429104978063335117565531)
    ·
      refine ⟨3643657467095002676348297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2429104978063335117565531 3643657467095002676348297)
      ·
        refine ⟨2732743100321252007261223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3643657467095002676348297 2732743100321252007261223)
        ·
          refine ⟨4099114650481878010891835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732743100321252007261223 4099114650481878010891835)
          ·
            refine ⟨6148671975722817016337753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099114650481878010891835 6148671975722817016337753)
            ·
              refine ⟨4611503981792112762253315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6148671975722817016337753 4611503981792112762253315)
              ·
                refine ⟨6917255972688169143379973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4611503981792112762253315 6917255972688169143379973)
                ·
                  refine ⟨1296985494879031714383745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6917255972688169143379973 1296985494879031714383745)
                  ·
                    refine ⟨972739121159273785787809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1296985494879031714383745 972739121159273785787809)
                    ·
                      refine ⟨729554340869455339340857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972739121159273785787809 729554340869455339340857)
                      ·
                        rfl

theorem cell23_1420802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1420802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420802 prefixEnd_1420802 := by exact prefixLift 1420802
  have htrace : WordTrace (prefixWord ++ tailWord_1420802) baseStart_1420802 baseEnd_1420802 := by
    simpa [prefixWord, tailWord_1420802, baseEnd_1420802] using wordTrace_append hprefix tailTrace_1420802
  have hstable : (prefixWord ++ tailWord_1420802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420802).length < 2 ^ (prefixWord ++ tailWord_1420802).sum := by decide
  have hdescent : baseEnd_1420802 < baseStart_1420802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420813 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1420813 : Nat := 118140960795 + 1420813 * 2 ^ 59
def prefixEnd_1420813 : Nat := 4983230072969 + 3 ^ 40 * 1420813 * 2
def baseEnd_1420813 : Nat := 729559989156654796303307

theorem tailTrace_1420813 : CollatzResearch.WordTrace tailWord_1420813 prefixEnd_1420813 729559989156654796303307 := by
  unfold tailWord_1420813
  simp only [CollatzResearch.WordTrace]
  refine ⟨51821307401644631386715093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34547538267763087591143395 51821307401644631386715093)
  ·
    refine ⟨1214561892226046048126135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51821307401644631386715093 1214561892226046048126135)
    ·
      refine ⟨1821842838339069072189203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214561892226046048126135 1821842838339069072189203)
      ·
        refine ⟨2732764257508603608283805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821842838339069072189203 2732764257508603608283805)
        ·
          refine ⟨1024786596565726353106427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2732764257508603608283805 1024786596565726353106427)
          ·
            refine ⟨1537179894848589529659641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024786596565726353106427 1537179894848589529659641)
            ·
              refine ⟨1152884921136442147244731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537179894848589529659641 1152884921136442147244731)
              ·
                refine ⟨1729327381704663220867097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152884921136442147244731 1729327381704663220867097)
                ·
                  refine ⟨1296995536278497415650323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1729327381704663220867097 1296995536278497415650323)
                  ·
                    refine ⟨1945493304417746123475485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1296995536278497415650323 1945493304417746123475485)
                    ·
                      refine ⟨729559989156654796303307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945493304417746123475485 729559989156654796303307)
                      ·
                        rfl

theorem cell23_1420813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1420813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420813 prefixEnd_1420813 := by exact prefixLift 1420813
  have htrace : WordTrace (prefixWord ++ tailWord_1420813) baseStart_1420813 baseEnd_1420813 := by
    simpa [prefixWord, tailWord_1420813, baseEnd_1420813] using wordTrace_append hprefix tailTrace_1420813
  have hstable : (prefixWord ++ tailWord_1420813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420813).length < 2 ^ (prefixWord ++ tailWord_1420813).sum := by decide
  have hdescent : baseEnd_1420813 < baseStart_1420813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420844 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1420844 : Nat := 118140960795 + 1420844 * 2 ^ 59
def prefixEnd_1420844 : Nat := 4983230072969 + 3 ^ 40 * 1420844 * 2
def baseEnd_1420844 : Nat := 729575907056944175015663

theorem tailTrace_1420844 : CollatzResearch.WordTrace tailWord_1420844 prefixEnd_1420844 729575907056944175015663 := by
  unfold tailWord_1420844
  simp only [CollatzResearch.WordTrace]
  refine ⟨25911219032266161840546793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34548292043021549120729057 25911219032266161840546793)
  ·
    refine ⟨19433414274199621380410095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25911219032266161840546793 19433414274199621380410095)
    ·
      refine ⟨29150121411299432070615143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19433414274199621380410095 29150121411299432070615143)
      ·
        refine ⟨43725182116949148105922715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29150121411299432070615143 43725182116949148105922715)
        ·
          refine ⟨65587773175423722158884073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43725182116949148105922715 65587773175423722158884073)
          ·
            refine ⟨49190829881567791619163055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65587773175423722158884073 49190829881567791619163055)
            ·
              refine ⟨73786244822351687428744583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49190829881567791619163055 73786244822351687428744583)
              ·
                refine ⟨110679367233527531143116875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73786244822351687428744583 110679367233527531143116875)
                ·
                  refine ⟨166019050850291296714675313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110679367233527531143116875 166019050850291296714675313)
                  ·
                    refine ⟨124514288137718472536006485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166019050850291296714675313 124514288137718472536006485)
                    ·
                      refine ⟨729575907056944175015663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 124514288137718472536006485 729575907056944175015663)
                      ·
                        rfl

theorem cell23_1420844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1420844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420844 prefixEnd_1420844 := by exact prefixLift 1420844
  have htrace : WordTrace (prefixWord ++ tailWord_1420844) baseStart_1420844 baseEnd_1420844 := by
    simpa [prefixWord, tailWord_1420844, baseEnd_1420844] using wordTrace_append hprefix tailTrace_1420844
  have hstable : (prefixWord ++ tailWord_1420844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420844).length < 2 ^ (prefixWord ++ tailWord_1420844).sum := by decide
  have hdescent : baseEnd_1420844 < baseStart_1420844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420858 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2]
def baseStart_1420858 : Nat := 118140960795 + 1420858 * 2 ^ 59
def prefixEnd_1420858 : Nat := 4983230072969 + 3 ^ 40 * 1420858 * 2
def baseEnd_1420858 : Nat := 729583095786107120240599

theorem tailTrace_1420858 : CollatzResearch.WordTrace tailWord_1420858 prefixEnd_1420858 729583095786107120240599 := by
  unfold tailWord_1420858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12955737171620401018025807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34548632457654402714735485 12955737171620401018025807)
  ·
    refine ⟨19433605757430601527038711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12955737171620401018025807 19433605757430601527038711)
    ·
      refine ⟨29150408636145902290558067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19433605757430601527038711 29150408636145902290558067)
      ·
        refine ⟨43725612954218853435837101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29150408636145902290558067 43725612954218853435837101)
        ·
          refine ⟨16397104857832070038438913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43725612954218853435837101 16397104857832070038438913)
          ·
            refine ⟨12297828643374052528829185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16397104857832070038438913 12297828643374052528829185)
            ·
              refine ⟨9223371482530539396621889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12297828643374052528829185 9223371482530539396621889)
              ·
                refine ⟨6917528611897904547466417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9223371482530539396621889 6917528611897904547466417)
                ·
                  refine ⟨5188146458923428410599813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6917528611897904547466417 5188146458923428410599813)
                  ·
                    refine ⟨972777461048142826987465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188146458923428410599813 972777461048142826987465)
                    ·
                      refine ⟨729583095786107120240599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972777461048142826987465 729583095786107120240599)
                      ·
                        rfl

theorem cell23_1420858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_1420858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420858 prefixEnd_1420858 := by exact prefixLift 1420858
  have htrace : WordTrace (prefixWord ++ tailWord_1420858) baseStart_1420858 baseEnd_1420858 := by
    simpa [prefixWord, tailWord_1420858, baseEnd_1420858] using wordTrace_append hprefix tailTrace_1420858
  have hstable : (prefixWord ++ tailWord_1420858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420858).length < 2 ^ (prefixWord ++ tailWord_1420858).sum := by decide
  have hdescent : baseEnd_1420858 < baseStart_1420858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420881 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 6]
def baseStart_1420881 : Nat := 118140960795 + 1420881 * 2 ^ 59
def prefixEnd_1420881 : Nat := 4983230072969 + 3 ^ 40 * 1420881 * 2
def baseEnd_1420881 : Nat := 81066100649017836694777

theorem tailTrace_1420881 : CollatzResearch.WordTrace tailWord_1420881 prefixEnd_1420881 81066100649017836694777 := by
  unfold tailWord_1420881
  simp only [CollatzResearch.WordTrace]
  refine ⟨51823787565398279000190497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34549191710265519333460331 51823787565398279000190497)
  ·
    refine ⟨38867840674048709250142873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51823787565398279000190497 38867840674048709250142873)
    ·
      refine ⟨29150880505536531937607155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38867840674048709250142873 29150880505536531937607155)
      ·
        refine ⟨43726320758304797906410733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29150880505536531937607155 43726320758304797906410733)
        ·
          refine ⟨16397370284364299214904025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43726320758304797906410733 16397370284364299214904025)
          ·
            refine ⟨12298027713273224411178019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16397370284364299214904025 12298027713273224411178019)
            ·
              refine ⟨18447041569909836616767029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12298027713273224411178019 18447041569909836616767029)
              ·
                refine ⟨1729410147179047182821909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18447041569909836616767029 1729410147179047182821909)
                ·
                  refine ⟨81066100649017836694777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1729410147179047182821909 81066100649017836694777)
                  ·
                    rfl

theorem cell23_1420881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 6].length) (baseStart_1420881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420881 prefixEnd_1420881 := by exact prefixLift 1420881
  have htrace : WordTrace (prefixWord ++ tailWord_1420881) baseStart_1420881 baseEnd_1420881 := by
    simpa [prefixWord, tailWord_1420881, baseEnd_1420881] using wordTrace_append hprefix tailTrace_1420881
  have hstable : (prefixWord ++ tailWord_1420881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420881).length < 2 ^ (prefixWord ++ tailWord_1420881).sum := by decide
  have hdescent : baseEnd_1420881 < baseStart_1420881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420908 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_1420908 : Nat := 118140960795 + 1420908 * 2 ^ 59
def prefixEnd_1420908 : Nat := 4983230072969 + 3 ^ 40 * 1420908 * 2
def baseEnd_1420908 : Nat := 729608769818831924615369

theorem tailTrace_1420908 : CollatzResearch.WordTrace tailWord_1420908 prefixEnd_1420908 729608769818831924615369 := by
  unfold tailWord_1420908
  simp only [CollatzResearch.WordTrace]
  refine ⟨25912386168150231305711689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34549848224200308407615585 25912386168150231305711689)
  ·
    refine ⟨19434289626112673479283767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25912386168150231305711689 19434289626112673479283767)
    ·
      refine ⟨29151434439169010218925651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19434289626112673479283767 29151434439169010218925651)
      ·
        refine ⟨43727151658753515328388477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29151434439169010218925651 43727151658753515328388477)
        ·
          refine ⟨16397681872032568248145679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43727151658753515328388477 16397681872032568248145679)
          ·
            refine ⟨24596522808048852372218519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16397681872032568248145679 24596522808048852372218519)
            ·
              refine ⟨36894784212073278558327779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24596522808048852372218519 36894784212073278558327779)
              ·
                refine ⟨55342176318109917837491669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36894784212073278558327779 55342176318109917837491669)
                ·
                  refine ⟨1297082257455701199316211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 55342176318109917837491669 1297082257455701199316211)
                  ·
                    refine ⟨1945623386183551798974317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297082257455701199316211 1945623386183551798974317)
                    ·
                      refine ⟨729608769818831924615369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945623386183551798974317 729608769818831924615369)
                      ·
                        rfl

theorem cell23_1420908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_1420908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420908 prefixEnd_1420908 := by exact prefixLift 1420908
  have htrace : WordTrace (prefixWord ++ tailWord_1420908) baseStart_1420908 baseEnd_1420908 := by
    simpa [prefixWord, tailWord_1420908, baseEnd_1420908] using wordTrace_append hprefix tailTrace_1420908
  have hstable : (prefixWord ++ tailWord_1420908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420908).length < 2 ^ (prefixWord ++ tailWord_1420908).sum := by decide
  have hdescent : baseEnd_1420908 < baseStart_1420908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420918 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1420918 : Nat := 118140960795 + 1420918 * 2 ^ 59
def prefixEnd_1420918 : Nat := 4983230072969 + 3 ^ 40 * 1420918 * 2
def baseEnd_1420918 : Nat := 729613904625376885490323

theorem tailTrace_1420918 : CollatzResearch.WordTrace tailWord_1420918 prefixEnd_1420918 729613904625376885490323 := by
  unfold tailWord_1420918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239071066641514644955463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34550091377509489546191605 3239071066641514644955463)
  ·
    refine ⟨4858606599962271967433195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3239071066641514644955463 4858606599962271967433195)
    ·
      refine ⟨7287909899943407951149793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4858606599962271967433195 7287909899943407951149793)
      ·
        refine ⟨5465932424957555963362345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7287909899943407951149793 5465932424957555963362345)
        ·
          refine ⟨4099449318718166972521759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5465932424957555963362345 4099449318718166972521759)
          ·
            refine ⟨6149173978077250458782639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099449318718166972521759 6149173978077250458782639)
            ·
              refine ⟨9223760967115875688173959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149173978077250458782639 9223760967115875688173959)
              ·
                refine ⟨13835641450673813532260939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9223760967115875688173959 13835641450673813532260939)
                ·
                  refine ⟨20753462176010720298391409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13835641450673813532260939 20753462176010720298391409)
                  ·
                    refine ⟨15565096632008040223793557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20753462176010720298391409 15565096632008040223793557)
                    ·
                      refine ⟨729613904625376885490323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15565096632008040223793557 729613904625376885490323)
                      ·
                        rfl

theorem cell23_1420918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1420918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420918 prefixEnd_1420918 := by exact prefixLift 1420918
  have htrace : WordTrace (prefixWord ++ tailWord_1420918) baseStart_1420918 baseEnd_1420918 := by
    simpa [prefixWord, tailWord_1420918, baseEnd_1420918] using wordTrace_append hprefix tailTrace_1420918
  have hstable : (prefixWord ++ tailWord_1420918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420918).length < 2 ^ (prefixWord ++ tailWord_1420918).sum := by decide
  have hdescent : baseEnd_1420918 < baseStart_1420918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420925 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_1420925 : Nat := 118140960795 + 1420925 * 2 ^ 59
def prefixEnd_1420925 : Nat := 4983230072969 + 3 ^ 40 * 1420925 * 2
def baseEnd_1420925 : Nat := 729617498989958358102791

theorem tailTrace_1420925 : CollatzResearch.WordTrace tailWord_1420925 prefixEnd_1420925 729617498989958358102791 := by
  unfold tailWord_1420925
  simp only [CollatzResearch.WordTrace]
  refine ⟨51825392377238874514792229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34550261584825916343194819 51825392377238874514792229)
  ·
    refine ⟨9717261070732288971523543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51825392377238874514792229 9717261070732288971523543)
    ·
      refine ⟨14575891606098433457285315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717261070732288971523543 14575891606098433457285315)
      ·
        refine ⟨21863837409147650185927973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14575891606098433457285315 21863837409147650185927973)
        ·
          refine ⟨4099469514215184409861495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21863837409147650185927973 4099469514215184409861495)
          ·
            refine ⟨6149204271322776614792243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099469514215184409861495 6149204271322776614792243)
            ·
              refine ⟨9223806406984164922188365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149204271322776614792243 9223806406984164922188365)
              ·
                refine ⟨3458927402619061845820637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9223806406984164922188365 3458927402619061845820637)
                ·
                  refine ⟨1297097775982148192182739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3458927402619061845820637 1297097775982148192182739)
                  ·
                    refine ⟨1945646663973222288274109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297097775982148192182739 1945646663973222288274109)
                    ·
                      refine ⟨729617498989958358102791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945646663973222288274109 729617498989958358102791)
                      ·
                        rfl

theorem cell23_1420925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_1420925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420925 prefixEnd_1420925 := by exact prefixLift 1420925
  have htrace : WordTrace (prefixWord ++ tailWord_1420925) baseStart_1420925 baseEnd_1420925 := by
    simpa [prefixWord, tailWord_1420925, baseEnd_1420925] using wordTrace_append hprefix tailTrace_1420925
  have hstable : (prefixWord ++ tailWord_1420925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420925).length < 2 ^ (prefixWord ++ tailWord_1420925).sum := by decide
  have hdescent : baseEnd_1420925 < baseStart_1420925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420965 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 5, 2, 2]
def baseStart_1420965 : Nat := 118140960795 + 1420965 * 2 ^ 59
def prefixEnd_1420965 : Nat := 4983230072969 + 3 ^ 40 * 1420965 * 2
def baseEnd_1420965 : Nat := 729638038216138201602607

theorem tailTrace_1420965 : CollatzResearch.WordTrace tailWord_1420965 prefixEnd_1420965 729638038216138201602607 := by
  unfold tailWord_1420965
  simp only [CollatzResearch.WordTrace]
  refine ⟨51826851297093961346248349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34551234198062640897498899 51826851297093961346248349)
  ·
    refine ⟨19435069236410235504843131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51826851297093961346248349 19435069236410235504843131)
    ·
      refine ⟨29152603854615353257264697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19435069236410235504843131 29152603854615353257264697)
      ·
        refine ⟨21864452890961514942948523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29152603854615353257264697 21864452890961514942948523)
        ·
          refine ⟨32796679336442272414422785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21864452890961514942948523 32796679336442272414422785)
          ·
            refine ⟨24597509502331704310817089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32796679336442272414422785 24597509502331704310817089)
            ·
              refine ⟨18448132126748778233112817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24597509502331704310817089 18448132126748778233112817)
              ·
                refine ⟨13836099095061583674834613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18448132126748778233112817 13836099095061583674834613)
                ·
                  refine ⟨1297134290162023469515745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13836099095061583674834613 1297134290162023469515745)
                  ·
                    refine ⟨972850717621517602136809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297134290162023469515745 972850717621517602136809)
                    ·
                      refine ⟨729638038216138201602607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972850717621517602136809 729638038216138201602607)
                      ·
                        rfl

theorem cell23_1420965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_1420965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420965 prefixEnd_1420965 := by exact prefixLift 1420965
  have htrace : WordTrace (prefixWord ++ tailWord_1420965) baseStart_1420965 baseEnd_1420965 := by
    simpa [prefixWord, tailWord_1420965, baseEnd_1420965] using wordTrace_append hprefix tailTrace_1420965
  have hstable : (prefixWord ++ tailWord_1420965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420965).length < 2 ^ (prefixWord ++ tailWord_1420965).sum := by decide
  have hdescent : baseEnd_1420965 < baseStart_1420965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420988 : List Nat := [2, 2, 2, 3, 1, 3, 2, 8]
def baseStart_1420988 : Nat := 118140960795 + 1420988 * 2 ^ 59
def prefixEnd_1420988 : Nat := 4983230072969 + 3 ^ 40 * 1420988 * 2
def baseEnd_1420988 : Nat := 27024068454488578207963

theorem tailTrace_1420988 : CollatzResearch.WordTrace tailWord_1420988 prefixEnd_1420988 27024068454488578207963 := by
  unfold tailWord_1420988
  simp only [CollatzResearch.WordTrace]
  refine ⟨25913845088005318137167809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34551793450673757516223745 25913845088005318137167809)
  ·
    refine ⟨19435383816003988602875857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25913845088005318137167809 19435383816003988602875857)
    ·
      refine ⟨14576537862002991452156893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19435383816003988602875857 14576537862002991452156893)
      ·
        refine ⟨5466201698251121794558835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14576537862002991452156893 5466201698251121794558835)
        ·
          refine ⟨8199302547376682691838253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5466201698251121794558835 8199302547376682691838253)
          ·
            refine ⟨3074738455266256009439345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8199302547376682691838253 3074738455266256009439345)
            ·
              refine ⟨2306053841449692007079509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074738455266256009439345 2306053841449692007079509)
              ·
                refine ⟨27024068454488578207963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2306053841449692007079509 27024068454488578207963)
                ·
                  rfl

theorem cell23_1420988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 8].length) (baseStart_1420988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420988 prefixEnd_1420988 := by exact prefixLift 1420988
  have htrace : WordTrace (prefixWord ++ tailWord_1420988) baseStart_1420988 baseEnd_1420988 := by
    simpa [prefixWord, tailWord_1420988, baseEnd_1420988] using wordTrace_append hprefix tailTrace_1420988
  have hstable : (prefixWord ++ tailWord_1420988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420988).length < 2 ^ (prefixWord ++ tailWord_1420988).sum := by decide
  have hdescent : baseEnd_1420988 < baseStart_1420988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420991 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1420991 : Nat := 118140960795 + 1420991 * 2 ^ 59
def prefixEnd_1420991 : Nat := 4983230072969 + 3 ^ 40 * 1420991 * 2
def baseEnd_1420991 : Nat := 729651388713155099877487

theorem tailTrace_1420991 : CollatzResearch.WordTrace tailWord_1420991 prefixEnd_1420991 729651388713155099877487 := by
  unfold tailWord_1420991
  simp only [CollatzResearch.WordTrace]
  refine ⟨51827799594999767786694827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34551866396666511857796551 51827799594999767786694827)
  ·
    refine ⟨77741699392499651680042241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51827799594999767786694827 77741699392499651680042241)
    ·
      refine ⟨58306274544374738760031681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77741699392499651680042241 58306274544374738760031681)
      ·
        refine ⟨43729705908281054070023761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58306274544374738760031681 43729705908281054070023761)
        ·
          refine ⟨32797279431210790552517821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43729705908281054070023761 32797279431210790552517821)
          ·
            refine ⟨12298979786704046457194183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32797279431210790552517821 12298979786704046457194183)
            ·
              refine ⟨18448469680056069685791275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12298979786704046457194183 18448469680056069685791275)
              ·
                refine ⟨27672704520084104528686913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18448469680056069685791275 27672704520084104528686913)
                ·
                  refine ⟨20754528390063078396515185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27672704520084104528686913 20754528390063078396515185)
                  ·
                    refine ⟨15565896292547308797386389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20754528390063078396515185 15565896292547308797386389)
                    ·
                      refine ⟨729651388713155099877487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15565896292547308797386389 729651388713155099877487)
                      ·
                        rfl

theorem cell23_1420991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1420991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1420991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1420991 prefixEnd_1420991 := by exact prefixLift 1420991
  have htrace : WordTrace (prefixWord ++ tailWord_1420991) baseStart_1420991 baseEnd_1420991 := by
    simpa [prefixWord, tailWord_1420991, baseEnd_1420991] using wordTrace_append hprefix tailTrace_1420991
  have hstable : (prefixWord ++ tailWord_1420991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420991).length < 2 ^ (prefixWord ++ tailWord_1420991).sum := by decide
  have hdescent : baseEnd_1420991 < baseStart_1420991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421005 : List Nat := [1, 6, 2, 1, 1, 1, 2, 9]
def baseStart_1421005 : Nat := 118140960795 + 1421005 * 2 ^ 59
def prefixEnd_1421005 : Nat := 4983230072969 + 3 ^ 40 * 1421005 * 2
def baseEnd_1421005 : Nat := 27024391757122890559349

theorem tailTrace_1421005 : CollatzResearch.WordTrace tailWord_1421005 prefixEnd_1421005 27024391757122890559349 := by
  unfold tailWord_1421005
  simp only [CollatzResearch.WordTrace]
  refine ⟨51828310216949048177704469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34552206811299365451802979 51828310216949048177704469)
  ·
    refine ⟨2429452041419486633329897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51828310216949048177704469 2429452041419486633329897)
    ·
      refine ⟨1822089031064614974997423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2429452041419486633329897 1822089031064614974997423)
      ·
        refine ⟨2733133546596922462496135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822089031064614974997423 2733133546596922462496135)
        ·
          refine ⟨4099700319895383693744203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733133546596922462496135 4099700319895383693744203)
          ·
            refine ⟨6149550479843075540616305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099700319895383693744203 6149550479843075540616305)
            ·
              refine ⟨4612162859882306655462229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149550479843075540616305 4612162859882306655462229)
              ·
                refine ⟨27024391757122890559349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4612162859882306655462229 27024391757122890559349)
                ·
                  rfl

theorem cell23_1421005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 9].length) (baseStart_1421005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421005 prefixEnd_1421005 := by exact prefixLift 1421005
  have htrace : WordTrace (prefixWord ++ tailWord_1421005) baseStart_1421005 baseEnd_1421005 := by
    simpa [prefixWord, tailWord_1421005, baseEnd_1421005] using wordTrace_append hprefix tailTrace_1421005
  have hstable : (prefixWord ++ tailWord_1421005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421005).length < 2 ^ (prefixWord ++ tailWord_1421005).sum := by decide
  have hdescent : baseEnd_1421005 < baseStart_1421005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421011 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_1421011 : Nat := 118140960795 + 1421011 * 2 ^ 59
def prefixEnd_1421011 : Nat := 4983230072969 + 3 ^ 40 * 1421011 * 2
def baseEnd_1421011 : Nat := 729661658326245021627395

theorem tailTrace_1421011 : CollatzResearch.WordTrace tailWord_1421011 prefixEnd_1421011 729661658326245021627395 := by
  unfold tailWord_1421011
  simp only [CollatzResearch.WordTrace]
  refine ⟨51828529054927311202422887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34552352703284874134948591 51828529054927311202422887)
  ·
    refine ⟨77742793582390966803634331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51828529054927311202422887 77742793582390966803634331)
    ·
      refine ⟨116614190373586450205451497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77742793582390966803634331 116614190373586450205451497)
      ·
        refine ⟨87460642780189837654088623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116614190373586450205451497 87460642780189837654088623)
        ·
          refine ⟨131190964170284756481132935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87460642780189837654088623 131190964170284756481132935)
          ·
            refine ⟨196786446255427134721699403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131190964170284756481132935 196786446255427134721699403)
            ·
              refine ⟨295179669383140702082549105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196786446255427134721699403 295179669383140702082549105)
              ·
                refine ⟨221384752037355526561911829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295179669383140702082549105 221384752037355526561911829)
                ·
                  refine ⟨10377410251751040307589617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 221384752037355526561911829 10377410251751040307589617)
                  ·
                    refine ⟨7783057688813280230692213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10377410251751040307589617 7783057688813280230692213)
                    ·
                      refine ⟨729661658326245021627395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7783057688813280230692213 729661658326245021627395)
                      ·
                        rfl

theorem cell23_1421011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_1421011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421011 prefixEnd_1421011 := by exact prefixLift 1421011
  have htrace : WordTrace (prefixWord ++ tailWord_1421011) baseStart_1421011 baseEnd_1421011 := by
    simpa [prefixWord, tailWord_1421011, baseEnd_1421011] using wordTrace_append hprefix tailTrace_1421011
  have hstable : (prefixWord ++ tailWord_1421011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421011).length < 2 ^ (prefixWord ++ tailWord_1421011).sum := by decide
  have hdescent : baseEnd_1421011 < baseStart_1421011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421032 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1421032 : Nat := 118140960795 + 1421032 * 2 ^ 59
def prefixEnd_1421032 : Nat := 4983230072969 + 3 ^ 40 * 1421032 * 2
def baseEnd_1421032 : Nat := 729672441419989439464799

theorem tailTrace_1421032 : CollatzResearch.WordTrace tailWord_1421032 prefixEnd_1421032 729672441419989439464799 := by
  unfold tailWord_1421032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25914647493925615894468675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34552863325234154525958233 25914647493925615894468675)
  ·
    refine ⟨38871971240888423841703013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25914647493925615894468675 38871971240888423841703013)
    ·
      refine ⟨7288494607666579470319315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38871971240888423841703013 7288494607666579470319315)
      ·
        refine ⟨10932741911499869205478973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7288494607666579470319315 10932741911499869205478973)
        ·
          refine ⟨4099778216812450952054615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10932741911499869205478973 4099778216812450952054615)
          ·
            refine ⟨6149667325218676428081923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099778216812450952054615 6149667325218676428081923)
            ·
              refine ⟨9224500987828014642122885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149667325218676428081923 9224500987828014642122885)
              ·
                refine ⟨1729593935217752745398041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9224500987828014642122885 1729593935217752745398041)
                ·
                  refine ⟨1297195451413314559048531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1729593935217752745398041 1297195451413314559048531)
                  ·
                    refine ⟨1945793177119971838572797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297195451413314559048531 1945793177119971838572797)
                    ·
                      refine ⟨729672441419989439464799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945793177119971838572797 729672441419989439464799)
                      ·
                        rfl

theorem cell23_1421032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1421032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421032 prefixEnd_1421032 := by exact prefixLift 1421032
  have htrace : WordTrace (prefixWord ++ tailWord_1421032) baseStart_1421032 baseEnd_1421032 := by
    simpa [prefixWord, tailWord_1421032, baseEnd_1421032] using wordTrace_append hprefix tailTrace_1421032
  have hstable : (prefixWord ++ tailWord_1421032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421032).length < 2 ^ (prefixWord ++ tailWord_1421032).sum := by decide
  have hdescent : baseEnd_1421032 < baseStart_1421032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421038 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1421038 : Nat := 118140960795 + 1421038 * 2 ^ 59
def prefixEnd_1421038 : Nat := 4983230072969 + 3 ^ 40 * 1421038 * 2
def baseEnd_1421038 : Nat := 729675522303916415989771

theorem tailTrace_1421038 : CollatzResearch.WordTrace tailWord_1421038 prefixEnd_1421038 729675522303916415989771 := by
  unfold tailWord_1421038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478689228228686851706971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34553009217219663209103845 6478689228228686851706971)
  ·
    refine ⟨9718033842343030277560457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6478689228228686851706971 9718033842343030277560457)
    ·
      refine ⟨7288525381757272708170343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9718033842343030277560457 7288525381757272708170343)
      ·
        refine ⟨10932788072635909062255515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7288525381757272708170343 10932788072635909062255515)
        ·
          refine ⟨16399182108953863593383273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10932788072635909062255515 16399182108953863593383273)
          ·
            refine ⟨12299386581715397695037455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16399182108953863593383273 12299386581715397695037455)
            ·
              refine ⟨18449079872573096542556183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12299386581715397695037455 18449079872573096542556183)
              ·
                refine ⟨27673619808859644813834275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18449079872573096542556183 27673619808859644813834275)
                ·
                  refine ⟨41510429713289467220751413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27673619808859644813834275 41510429713289467220751413)
                  ·
                    refine ⟨3891602785620887551945445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41510429713289467220751413 3891602785620887551945445)
                    ·
                      refine ⟨729675522303916415989771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3891602785620887551945445 729675522303916415989771)
                      ·
                        rfl

theorem cell23_1421038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1421038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421038 prefixEnd_1421038 := by exact prefixLift 1421038
  have htrace : WordTrace (prefixWord ++ tailWord_1421038) baseStart_1421038 baseEnd_1421038 := by
    simpa [prefixWord, tailWord_1421038, baseEnd_1421038] using wordTrace_append hprefix tailTrace_1421038
  have hstable : (prefixWord ++ tailWord_1421038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421038).length < 2 ^ (prefixWord ++ tailWord_1421038).sum := by decide
  have hdescent : baseEnd_1421038 < baseStart_1421038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421055 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 1, 4, 2]
def baseStart_1421055 : Nat := 118140960795 + 1421055 * 2 ^ 59
def prefixEnd_1421055 : Nat := 4983230072969 + 3 ^ 40 * 1421055 * 2
def baseEnd_1421055 : Nat := 729684251475042849477193

theorem tailTrace_1421055 : CollatzResearch.WordTrace tailWord_1421055 prefixEnd_1421055 729684251475042849477193 := by
  unfold tailWord_1421055
  simp only [CollatzResearch.WordTrace]
  refine ⟨51830133866767906717024619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34553422577845271144683079 51830133866767906717024619)
  ·
    refine ⟨77745200800151860075536929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51830133866767906717024619 77745200800151860075536929)
    ·
      refine ⟨58308900600113895056652697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77745200800151860075536929 58308900600113895056652697)
      ·
        refine ⟨43731675450085421292489523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58308900600113895056652697 43731675450085421292489523)
        ·
          refine ⟨65597513175128131938734285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43731675450085421292489523 65597513175128131938734285)
          ·
            refine ⟨24599067440673049477025357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65597513175128131938734285 24599067440673049477025357)
            ·
              refine ⟨9224650290252393553884509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24599067440673049477025357 9224650290252393553884509)
              ·
                refine ⟨3459243858844647582706691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9224650290252393553884509 3459243858844647582706691)
                ·
                  refine ⟨5188865788266971374060037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459243858844647582706691 5188865788266971374060037)
                  ·
                    refine ⟨972912335300057132636257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188865788266971374060037 972912335300057132636257)
                    ·
                      refine ⟨729684251475042849477193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972912335300057132636257 729684251475042849477193)
                      ·
                        rfl

theorem cell23_1421055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_1421055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421055 prefixEnd_1421055 := by exact prefixLift 1421055
  have htrace : WordTrace (prefixWord ++ tailWord_1421055) baseStart_1421055 baseEnd_1421055 := by
    simpa [prefixWord, tailWord_1421055, baseEnd_1421055] using wordTrace_append hprefix tailTrace_1421055
  have hstable : (prefixWord ++ tailWord_1421055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421055).length < 2 ^ (prefixWord ++ tailWord_1421055).sum := by decide
  have hdescent : baseEnd_1421055 < baseStart_1421055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421089 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_1421089 : Nat := 118140960795 + 1421089 * 2 ^ 59
def prefixEnd_1421089 : Nat := 4983230072969 + 3 ^ 40 * 1421089 * 2
def baseEnd_1421089 : Nat := 729701709817295716452037

theorem tailTrace_1421089 : CollatzResearch.WordTrace tailWord_1421089 prefixEnd_1421089 729701709817295716452037 := by
  unfold tailWord_1421089
  simp only [CollatzResearch.WordTrace]
  refine ⟨51831373948644730523762321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34554249299096487015841547 51831373948644730523762321)
  ·
    refine ⟨38873530461483547892821741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51831373948644730523762321 38873530461483547892821741)
    ·
      refine ⟨14577573923056330459808153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38873530461483547892821741 14577573923056330459808153)
      ·
        refine ⟨10933180442292247844856115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14577573923056330459808153 10933180442292247844856115)
        ·
          refine ⟨16399770663438371767284173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10933180442292247844856115 16399770663438371767284173)
          ·
            refine ⟨6149913998789389412731565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16399770663438371767284173 6149913998789389412731565)
            ·
              refine ⟨2306217749546021029774337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6149913998789389412731565 2306217749546021029774337)
              ·
                refine ⟨1729663312159515772330753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306217749546021029774337 1729663312159515772330753)
                ·
                  refine ⟨1297247484119636829248065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1729663312159515772330753 1297247484119636829248065)
                  ·
                    refine ⟨972935613089727621936049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297247484119636829248065 972935613089727621936049)
                    ·
                      refine ⟨729701709817295716452037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972935613089727621936049 729701709817295716452037)
                      ·
                        rfl

theorem cell23_1421089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_1421089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421089 prefixEnd_1421089 := by exact prefixLift 1421089
  have htrace : WordTrace (prefixWord ++ tailWord_1421089) baseStart_1421089 baseEnd_1421089 := by
    simpa [prefixWord, tailWord_1421089, baseEnd_1421089] using wordTrace_append hprefix tailTrace_1421089
  have hstable : (prefixWord ++ tailWord_1421089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421089).length < 2 ^ (prefixWord ++ tailWord_1421089).sum := by decide
  have hdescent : baseEnd_1421089 < baseStart_1421089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421105 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1421105 : Nat := 118140960795 + 1421105 * 2 ^ 59
def prefixEnd_1421105 : Nat := 4983230072969 + 3 ^ 40 * 1421105 * 2
def baseEnd_1421105 : Nat := 729709925507767653851963

theorem tailTrace_1421105 : CollatzResearch.WordTrace tailWord_1421105 prefixEnd_1421105 729709925507767653851963 := by
  unfold tailWord_1421105
  simp only [CollatzResearch.WordTrace]
  refine ⟨51831957516586765256344769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34554638344391176837563179 51831957516586765256344769)
  ·
    refine ⟨38873968137440073942258577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51831957516586765256344769 38873968137440073942258577)
    ·
      refine ⟨29155476103080055456693933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38873968137440073942258577 29155476103080055456693933)
      ·
        refine ⟨10933303538655020796260225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29155476103080055456693933 10933303538655020796260225)
        ·
          refine ⟨8199977653991265597195169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10933303538655020796260225 8199977653991265597195169)
          ·
            refine ⟨6149983240493449197896377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8199977653991265597195169 6149983240493449197896377)
            ·
              refine ⟨4612487430370086898422283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149983240493449197896377 4612487430370086898422283)
              ·
                refine ⟨6918731145555130347633425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612487430370086898422283 6918731145555130347633425)
                ·
                  refine ⟨5189048359166347760725069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6918731145555130347633425 5189048359166347760725069)
                  ·
                    refine ⟨1945893134687380410271901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5189048359166347760725069 1945893134687380410271901)
                    ·
                      refine ⟨729709925507767653851963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945893134687380410271901 729709925507767653851963)
                      ·
                        rfl

theorem cell23_1421105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1421105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421105 prefixEnd_1421105 := by exact prefixLift 1421105
  have htrace : WordTrace (prefixWord ++ tailWord_1421105) baseStart_1421105 baseEnd_1421105 := by
    simpa [prefixWord, tailWord_1421105, baseEnd_1421105] using wordTrace_append hprefix tailTrace_1421105
  have hstable : (prefixWord ++ tailWord_1421105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421105).length < 2 ^ (prefixWord ++ tailWord_1421105).sum := by decide
  have hdescent : baseEnd_1421105 < baseStart_1421105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421106 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_1421106 : Nat := 118140960795 + 1421106 * 2 ^ 59
def prefixEnd_1421106 : Nat := 4983230072969 + 3 ^ 40 * 1421106 * 2
def baseEnd_1421106 : Nat := 729710438988422149939459

theorem tailTrace_1421106 : CollatzResearch.WordTrace tailWord_1421106 prefixEnd_1421106 729710438988422149939459 := by
  unfold tailWord_1421106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957998497395785606782793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34554662659722094951420781 12957998497395785606782793)
  ·
    refine ⟨9718498873046839205087095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12957998497395785606782793 9718498873046839205087095)
    ·
      refine ⟨14577748309570258807630643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9718498873046839205087095 14577748309570258807630643)
      ·
        refine ⟨21866622464355388211445965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14577748309570258807630643 21866622464355388211445965)
        ·
          refine ⟨8199983424133270579292237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21866622464355388211445965 8199983424133270579292237)
          ·
            refine ⟨3074993784049976467234589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8199983424133270579292237 3074993784049976467234589)
            ·
              refine ⟨1153122669018741175212971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3074993784049976467234589 1153122669018741175212971)
              ·
                refine ⟨1729684003528111762819457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153122669018741175212971 1729684003528111762819457)
                ·
                  refine ⟨1297263002646083822114593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1729684003528111762819457 1297263002646083822114593)
                  ·
                    refine ⟨972947251984562866585945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297263002646083822114593 972947251984562866585945)
                    ·
                      refine ⟨729710438988422149939459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972947251984562866585945 729710438988422149939459)
                      ·
                        rfl

theorem cell23_1421106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_1421106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421106 prefixEnd_1421106 := by exact prefixLift 1421106
  have htrace : WordTrace (prefixWord ++ tailWord_1421106) baseStart_1421106 baseEnd_1421106 := by
    simpa [prefixWord, tailWord_1421106, baseEnd_1421106] using wordTrace_append hprefix tailTrace_1421106
  have hstable : (prefixWord ++ tailWord_1421106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421106).length < 2 ^ (prefixWord ++ tailWord_1421106).sum := by decide
  have hdescent : baseEnd_1421106 < baseStart_1421106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421145 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1421145 : Nat := 118140960795 + 1421145 * 2 ^ 59
def prefixEnd_1421145 : Nat := 4983230072969 + 3 ^ 40 * 1421145 * 2
def baseEnd_1421145 : Nat := 729730464733947497351779

theorem tailTrace_1421145 : CollatzResearch.WordTrace tailWord_1421145 prefixEnd_1421145 729730464733947497351779 := by
  unfold tailWord_1421145
  simp only [CollatzResearch.WordTrace]
  refine ⟨51833416436441852087800889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34555610957627901391867259 51833416436441852087800889)
  ·
    refine ⟨38875062327331389065850667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51833416436441852087800889 38875062327331389065850667)
    ·
      refine ⟨58312593490997083598776001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38875062327331389065850667 58312593490997083598776001)
      ·
        refine ⟨43734445118247812699082001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58312593490997083598776001 43734445118247812699082001)
        ·
          refine ⟨32800833838685859524311501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43734445118247812699082001 32800833838685859524311501)
          ·
            refine ⟨12300312689507197321616813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32800833838685859524311501 12300312689507197321616813)
            ·
              refine ⟨4612617258565198995606305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12300312689507197321616813 4612617258565198995606305)
              ·
                refine ⟨3459462943923899246704729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612617258565198995606305 3459462943923899246704729)
                ·
                  refine ⟨2594597207942924435028547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459462943923899246704729 2594597207942924435028547)
                  ·
                    refine ⟨3891895811914386652542821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2594597207942924435028547 3891895811914386652542821)
                    ·
                      refine ⟨729730464733947497351779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3891895811914386652542821 729730464733947497351779)
                      ·
                        rfl

theorem cell23_1421145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1421145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421145 prefixEnd_1421145 := by exact prefixLift 1421145
  have htrace : WordTrace (prefixWord ++ tailWord_1421145) baseStart_1421145 baseEnd_1421145 := by
    simpa [prefixWord, tailWord_1421145, baseEnd_1421145] using wordTrace_append hprefix tailTrace_1421145
  have hstable : (prefixWord ++ tailWord_1421145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421145).length < 2 ^ (prefixWord ++ tailWord_1421145).sum := by decide
  have hdescent : baseEnd_1421145 < baseStart_1421145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421165 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1421165 : Nat := 118140960795 + 1421165 * 2 ^ 59
def prefixEnd_1421165 : Nat := 4983230072969 + 3 ^ 40 * 1421165 * 2
def baseEnd_1421165 : Nat := 729740734347037419101687

theorem tailTrace_1421165 : CollatzResearch.WordTrace tailWord_1421165 prefixEnd_1421165 729740734347037419101687 := by
  unfold tailWord_1421165
  simp only [CollatzResearch.WordTrace]
  refine ⟨51834145896369395503528949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34556097264246263669019299 51834145896369395503528949)
  ·
    refine ⟨4859451177784630828455839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51834145896369395503528949 4859451177784630828455839)
    ·
      refine ⟨7289176766676946242683759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859451177784630828455839 7289176766676946242683759)
      ·
        refine ⟨10933765150015419364025639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289176766676946242683759 10933765150015419364025639)
        ·
          refine ⟨16400647725023129046038459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10933765150015419364025639 16400647725023129046038459)
          ·
            refine ⟨24600971587534693569057689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16400647725023129046038459 24600971587534693569057689)
            ·
              refine ⟨18450728690651020176793267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24600971587534693569057689 18450728690651020176793267)
              ·
                refine ⟨27676093035976530265189901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18450728690651020176793267 27676093035976530265189901)
                ·
                  refine ⟨10378534888491198849446213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27676093035976530265189901 10378534888491198849446213)
                  ·
                    refine ⟨1945975291592099784271165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10378534888491198849446213 1945975291592099784271165)
                    ·
                      refine ⟨729740734347037419101687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1945975291592099784271165 729740734347037419101687)
                      ·
                        rfl

theorem cell23_1421165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1421165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421165 prefixEnd_1421165 := by exact prefixLift 1421165
  have htrace : WordTrace (prefixWord ++ tailWord_1421165) baseStart_1421165 baseEnd_1421165 := by
    simpa [prefixWord, tailWord_1421165, baseEnd_1421165] using wordTrace_append hprefix tailTrace_1421165
  have hstable : (prefixWord ++ tailWord_1421165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421165).length < 2 ^ (prefixWord ++ tailWord_1421165).sum := by decide
  have hdescent : baseEnd_1421165 < baseStart_1421165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421202 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_1421202 : Nat := 118140960795 + 1421202 * 2 ^ 59
def prefixEnd_1421202 : Nat := 4983230072969 + 3 ^ 40 * 1421202 * 2
def baseEnd_1421202 : Nat := 81084414792361530482113

theorem tailTrace_1421202 : CollatzResearch.WordTrace tailWord_1421202 prefixEnd_1421202 81084414792361530482113 := by
  unfold tailWord_1421202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12958873849308837705656465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34556996931490233881750573 12958873849308837705656465)
  ·
    refine ⟨9719155386981628279242349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12958873849308837705656465 9719155386981628279242349)
    ·
      refine ⟨3644683270118110604715881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9719155386981628279242349 3644683270118110604715881)
      ·
        refine ⟨2733512452588582953536911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3644683270118110604715881 2733512452588582953536911)
        ·
          refine ⟨4100268678882874430305367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733512452588582953536911 4100268678882874430305367)
          ·
            refine ⟨6150403018324311645458051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100268678882874430305367 6150403018324311645458051)
            ·
              refine ⟨9225604527486467468187077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150403018324311645458051 9225604527486467468187077)
              ·
                refine ⟨1729800848903712650285077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9225604527486467468187077 1729800848903712650285077)
                ·
                  refine ⟨81084414792361530482113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1729800848903712650285077 81084414792361530482113)
                  ·
                    rfl

theorem cell23_1421202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_1421202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421202 prefixEnd_1421202 := by exact prefixLift 1421202
  have htrace : WordTrace (prefixWord ++ tailWord_1421202) baseStart_1421202 baseEnd_1421202 := by
    simpa [prefixWord, tailWord_1421202, baseEnd_1421202] using wordTrace_append hprefix tailTrace_1421202
  have hstable : (prefixWord ++ tailWord_1421202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421202).length < 2 ^ (prefixWord ++ tailWord_1421202).sum := by decide
  have hdescent : baseEnd_1421202 < baseStart_1421202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421230 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1421230 : Nat := 118140960795 + 1421230 * 2 ^ 59
def prefixEnd_1421230 : Nat := 4983230072969 + 3 ^ 40 * 1421230 * 2
def baseEnd_1421230 : Nat := 729774110589579664788889

theorem tailTrace_1421230 : CollatzResearch.WordTrace tailWord_1421230 prefixEnd_1421230 729774110589579664788889 := by
  unfold tailWord_1421230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479564580141738950580643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34557677760755941069763429 6479564580141738950580643)
  ·
    refine ⟨9719346870212608425870965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479564580141738950580643 9719346870212608425870965)
    ·
      refine ⟨911188769082432039925403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9719346870212608425870965 911188769082432039925403)
      ·
        refine ⟨1366783153623648059888105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911188769082432039925403 1366783153623648059888105)
        ·
          refine ⟨1025087365217736044916079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1366783153623648059888105 1025087365217736044916079)
          ·
            refine ⟨1537631047826604067374119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025087365217736044916079 1537631047826604067374119)
            ·
              refine ⟨2306446571739906101061179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537631047826604067374119 2306446571739906101061179)
              ·
                refine ⟨3459669857609859151591769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306446571739906101061179 3459669857609859151591769)
                ·
                  refine ⟨2594752393207394363693827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459669857609859151591769 2594752393207394363693827)
                  ·
                    refine ⟨3892128589811091545540741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2594752393207394363693827 3892128589811091545540741)
                    ·
                      refine ⟨729774110589579664788889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3892128589811091545540741 729774110589579664788889)
                      ·
                        rfl

theorem cell23_1421230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1421230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421230 prefixEnd_1421230 := by exact prefixLift 1421230
  have htrace : WordTrace (prefixWord ++ tailWord_1421230) baseStart_1421230 baseEnd_1421230 := by
    simpa [prefixWord, tailWord_1421230, baseEnd_1421230] using wordTrace_append hprefix tailTrace_1421230
  have hstable : (prefixWord ++ tailWord_1421230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421230).length < 2 ^ (prefixWord ++ tailWord_1421230).sum := by decide
  have hdescent : baseEnd_1421230 < baseStart_1421230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421235 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 4]
def baseStart_1421235 : Nat := 118140960795 + 1421235 * 2 ^ 59
def prefixEnd_1421235 : Nat := 4983230072969 + 3 ^ 40 * 1421235 * 2
def baseEnd_1421235 : Nat := 729776677992852145226365

theorem tailTrace_1421235 : CollatzResearch.WordTrace tailWord_1421235 prefixEnd_1421235 729776677992852145226365 := by
  unfold tailWord_1421235
  simp only [CollatzResearch.WordTrace]
  refine ⟨51836699006115797458577159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34557799337410531639051439 51836699006115797458577159)
  ·
    refine ⟨77755048509173696187865739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51836699006115797458577159 77755048509173696187865739)
    ·
      refine ⟨116632572763760544281798609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77755048509173696187865739 116632572763760544281798609)
      ·
        refine ⟨87474429572820408211348957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116632572763760544281798609 87474429572820408211348957)
        ·
          refine ⟨32802911089807653079255859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87474429572820408211348957 32802911089807653079255859)
          ·
            refine ⟨49204366634711479618883789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32802911089807653079255859 49204366634711479618883789)
            ·
              refine ⟨18451637488016804857081421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49204366634711479618883789 18451637488016804857081421)
              ·
                refine ⟨6919364058006301821405533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18451637488016804857081421 6919364058006301821405533)
                ·
                  refine ⟨2594761521752363183027075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6919364058006301821405533 2594761521752363183027075)
                  ·
                    refine ⟨3892142282628544774540613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2594761521752363183027075 3892142282628544774540613)
                    ·
                      refine ⟨729776677992852145226365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3892142282628544774540613 729776677992852145226365)
                      ·
                        rfl

theorem cell23_1421235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_1421235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421235 prefixEnd_1421235 := by exact prefixLift 1421235
  have htrace : WordTrace (prefixWord ++ tailWord_1421235) baseStart_1421235 baseEnd_1421235 := by
    simpa [prefixWord, tailWord_1421235, baseEnd_1421235] using wordTrace_append hprefix tailTrace_1421235
  have hstable : (prefixWord ++ tailWord_1421235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421235).length < 2 ^ (prefixWord ++ tailWord_1421235).sum := by decide
  have hdescent : baseEnd_1421235 < baseStart_1421235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421246 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_1421246 : Nat := 118140960795 + 1421246 * 2 ^ 59
def prefixEnd_1421246 : Nat := 4983230072969 + 3 ^ 40 * 1421246 * 2
def baseEnd_1421246 : Nat := 729782326280051602188815

theorem tailTrace_1421246 : CollatzResearch.WordTrace tailWord_1421246 prefixEnd_1421246 729782326280051602188815 := by
  unfold tailWord_1421246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479637526134493292153449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34558066806050630891485061 6479637526134493292153449)
  ·
    refine ⟨4859728144600869969115087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6479637526134493292153449 4859728144600869969115087)
    ·
      refine ⟨7289592216901304953672631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859728144600869969115087 7289592216901304953672631)
      ·
        refine ⟨10934388325351957430508947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289592216901304953672631 10934388325351957430508947)
        ·
          refine ⟨16401582488027936145763421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10934388325351957430508947 16401582488027936145763421)
          ·
            refine ⟨6150593433010476054661283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16401582488027936145763421 6150593433010476054661283)
            ·
              refine ⟨9225890149515714081991925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150593433010476054661283 9225890149515714081991925)
              ·
                refine ⟨864927201517098195186743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9225890149515714081991925 864927201517098195186743)
                ·
                  refine ⟨1297390802275647292780115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864927201517098195186743 1297390802275647292780115)
                  ·
                    refine ⟨1946086203413470939170173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297390802275647292780115 1946086203413470939170173)
                    ·
                      refine ⟨729782326280051602188815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1946086203413470939170173 729782326280051602188815)
                      ·
                        rfl

theorem cell23_1421246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_1421246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421246 prefixEnd_1421246 := by exact prefixLift 1421246
  have htrace : WordTrace (prefixWord ++ tailWord_1421246) baseStart_1421246 baseEnd_1421246 := by
    simpa [prefixWord, tailWord_1421246, baseEnd_1421246] using wordTrace_append hprefix tailTrace_1421246
  have hstable : (prefixWord ++ tailWord_1421246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421246).length < 2 ^ (prefixWord ++ tailWord_1421246).sum := by decide
  have hdescent : baseEnd_1421246 < baseStart_1421246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421255 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1421255 : Nat := 118140960795 + 1421255 * 2 ^ 59
def prefixEnd_1421255 : Nat := 4983230072969 + 3 ^ 40 * 1421255 * 2
def baseEnd_1421255 : Nat := 729786947605942066976273

theorem tailTrace_1421255 : CollatzResearch.WordTrace tailWord_1421255 prefixEnd_1421255 729786947605942066976273 := by
  unfold tailWord_1421255
  simp only [CollatzResearch.WordTrace]
  refine ⟨51837428466043340874305219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34558285644028893916203479 51837428466043340874305219)
  ·
    refine ⟨77756142699065011311457829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51837428466043340874305219 77756142699065011311457829)
    ·
      refine ⟨14579276756074689620898343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77756142699065011311457829 14579276756074689620898343)
      ·
        refine ⟨21868915134112034431347515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14579276756074689620898343 21868915134112034431347515)
        ·
          refine ⟨32803372701168051647021273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21868915134112034431347515 32803372701168051647021273)
          ·
            refine ⟨24602529525876038735265955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32803372701168051647021273 24602529525876038735265955)
            ·
              refine ⟨36903794288814058102898933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24602529525876038735265955 36903794288814058102898933)
              ·
                refine ⟨3459730714576317947146775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36903794288814058102898933 3459730714576317947146775)
                ·
                  refine ⟨5189596071864476920720163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459730714576317947146775 5189596071864476920720163)
                  ·
                    refine ⟨7784394107796715381080245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189596071864476920720163 7784394107796715381080245)
                    ·
                      refine ⟨729786947605942066976273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7784394107796715381080245 729786947605942066976273)
                      ·
                        rfl

theorem cell23_1421255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1421255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421255 prefixEnd_1421255 := by exact prefixLift 1421255
  have htrace : WordTrace (prefixWord ++ tailWord_1421255) baseStart_1421255 baseEnd_1421255 := by
    simpa [prefixWord, tailWord_1421255, baseEnd_1421255] using wordTrace_append hprefix tailTrace_1421255
  have hstable : (prefixWord ++ tailWord_1421255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421255).length < 2 ^ (prefixWord ++ tailWord_1421255).sum := by decide
  have hdescent : baseEnd_1421255 < baseStart_1421255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421262 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_1421262 : Nat := 118140960795 + 1421262 * 2 ^ 59
def prefixEnd_1421262 : Nat := 4983230072969 + 3 ^ 40 * 1421262 * 2
def baseEnd_1421262 : Nat := 243263513990174513196247

theorem tailTrace_1421262 : CollatzResearch.WordTrace tailWord_1421262 prefixEnd_1421262 243263513990174513196247 := by
  unfold tailWord_1421262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479710472127247633726255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34558455851345320713206693 6479710472127247633726255)
  ·
    refine ⟨9719565708190871450589383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479710472127247633726255 9719565708190871450589383)
    ·
      refine ⟨14579348562286307175884075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9719565708190871450589383 14579348562286307175884075)
      ·
        refine ⟨21869022843429460763826113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14579348562286307175884075 21869022843429460763826113)
        ·
          refine ⟨16401767132572095572869585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21869022843429460763826113 16401767132572095572869585)
          ·
            refine ⟨12301325349429071679652189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16401767132572095572869585 12301325349429071679652189)
            ·
              refine ⟨4612997006035901879869571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12301325349429071679652189 4612997006035901879869571)
              ·
                refine ⟨6919495509053852819804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612997006035901879869571 6919495509053852819804357)
                ·
                  refine ⟨1297405407947597403713317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6919495509053852819804357 1297405407947597403713317)
                  ·
                    refine ⟨243263513990174513196247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1297405407947597403713317 243263513990174513196247)
                    ·
                      rfl

theorem cell23_1421262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_1421262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421262 prefixEnd_1421262 := by exact prefixLift 1421262
  have htrace : WordTrace (prefixWord ++ tailWord_1421262) baseStart_1421262 baseEnd_1421262 := by
    simpa [prefixWord, tailWord_1421262, baseEnd_1421262] using wordTrace_append hprefix tailTrace_1421262
  have hstable : (prefixWord ++ tailWord_1421262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421262).length < 2 ^ (prefixWord ++ tailWord_1421262).sum := by decide
  have hdescent : baseEnd_1421262 < baseStart_1421262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421319 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1421319 : Nat := 118140960795 + 1421319 * 2 ^ 59
def prefixEnd_1421319 : Nat := 4983230072969 + 3 ^ 40 * 1421319 * 2
def baseEnd_1421319 : Nat := 729819810367829816575979

theorem tailTrace_1421319 : CollatzResearch.WordTrace tailWord_1421319 prefixEnd_1421319 729819810367829816575979 := by
  unfold tailWord_1421319
  simp only [CollatzResearch.WordTrace]
  refine ⟨51839762737811479804635011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34559841825207653203090007 51839762737811479804635011)
  ·
    refine ⟨77759644106717219706952517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51839762737811479804635011 77759644106717219706952517)
    ·
      refine ⟨14579933270009478695053597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77759644106717219706952517 14579933270009478695053597)
      ·
        refine ⟨5467474976253554510645099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14579933270009478695053597 5467474976253554510645099)
        ·
          refine ⟨8201212464380331765967649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467474976253554510645099 8201212464380331765967649)
          ·
            refine ⟨6150909348285248824475737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8201212464380331765967649 6150909348285248824475737)
            ·
              refine ⟨4613182011213936618356803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6150909348285248824475737 4613182011213936618356803)
              ·
                refine ⟨6919773016820904927535205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613182011213936618356803 6919773016820904927535205)
                ·
                  refine ⟨1297457440653919673912851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6919773016820904927535205 1297457440653919673912851)
                  ·
                    refine ⟨1946186160980879510869277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297457440653919673912851 1946186160980879510869277)
                    ·
                      refine ⟨729819810367829816575979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1946186160980879510869277 729819810367829816575979)
                      ·
                        rfl

theorem cell23_1421319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1421319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421319 prefixEnd_1421319 := by exact prefixLift 1421319
  have htrace : WordTrace (prefixWord ++ tailWord_1421319) baseStart_1421319 baseEnd_1421319 := by
    simpa [prefixWord, tailWord_1421319, baseEnd_1421319] using wordTrace_append hprefix tailTrace_1421319
  have hstable : (prefixWord ++ tailWord_1421319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421319).length < 2 ^ (prefixWord ++ tailWord_1421319).sum := by decide
  have hdescent : baseEnd_1421319 < baseStart_1421319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421355 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4]
def baseStart_1421355 : Nat := 118140960795 + 1421355 * 2 ^ 59
def prefixEnd_1421355 : Nat := 4983230072969 + 3 ^ 40 * 1421355 * 2
def baseEnd_1421355 : Nat := 729838295671391675725813

theorem tailTrace_1421355 : CollatzResearch.WordTrace tailWord_1421355 prefixEnd_1421355 729838295671391675725813 := by
  unfold tailWord_1421355
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841075765681057952945519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34560717177120705301963679 51841075765681057952945519)
  ·
    refine ⟨77761613648521586929418279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51841075765681057952945519 77761613648521586929418279)
    ·
      refine ⟨116642420472782380394127419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77761613648521586929418279 116642420472782380394127419)
      ·
        refine ⟨174963630709173570591191129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116642420472782380394127419 174963630709173570591191129)
        ·
          refine ⟨131222723031880177943393347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174963630709173570591191129 131222723031880177943393347)
          ·
            refine ⟨196834084547820266915090021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131222723031880177943393347 196834084547820266915090021)
            ·
              refine ⟨36906390852716300046579379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196834084547820266915090021 36906390852716300046579379)
              ·
                refine ⟨55359586279074450069869069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36906390852716300046579379 55359586279074450069869069)
                ·
                  refine ⟨20759844854652918776200901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55359586279074450069869069 20759844854652918776200901)
                  ·
                    refine ⟨3892470910247422270537669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20759844854652918776200901 3892470910247422270537669)
                    ·
                      refine ⟨729838295671391675725813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3892470910247422270537669 729838295671391675725813)
                      ·
                        rfl

theorem cell23_1421355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_1421355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421355 prefixEnd_1421355 := by exact prefixLift 1421355
  have htrace : WordTrace (prefixWord ++ tailWord_1421355) baseStart_1421355 baseEnd_1421355 := by
    simpa [prefixWord, tailWord_1421355, baseEnd_1421355] using wordTrace_append hprefix tailTrace_1421355
  have hstable : (prefixWord ++ tailWord_1421355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421355).length < 2 ^ (prefixWord ++ tailWord_1421355).sum := by decide
  have hdescent : baseEnd_1421355 < baseStart_1421355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421359 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 4, 2, 2]
def baseStart_1421359 : Nat := 118140960795 + 1421359 * 2 ^ 59
def prefixEnd_1421359 : Nat := 4983230072969 + 3 ^ 40 * 1421359 * 2
def baseEnd_1421359 : Nat := 729840349594009660075795

theorem tailTrace_1421359 : CollatzResearch.WordTrace tailWord_1421359 prefixEnd_1421359 729840349594009660075795 := by
  unfold tailWord_1421359
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841221657666566636091131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34560814438444377757394087 51841221657666566636091131)
  ·
    refine ⟨77761832486499849954136697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51841221657666566636091131 77761832486499849954136697)
    ·
      refine ⟨58321374364874887465602523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77761832486499849954136697 58321374364874887465602523)
      ·
        refine ⟨87482061547312331198403785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58321374364874887465602523 87482061547312331198403785)
        ·
          refine ⟨65611546160484248398802839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87482061547312331198403785 65611546160484248398802839)
          ·
            refine ⟨98417319240726372598204259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65611546160484248398802839 98417319240726372598204259)
            ·
              refine ⟨147625978861089558897306389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98417319240726372598204259 147625978861089558897306389)
              ·
                refine ⟨6919967759113573073311237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147625978861089558897306389 6919967759113573073311237)
                ·
                  refine ⟨1297493954833794951245857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6919967759113573073311237 1297493954833794951245857)
                  ·
                    refine ⟨973120466125346213434393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297493954833794951245857 973120466125346213434393)
                    ·
                      refine ⟨729840349594009660075795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973120466125346213434393 729840349594009660075795)
                      ·
                        rfl

theorem cell23_1421359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 2, 2].length) (baseStart_1421359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421359 prefixEnd_1421359 := by exact prefixLift 1421359
  have htrace : WordTrace (prefixWord ++ tailWord_1421359) baseStart_1421359 baseEnd_1421359 := by
    simpa [prefixWord, tailWord_1421359, baseEnd_1421359] using wordTrace_append hprefix tailTrace_1421359
  have hstable : (prefixWord ++ tailWord_1421359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421359).length < 2 ^ (prefixWord ++ tailWord_1421359).sum := by decide
  have hdescent : baseEnd_1421359 < baseStart_1421359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421362 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1421362 : Nat := 118140960795 + 1421362 * 2 ^ 59
def prefixEnd_1421362 : Nat := 4983230072969 + 3 ^ 40 * 1421362 * 2
def baseEnd_1421362 : Nat := 729841890035973148338281

theorem tailTrace_1421362 : CollatzResearch.WordTrace tailWord_1421362 prefixEnd_1421362 729841890035973148338281 := by
  unfold tailWord_1421362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12960332769163924537112585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34560887384437132098966893 12960332769163924537112585)
  ·
    refine ⟨9720249576872943402834439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12960332769163924537112585 9720249576872943402834439)
    ·
      refine ⟨14580374365309415104251659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9720249576872943402834439 14580374365309415104251659)
      ·
        refine ⟨21870561547964122656377489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14580374365309415104251659 21870561547964122656377489)
        ·
          refine ⟨16402921160973091992283117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21870561547964122656377489 16402921160973091992283117)
          ·
            refine ⟨6151095435364909497106169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16402921160973091992283117 6151095435364909497106169)
            ·
              refine ⟨4613321576523682122829627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151095435364909497106169 4613321576523682122829627)
              ·
                refine ⟨6919982364785523184244441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613321576523682122829627 6919982364785523184244441)
                ·
                  refine ⟨5189986773589142388183331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919982364785523184244441 5189986773589142388183331)
                  ·
                    refine ⟨7784980160383713582274997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189986773589142388183331 7784980160383713582274997)
                    ·
                      refine ⟨729841890035973148338281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7784980160383713582274997 729841890035973148338281)
                      ·
                        rfl

theorem cell23_1421362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1421362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421362 prefixEnd_1421362 := by exact prefixLift 1421362
  have htrace : WordTrace (prefixWord ++ tailWord_1421362) baseStart_1421362 baseEnd_1421362 := by
    simpa [prefixWord, tailWord_1421362, baseEnd_1421362] using wordTrace_append hprefix tailTrace_1421362
  have hstable : (prefixWord ++ tailWord_1421362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421362).length < 2 ^ (prefixWord ++ tailWord_1421362).sum := by decide
  have hdescent : baseEnd_1421362 < baseStart_1421362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421372 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1421372 : Nat := 118140960795 + 1421372 * 2 ^ 59
def prefixEnd_1421372 : Nat := 4983230072969 + 3 ^ 40 * 1421372 * 2
def baseEnd_1421372 : Nat := 729847024842518109213235

theorem tailTrace_1421372 : CollatzResearch.WordTrace tailWord_1421372 prefixEnd_1421372 729847024842518109213235 := by
  unfold tailWord_1421372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25920847903309734928157185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34561130537746313237542913 25920847903309734928157185)
  ·
    refine ⟨19440635927482301196117889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25920847903309734928157185 19440635927482301196117889)
    ·
      refine ⟨14580476945611725897088417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19440635927482301196117889 14580476945611725897088417)
      ·
        refine ⟨10935357709208794422816313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14580476945611725897088417 10935357709208794422816313)
        ·
          refine ⟨8201518281906595817112235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935357709208794422816313 8201518281906595817112235)
          ·
            refine ⟨12302277422859893725668353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201518281906595817112235 12302277422859893725668353)
            ·
              refine ⟨9226708067144920294251265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12302277422859893725668353 9226708067144920294251265)
              ·
                refine ⟨6920031050358690220688449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9226708067144920294251265 6920031050358690220688449)
                ·
                  refine ⟨5190023287769017665516337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6920031050358690220688449 5190023287769017665516337)
                  ·
                    refine ⟨3892517465826763249137253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5190023287769017665516337 3892517465826763249137253)
                    ·
                      refine ⟨729847024842518109213235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3892517465826763249137253 729847024842518109213235)
                      ·
                        rfl

theorem cell23_1421372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1421372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421372 prefixEnd_1421372 := by exact prefixLift 1421372
  have htrace : WordTrace (prefixWord ++ tailWord_1421372) baseStart_1421372 baseEnd_1421372 := by
    simpa [prefixWord, tailWord_1421372, baseEnd_1421372] using wordTrace_append hprefix tailTrace_1421372
  have hstable : (prefixWord ++ tailWord_1421372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421372).length < 2 ^ (prefixWord ++ tailWord_1421372).sum := by decide
  have hdescent : baseEnd_1421372 < baseStart_1421372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421375 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1421375 : Nat := 118140960795 + 1421375 * 2 ^ 59
def prefixEnd_1421375 : Nat := 4983230072969 + 3 ^ 40 * 1421375 * 2
def baseEnd_1421375 : Nat := 729848565284481597475721

theorem tailTrace_1421375 : CollatzResearch.WordTrace tailWord_1421375 prefixEnd_1421375 729848565284481597475721 := by
  unfold tailWord_1421375
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841805225608601368673579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34561203483739067579115719 51841805225608601368673579)
  ·
    refine ⟨77762707838412902053010369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51841805225608601368673579 77762707838412902053010369)
    ·
      refine ⟨58322030878809676539757777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77762707838412902053010369 58322030878809676539757777)
      ·
        refine ⟨43741523159107257404818333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58322030878809676539757777 43741523159107257404818333)
        ·
          refine ⟨16403071184665221526806875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43741523159107257404818333 16403071184665221526806875)
          ·
            refine ⟨24604606776997832290210313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16403071184665221526806875 24604606776997832290210313)
            ·
              refine ⟨18453455082748374217657735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24604606776997832290210313 18453455082748374217657735)
              ·
                refine ⟨27680182624122561326486603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18453455082748374217657735 27680182624122561326486603)
                ·
                  refine ⟨41520273936183841989729905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27680182624122561326486603 41520273936183841989729905)
                  ·
                    refine ⟨31140205452137881492297429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41520273936183841989729905 31140205452137881492297429)
                    ·
                      refine ⟨729848565284481597475721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31140205452137881492297429 729848565284481597475721)
                      ·
                        rfl

theorem cell23_1421375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1421375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421375 prefixEnd_1421375 := by exact prefixLift 1421375
  have htrace : WordTrace (prefixWord ++ tailWord_1421375) baseStart_1421375 baseEnd_1421375 := by
    simpa [prefixWord, tailWord_1421375, baseEnd_1421375] using wordTrace_append hprefix tailTrace_1421375
  have hstable : (prefixWord ++ tailWord_1421375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421375).length < 2 ^ (prefixWord ++ tailWord_1421375).sum := by decide
  have hdescent : baseEnd_1421375 < baseStart_1421375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421376 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 2, 2, 2]
def baseStart_1421376 : Nat := 118140960795 + 1421376 * 2 ^ 59
def prefixEnd_1421376 : Nat := 4983230072969 + 3 ^ 40 * 1421376 * 2
def baseEnd_1421376 : Nat := 729849078765136093563217

theorem tailTrace_1421376 : CollatzResearch.WordTrace tailWord_1421376 prefixEnd_1421376 729849078765136093563217 := by
  unfold tailWord_1421376
  simp only [CollatzResearch.WordTrace]
  refine ⟨25920920849302489269729991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34561227799069985692973321 25920920849302489269729991)
  ·
    refine ⟨38881381273953733904594987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25920920849302489269729991 38881381273953733904594987)
    ·
      refine ⟨58322071910930600856892481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38881381273953733904594987 58322071910930600856892481)
      ·
        refine ⟨43741553933197950642669361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58322071910930600856892481 43741553933197950642669361)
        ·
          refine ⟨32806165449898462982002021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43741553933197950642669361 32806165449898462982002021)
          ·
            refine ⟨6151156021855961809125379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32806165449898462982002021 6151156021855961809125379)
            ·
              refine ⟨9226734032783942713688069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6151156021855961809125379 9226734032783942713688069)
              ·
                refine ⟨1730012631146989258816513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9226734032783942713688069 1730012631146989258816513)
                ·
                  refine ⟨1297509473360241944112385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1730012631146989258816513 1297509473360241944112385)
                  ·
                    refine ⟨973132105020181458084289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297509473360241944112385 973132105020181458084289)
                    ·
                      refine ⟨729849078765136093563217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973132105020181458084289 729849078765136093563217)
                      ·
                        rfl

theorem cell23_1421376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_1421376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421376 prefixEnd_1421376 := by exact prefixLift 1421376
  have htrace : WordTrace (prefixWord ++ tailWord_1421376) baseStart_1421376 baseEnd_1421376 := by
    simpa [prefixWord, tailWord_1421376, baseEnd_1421376] using wordTrace_append hprefix tailTrace_1421376
  have hstable : (prefixWord ++ tailWord_1421376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421376).length < 2 ^ (prefixWord ++ tailWord_1421376).sum := by decide
  have hdescent : baseEnd_1421376 < baseStart_1421376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421389 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1421389 : Nat := 118140960795 + 1421389 * 2 ^ 59
def prefixEnd_1421389 : Nat := 4983230072969 + 3 ^ 40 * 1421389 * 2
def baseEnd_1421389 : Nat := 729855754013644542700657

theorem tailTrace_1421389 : CollatzResearch.WordTrace tailWord_1421389 prefixEnd_1421389 729855754013644542700657 := by
  unfold tailWord_1421389
  simp only [CollatzResearch.WordTrace]
  refine ⟨51842315847557881759683221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34561543898371921173122147 51842315847557881759683221)
  ·
    refine ⟨2430108555354275707485151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51842315847557881759683221 2430108555354275707485151)
    ·
      refine ⟨3645162833031413561227727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430108555354275707485151 3645162833031413561227727)
      ·
        refine ⟨5467744249547120341841591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645162833031413561227727 5467744249547120341841591)
        ·
          refine ⟨8201616374320680512762387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467744249547120341841591 8201616374320680512762387)
          ·
            refine ⟨12302424561481020769143581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201616374320680512762387 12302424561481020769143581)
            ·
              refine ⟨4613409210555382788428843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12302424561481020769143581 4613409210555382788428843)
              ·
                refine ⟨6920113815833074182643265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613409210555382788428843 6920113815833074182643265)
                ·
                  refine ⟨5190085361874805636982449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6920113815833074182643265 5190085361874805636982449)
                  ·
                    refine ⟨3892564021406104227736837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5190085361874805636982449 3892564021406104227736837)
                    ·
                      refine ⟨729855754013644542700657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3892564021406104227736837 729855754013644542700657)
                      ·
                        rfl

theorem cell23_1421389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1421389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421389 prefixEnd_1421389 := by exact prefixLift 1421389
  have htrace : WordTrace (prefixWord ++ tailWord_1421389) baseStart_1421389 baseEnd_1421389 := by
    simpa [prefixWord, tailWord_1421389, baseEnd_1421389] using wordTrace_append hprefix tailTrace_1421389
  have hstable : (prefixWord ++ tailWord_1421389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421389).length < 2 ^ (prefixWord ++ tailWord_1421389).sum := by decide
  have hdescent : baseEnd_1421389 < baseStart_1421389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421432 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_1421432 : Nat := 118140960795 + 1421432 * 2 ^ 59
def prefixEnd_1421432 : Nat := 4983230072969 + 3 ^ 40 * 1421432 * 2
def baseEnd_1421432 : Nat := 729877833681787874462959

theorem tailTrace_1421432 : CollatzResearch.WordTrace tailWord_1421432 prefixEnd_1421432 729877833681787874462959 := by
  unfold tailWord_1421432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25921942093201050051749275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34562589457601400068999033 25921942093201050051749275)
  ·
    refine ⟨38882913139801575077623913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25921942093201050051749275 38882913139801575077623913)
    ·
      refine ⟨29162184854851181308217935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38882913139801575077623913 29162184854851181308217935)
      ·
        refine ⟨43743277282276771962326903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29162184854851181308217935 43743277282276771962326903)
        ·
          refine ⟨65614915923415157943490355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43743277282276771962326903 65614915923415157943490355)
          ·
            refine ⟨98422373885122736915235533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65614915923415157943490355 98422373885122736915235533)
            ·
              refine ⟨36908390206921026343213325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98422373885122736915235533 36908390206921026343213325)
              ·
                refine ⟨13840646327595384878704997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36908390206921026343213325 13840646327595384878704997)
                ·
                  refine ⟨2595121186424134664757187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13840646327595384878704997 2595121186424134664757187)
                  ·
                    refine ⟨3892681779636201997135781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595121186424134664757187 3892681779636201997135781)
                    ·
                      refine ⟨729877833681787874462959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3892681779636201997135781 729877833681787874462959)
                      ·
                        rfl

theorem cell23_1421432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_1421432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421432 prefixEnd_1421432 := by exact prefixLift 1421432
  have htrace : WordTrace (prefixWord ++ tailWord_1421432) baseStart_1421432 baseEnd_1421432 := by
    simpa [prefixWord, tailWord_1421432, baseEnd_1421432] using wordTrace_append hprefix tailTrace_1421432
  have hstable : (prefixWord ++ tailWord_1421432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421432).length < 2 ^ (prefixWord ++ tailWord_1421432).sum := by decide
  have hdescent : baseEnd_1421432 < baseStart_1421432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421449 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 2, 4, 2]
def baseStart_1421449 : Nat := 118140960795 + 1421449 * 2 ^ 59
def prefixEnd_1421449 : Nat := 4983230072969 + 3 ^ 40 * 1421449 * 2
def baseEnd_1421449 : Nat := 729886562852914307950381

theorem tailTrace_1421449 : CollatzResearch.WordTrace tailWord_1421449 prefixEnd_1421449 729886562852914307950381 := by
  unfold tailWord_1421449
  simp only [CollatzResearch.WordTrace]
  refine ⟨51844504227340512006867401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34563002818227008004578267 51844504227340512006867401)
  ·
    refine ⟨38883378170505384005150551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51844504227340512006867401 38883378170505384005150551)
    ·
      refine ⟨58325067255758076007725827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38883378170505384005150551 58325067255758076007725827)
      ·
        refine ⟨87487600883637114011588741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58325067255758076007725827 87487600883637114011588741)
        ·
          refine ⟨16403925165681958877172889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87487600883637114011588741 16403925165681958877172889)
          ·
            refine ⟨12302943874261469157879667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16403925165681958877172889 12302943874261469157879667)
            ·
              refine ⟨18454415811392203736819501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12302943874261469157879667 18454415811392203736819501)
              ·
                refine ⟨6920405929272076401307313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18454415811392203736819501 6920405929272076401307313)
                ·
                  refine ⟨5190304446954057300980485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6920405929272076401307313 5190304446954057300980485)
                  ·
                    refine ⟨973182083803885743933841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190304446954057300980485 973182083803885743933841)
                    ·
                      refine ⟨729886562852914307950381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973182083803885743933841 729886562852914307950381)
                      ·
                        rfl

theorem cell23_1421449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 4, 2].length) (baseStart_1421449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421449 prefixEnd_1421449 := by exact prefixLift 1421449
  have htrace : WordTrace (prefixWord ++ tailWord_1421449) baseStart_1421449 baseEnd_1421449 := by
    simpa [prefixWord, tailWord_1421449, baseEnd_1421449] using wordTrace_append hprefix tailTrace_1421449
  have hstable : (prefixWord ++ tailWord_1421449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421449).length < 2 ^ (prefixWord ++ tailWord_1421449).sum := by decide
  have hdescent : baseEnd_1421449 < baseStart_1421449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421469 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1421469 : Nat := 118140960795 + 1421469 * 2 ^ 59
def prefixEnd_1421469 : Nat := 4983230072969 + 3 ^ 40 * 1421469 * 2
def baseEnd_1421469 : Nat := 729896832466004229700289

theorem tailTrace_1421469 : CollatzResearch.WordTrace tailWord_1421469 prefixEnd_1421469 729896832466004229700289 := by
  unfold tailWord_1421469
  simp only [CollatzResearch.WordTrace]
  refine ⟨51845233687268055422595461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34563489124845370281730307 51845233687268055422595461)
  ·
    refine ⟨9720981316362760391736649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51845233687268055422595461 9720981316362760391736649)
    ·
      refine ⟨7290735987272070293802487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9720981316362760391736649 7290735987272070293802487)
      ·
        refine ⟨10936103980908105440703731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290735987272070293802487 10936103980908105440703731)
        ·
          refine ⟨16404155971362158161055597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10936103980908105440703731 16404155971362158161055597)
          ·
            refine ⟨6151558489260809310395849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16404155971362158161055597 6151558489260809310395849)
            ·
              refine ⟨4613668866945606982796887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151558489260809310395849 4613668866945606982796887)
              ·
                refine ⟨6920503300418410474195331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613668866945606982796887 6920503300418410474195331)
                ·
                  refine ⟨10380754950627615711292997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6920503300418410474195331 10380754950627615711292997)
                  ·
                    refine ⟨1946391553242677945867437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10380754950627615711292997 1946391553242677945867437)
                    ·
                      refine ⟨729896832466004229700289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1946391553242677945867437 729896832466004229700289)
                      ·
                        rfl

theorem cell23_1421469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1421469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421469 prefixEnd_1421469 := by exact prefixLift 1421469
  have htrace : WordTrace (prefixWord ++ tailWord_1421469) baseStart_1421469 baseEnd_1421469 := by
    simpa [prefixWord, tailWord_1421469, baseEnd_1421469] using wordTrace_append hprefix tailTrace_1421469
  have hstable : (prefixWord ++ tailWord_1421469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421469).length < 2 ^ (prefixWord ++ tailWord_1421469).sum := by decide
  have hdescent : baseEnd_1421469 < baseStart_1421469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421472 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 8]
def baseStart_1421472 : Nat := 118140960795 + 1421472 * 2 ^ 59
def prefixEnd_1421472 : Nat := 4983230072969 + 3 ^ 40 * 1421472 * 2
def baseEnd_1421472 : Nat := 81099819211996413106975

theorem tailTrace_1421472 : CollatzResearch.WordTrace tailWord_1421472 prefixEnd_1421472 81099819211996413106975 := by
  unfold tailWord_1421472
  simp only [CollatzResearch.WordTrace]
  refine ⟨25922671553128593467477335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34563562070838124623303113 25922671553128593467477335)
  ·
    refine ⟨38884007329692890201216003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25922671553128593467477335 38884007329692890201216003)
    ·
      refine ⟨58326010994539335301824005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38884007329692890201216003 58326010994539335301824005)
      ·
        refine ⟨10936127061476125369092001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58326010994539335301824005 10936127061476125369092001)
        ·
          refine ⟨8202095296107094026819001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10936127061476125369092001 8202095296107094026819001)
          ·
            refine ⟨6151571472080320520114251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8202095296107094026819001 6151571472080320520114251)
            ·
              refine ⟨9227357208120480780171377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6151571472080320520114251 9227357208120480780171377)
              ·
                refine ⟨6920517906090360585128533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9227357208120480780171377 6920517906090360585128533)
                ·
                  refine ⟨81099819211996413106975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6920517906090360585128533 81099819211996413106975)
                  ·
                    rfl

theorem cell23_1421472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_1421472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421472 prefixEnd_1421472 := by exact prefixLift 1421472
  have htrace : WordTrace (prefixWord ++ tailWord_1421472) baseStart_1421472 baseEnd_1421472 := by
    simpa [prefixWord, tailWord_1421472, baseEnd_1421472] using wordTrace_append hprefix tailTrace_1421472
  have hstable : (prefixWord ++ tailWord_1421472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421472).length < 2 ^ (prefixWord ++ tailWord_1421472).sum := by decide
  have hdescent : baseEnd_1421472 < baseStart_1421472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421509 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 3, 5, 2]
def baseStart_1421509 : Nat := 118140960795 + 1421509 * 2 ^ 59
def prefixEnd_1421509 : Nat := 4983230072969 + 3 ^ 40 * 1421509 * 2
def baseEnd_1421509 : Nat := 729917371692184073200105

theorem tailTrace_1421509 : CollatzResearch.WordTrace tailWord_1421509 prefixEnd_1421509 729917371692184073200105 := by
  unfold tailWord_1421509
  simp only [CollatzResearch.WordTrace]
  refine ⟨51846692607123142254051581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34564461738082094836034387 51846692607123142254051581)
  ·
    refine ⟨19442509727671178345269343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51846692607123142254051581 19442509727671178345269343)
    ·
      refine ⟨29163764591506767517904015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19442509727671178345269343 29163764591506767517904015)
      ·
        refine ⟨43745646887260151276856023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29163764591506767517904015 43745646887260151276856023)
        ·
          refine ⟨65618470330890226915284035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43745646887260151276856023 65618470330890226915284035)
          ·
            refine ⟨98427705496335340372926053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65618470330890226915284035 98427705496335340372926053)
            ·
              refine ⟨18455194780562876319923635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98427705496335340372926053 18455194780562876319923635)
              ·
                refine ⟨27682792170844314479885453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18455194780562876319923635 27682792170844314479885453)
                ·
                  refine ⟨10381047064066617929957045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27682792170844314479885453 10381047064066617929957045)
                  ·
                    refine ⟨973223162256245430933473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10381047064066617929957045 973223162256245430933473)
                    ·
                      refine ⟨729917371692184073200105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973223162256245430933473 729917371692184073200105)
                      ·
                        rfl

theorem cell23_1421509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_1421509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421509 prefixEnd_1421509 := by exact prefixLift 1421509
  have htrace : WordTrace (prefixWord ++ tailWord_1421509) baseStart_1421509 baseEnd_1421509 := by
    simpa [prefixWord, tailWord_1421509, baseEnd_1421509] using wordTrace_append hprefix tailTrace_1421509
  have hstable : (prefixWord ++ tailWord_1421509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421509).length < 2 ^ (prefixWord ++ tailWord_1421509).sum := by decide
  have hdescent : baseEnd_1421509 < baseStart_1421509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421536 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 1, 5]
def baseStart_1421536 : Nat := 118140960795 + 1421536 * 2 ^ 59
def prefixEnd_1421536 : Nat := 4983230072969 + 3 ^ 40 * 1421536 * 2
def baseEnd_1421536 : Nat := 243310411889951822520827

theorem tailTrace_1421536 : CollatzResearch.WordTrace tailWord_1421536 prefixEnd_1421536 243310411889951822520827 := by
  unfold tailWord_1421536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25923838689012662932642231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34565118252016883910189641 25923838689012662932642231)
  ·
    refine ⟨38885758033518994398963347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25923838689012662932642231 38885758033518994398963347)
    ·
      refine ⟨58328637050278491598445021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38885758033518994398963347 58328637050278491598445021)
      ·
        refine ⟨21873238893854434349416883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58328637050278491598445021 21873238893854434349416883)
        ·
          refine ⟨32809858340781651524125325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21873238893854434349416883 32809858340781651524125325)
          ·
            refine ⟨12303696877793119321546997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32809858340781651524125325 12303696877793119321546997)
            ·
              refine ⟨1153471582293104936395031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12303696877793119321546997 1153471582293104936395031)
              ·
                refine ⟨1730207373439657404592547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153471582293104936395031 1730207373439657404592547)
                ·
                  refine ⟨2595311060159486106888821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730207373439657404592547 2595311060159486106888821)
                  ·
                    refine ⟨243310411889951822520827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2595311060159486106888821 243310411889951822520827)
                    ·
                      rfl

theorem cell23_1421536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 5].length) (baseStart_1421536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421536 prefixEnd_1421536 := by exact prefixLift 1421536
  have htrace : WordTrace (prefixWord ++ tailWord_1421536) baseStart_1421536 baseEnd_1421536 := by
    simpa [prefixWord, tailWord_1421536, baseEnd_1421536] using wordTrace_append hprefix tailTrace_1421536
  have hstable : (prefixWord ++ tailWord_1421536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421536).length < 2 ^ (prefixWord ++ tailWord_1421536).sum := by decide
  have hdescent : baseEnd_1421536 < baseStart_1421536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421543 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1421543 : Nat := 118140960795 + 1421543 * 2 ^ 59
def prefixEnd_1421543 : Nat := 4983230072969 + 3 ^ 40 * 1421543 * 2
def baseEnd_1421543 : Nat := 729934830034436940174949

theorem tailTrace_1421543 : CollatzResearch.WordTrace tailWord_1421543 prefixEnd_1421543 729934830034436940174949 := by
  unfold tailWord_1421543
  simp only [CollatzResearch.WordTrace]
  refine ⟨51847932688999966060789283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34565288459333310707192855 51847932688999966060789283)
  ·
    refine ⟨77771899033499949091183925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51847932688999966060789283 77771899033499949091183925)
    ·
      refine ⟨7291115534390620227298493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77771899033499949091183925 7291115534390620227298493)
      ·
        refine ⟨2734168325396482585236935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7291115534390620227298493 2734168325396482585236935)
        ·
          refine ⟨4101252488094723877855403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734168325396482585236935 4101252488094723877855403)
          ·
            refine ⟨6151878732142085816783105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101252488094723877855403 6151878732142085816783105)
            ·
              refine ⟨4613909049106564362587329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151878732142085816783105 4613909049106564362587329)
              ·
                refine ⟨3460431786829923271940497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4613909049106564362587329 3460431786829923271940497)
                ·
                  refine ⟨2595323840122442453955373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3460431786829923271940497 2595323840122442453955373)
                  ·
                    refine ⟨973246440045915920233265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595323840122442453955373 973246440045915920233265)
                    ·
                      refine ⟨729934830034436940174949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973246440045915920233265 729934830034436940174949)
                      ·
                        rfl

theorem cell23_1421543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1421543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421543 prefixEnd_1421543 := by exact prefixLift 1421543
  have htrace : WordTrace (prefixWord ++ tailWord_1421543) baseStart_1421543 baseEnd_1421543 := by
    simpa [prefixWord, tailWord_1421543, baseEnd_1421543] using wordTrace_append hprefix tailTrace_1421543
  have hstable : (prefixWord ++ tailWord_1421543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421543).length < 2 ^ (prefixWord ++ tailWord_1421543).sum := by decide
  have hdescent : baseEnd_1421543 < baseStart_1421543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421552 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_1421552 : Nat := 118140960795 + 1421552 * 2 ^ 59
def prefixEnd_1421552 : Nat := 4983230072969 + 3 ^ 40 * 1421552 * 2
def baseEnd_1421552 : Nat := 729939451360327404962407

theorem tailTrace_1421552 : CollatzResearch.WordTrace tailWord_1421552 prefixEnd_1421552 729939451360327404962407 := by
  unfold tailWord_1421552
  simp only [CollatzResearch.WordTrace]
  refine ⟨25924130472983680298933455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34565507297311573731911273 25924130472983680298933455)
  ·
    refine ⟨38886195709475520448400183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25924130472983680298933455 38886195709475520448400183)
    ·
      refine ⟨58329293564213280672600275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38886195709475520448400183 58329293564213280672600275)
      ·
        refine ⟨87493940346319921008900413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58329293564213280672600275 87493940346319921008900413)
        ·
          refine ⟨32810227629869970378337655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87493940346319921008900413 32810227629869970378337655)
          ·
            refine ⟨49215341444804955567506483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32810227629869970378337655 49215341444804955567506483)
            ·
              refine ⟨73823012167207433351259725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49215341444804955567506483 73823012167207433351259725)
              ·
                refine ⟨27683629562702787506722397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73823012167207433351259725 27683629562702787506722397)
                ·
                  refine ⟨10381361086013545315020899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27683629562702787506722397 10381361086013545315020899)
                  ·
                    refine ⟨15572041629020317972531349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10381361086013545315020899 15572041629020317972531349)
                    ·
                      refine ⟨729939451360327404962407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15572041629020317972531349 729939451360327404962407)
                      ·
                        rfl

theorem cell23_1421552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_1421552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421552 prefixEnd_1421552 := by exact prefixLift 1421552
  have htrace : WordTrace (prefixWord ++ tailWord_1421552) baseStart_1421552 baseEnd_1421552 := by
    simpa [prefixWord, tailWord_1421552, baseEnd_1421552] using wordTrace_append hprefix tailTrace_1421552
  have hstable : (prefixWord ++ tailWord_1421552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421552).length < 2 ^ (prefixWord ++ tailWord_1421552).sum := by decide
  have hdescent : baseEnd_1421552 < baseStart_1421552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421566 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1421566 : Nat := 118140960795 + 1421566 * 2 ^ 59
def prefixEnd_1421566 : Nat := 4983230072969 + 3 ^ 40 * 1421566 * 2
def baseEnd_1421566 : Nat := 243315546696496783395781

theorem tailTrace_1421566 : CollatzResearch.WordTrace tailWord_1421566 prefixEnd_1421566 243315546696496783395781 := by
  unfold tailWord_1421566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481096445989580123609569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34565847711944427325917701 6481096445989580123609569)
  ·
    refine ⟨4860822334492185092707177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6481096445989580123609569 4860822334492185092707177)
    ·
      refine ⟨3645616750869138819530383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4860822334492185092707177 3645616750869138819530383)
      ·
        refine ⟨5468425126303708229295575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645616750869138819530383 5468425126303708229295575)
        ·
          refine ⟨8202637689455562343943363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5468425126303708229295575 8202637689455562343943363)
          ·
            refine ⟨12303956534183343515915045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8202637689455562343943363 12303956534183343515915045)
            ·
              refine ⟨2306991850159376909234071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12303956534183343515915045 2306991850159376909234071)
              ·
                refine ⟨3460487775239065363851107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306991850159376909234071 3460487775239065363851107)
                ·
                  refine ⟨5190731662858598045776661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460487775239065363851107 5190731662858598045776661)
                  ·
                    refine ⟨243315546696496783395781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5190731662858598045776661 243315546696496783395781)
                    ·
                      rfl

theorem cell23_1421566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1421566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421566 prefixEnd_1421566 := by exact prefixLift 1421566
  have htrace : WordTrace (prefixWord ++ tailWord_1421566) baseStart_1421566 baseEnd_1421566 := by
    simpa [prefixWord, tailWord_1421566, baseEnd_1421566] using wordTrace_append hprefix tailTrace_1421566
  have hstable : (prefixWord ++ tailWord_1421566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421566).length < 2 ^ (prefixWord ++ tailWord_1421566).sum := by decide
  have hdescent : baseEnd_1421566 < baseStart_1421566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421576 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1421576 : Nat := 118140960795 + 1421576 * 2 ^ 59
def prefixEnd_1421576 : Nat := 4983230072969 + 3 ^ 40 * 1421576 * 2
def baseEnd_1421576 : Nat := 729951774896035311062297

theorem tailTrace_1421576 : CollatzResearch.WordTrace tailWord_1421576 prefixEnd_1421576 729951774896035311062297 := by
  unfold tailWord_1421576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25924568148940206348370291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34566090865253608464493721 25924568148940206348370291)
  ·
    refine ⟨38886852223410309522555437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25924568148940206348370291 38886852223410309522555437)
    ·
      refine ⟨14582569583778866070958289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38886852223410309522555437 14582569583778866070958289)
      ·
        refine ⟨10936927187834149553218717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14582569583778866070958289 10936927187834149553218717)
        ·
          refine ⟨4101347695437806082457019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10936927187834149553218717 4101347695437806082457019)
          ·
            refine ⟨6152021543156709123685529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101347695437806082457019 6152021543156709123685529)
            ·
              refine ⟨4614016157367531842764147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6152021543156709123685529 4614016157367531842764147)
              ·
                refine ⟨6921024236051297764146221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614016157367531842764147 6921024236051297764146221)
                ·
                  refine ⟨2595384088519236661554833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6921024236051297764146221 2595384088519236661554833)
                  ·
                    refine ⟨1946538066389427496166125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2595384088519236661554833 1946538066389427496166125)
                    ·
                      refine ⟨729951774896035311062297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1946538066389427496166125 729951774896035311062297)
                      ·
                        rfl

theorem cell23_1421576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1421576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421576 prefixEnd_1421576 := by exact prefixLift 1421576
  have htrace : WordTrace (prefixWord ++ tailWord_1421576) baseStart_1421576 baseEnd_1421576 := by
    simpa [prefixWord, tailWord_1421576, baseEnd_1421576] using wordTrace_append hprefix tailTrace_1421576
  have hstable : (prefixWord ++ tailWord_1421576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421576).length < 2 ^ (prefixWord ++ tailWord_1421576).sum := by decide
  have hdescent : baseEnd_1421576 < baseStart_1421576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421579 : List Nat := [1, 1, 1, 1, 5, 2, 5, 7]
def baseStart_1421579 : Nat := 118140960795 + 1421579 * 2 ^ 59
def prefixEnd_1421579 : Nat := 4983230072969 + 3 ^ 40 * 1421579 * 2
def baseEnd_1421579 : Nat := 27035307975481437012029

theorem tailTrace_1421579 : CollatzResearch.WordTrace tailWord_1421579 prefixEnd_1421579 27035307975481437012029 := by
  unfold tailWord_1421579
  simp only [CollatzResearch.WordTrace]
  refine ⟨51849245716869544209099791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34566163811246362806066527 51849245716869544209099791)
  ·
    refine ⟨77773868575304316313649687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51849245716869544209099791 77773868575304316313649687)
    ·
      refine ⟨116660802862956474470474531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77773868575304316313649687 116660802862956474470474531)
      ·
        refine ⟨174991204294434711705711797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116660802862956474470474531 174991204294434711705711797)
        ·
          refine ⟨16405425402603254222410481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174991204294434711705711797 16405425402603254222410481)
          ·
            refine ⟨12304069051952440666807861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16405425402603254222410481 12304069051952440666807861)
            ·
              refine ⟨1153506473620541312513237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12304069051952440666807861 1153506473620541312513237)
              ·
                refine ⟨27035307975481437012029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1153506473620541312513237 27035307975481437012029)
                ·
                  rfl

theorem cell23_1421579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 7].length) (baseStart_1421579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421579 prefixEnd_1421579 := by exact prefixLift 1421579
  have htrace : WordTrace (prefixWord ++ tailWord_1421579) baseStart_1421579 baseEnd_1421579 := by
    simpa [prefixWord, tailWord_1421579, baseEnd_1421579] using wordTrace_append hprefix tailTrace_1421579
  have hstable : (prefixWord ++ tailWord_1421579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421579).length < 2 ^ (prefixWord ++ tailWord_1421579).sum := by decide
  have hdescent : baseEnd_1421579 < baseStart_1421579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421616 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 3, 3, 2]
def baseStart_1421616 : Nat := 118140960795 + 1421616 * 2 ^ 59
def prefixEnd_1421616 : Nat := 4983230072969 + 3 ^ 40 * 1421616 * 2
def baseEnd_1421616 : Nat := 729972314122215154562113

theorem tailTrace_1421616 : CollatzResearch.WordTrace tailWord_1421616 prefixEnd_1421616 729972314122215154562113 := by
  unfold tailWord_1421616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25925297608867749764098351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34567063478490333018797801 25925297608867749764098351)
  ·
    refine ⟨38887946413301624646147527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25925297608867749764098351 38887946413301624646147527)
    ·
      refine ⟨58331919619952436969221291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38887946413301624646147527 58331919619952436969221291)
      ·
        refine ⟨87497879429928655453831937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58331919619952436969221291 87497879429928655453831937)
        ·
          refine ⟨65623409572446491590373953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87497879429928655453831937 65623409572446491590373953)
          ·
            refine ⟨49217557179334868692780465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65623409572446491590373953 49217557179334868692780465)
            ·
              refine ⟨36913167884501151519585349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49217557179334868692780465 36913167884501151519585349)
              ·
                refine ⟨6921218978343965909922253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36913167884501151519585349 6921218978343965909922253)
                ·
                  refine ⟨2595457116878987216220845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6921218978343965909922253 2595457116878987216220845)
                  ·
                    refine ⟨973296418829620206082817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595457116878987216220845 973296418829620206082817)
                    ·
                      refine ⟨729972314122215154562113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973296418829620206082817 729972314122215154562113)
                      ·
                        rfl

theorem cell23_1421616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 3, 2].length) (baseStart_1421616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421616 prefixEnd_1421616 := by exact prefixLift 1421616
  have htrace : WordTrace (prefixWord ++ tailWord_1421616) baseStart_1421616 baseEnd_1421616 := by
    simpa [prefixWord, tailWord_1421616, baseEnd_1421616] using wordTrace_append hprefix tailTrace_1421616
  have hstable : (prefixWord ++ tailWord_1421616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421616).length < 2 ^ (prefixWord ++ tailWord_1421616).sum := by decide
  have hdescent : baseEnd_1421616 < baseStart_1421616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421649 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1421649 : Nat := 118140960795 + 1421649 * 2 ^ 59
def prefixEnd_1421649 : Nat := 4983230072969 + 3 ^ 40 * 1421649 * 2
def baseEnd_1421649 : Nat := 729989258983813525449461

theorem tailTrace_1421649 : CollatzResearch.WordTrace tailWord_1421649 prefixEnd_1421649 729989258983813525449461 := by
  unfold tailWord_1421649
  simp only [CollatzResearch.WordTrace]
  refine ⟨51851798826615946164148001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34567865884410630776098667 51851798826615946164148001)
  ·
    refine ⟨38888849119961959623111001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51851798826615946164148001 38888849119961959623111001)
    ·
      refine ⟨29166636839971469717333251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38888849119961959623111001 29166636839971469717333251)
      ·
        refine ⟨43749955259957204575999877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29166636839971469717333251 43749955259957204575999877)
        ·
          refine ⟨8203116611241975857999977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43749955259957204575999877 8203116611241975857999977)
          ·
            refine ⟨6152337458431481893499983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8203116611241975857999977 6152337458431481893499983)
            ·
              refine ⟨9228506187647222840249975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152337458431481893499983 9228506187647222840249975)
              ·
                refine ⟨13842759281470834260374963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9228506187647222840249975 13842759281470834260374963)
                ·
                  refine ⟨20764138922206251390562445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13842759281470834260374963 20764138922206251390562445)
                  ·
                    refine ⟨7786552095827344271460917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20764138922206251390562445 7786552095827344271460917)
                    ·
                      refine ⟨729989258983813525449461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7786552095827344271460917 729989258983813525449461)
                      ·
                        rfl

theorem cell23_1421649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1421649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421649 prefixEnd_1421649 := by exact prefixLift 1421649
  have htrace : WordTrace (prefixWord ++ tailWord_1421649) baseStart_1421649 baseEnd_1421649 := by
    simpa [prefixWord, tailWord_1421649, baseEnd_1421649] using wordTrace_append hprefix tailTrace_1421649
  have hstable : (prefixWord ++ tailWord_1421649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421649).length < 2 ^ (prefixWord ++ tailWord_1421649).sum := by decide
  have hdescent : baseEnd_1421649 < baseStart_1421649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421663 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 4, 2, 2]
def baseStart_1421663 : Nat := 118140960795 + 1421663 * 2 ^ 59
def prefixEnd_1421663 : Nat := 4983230072969 + 3 ^ 40 * 1421663 * 2
def baseEnd_1421663 : Nat := 729996447712976470674397

theorem tailTrace_1421663 : CollatzResearch.WordTrace tailWord_1421663 prefixEnd_1421663 729996447712976470674397 := by
  unfold tailWord_1421663
  simp only [CollatzResearch.WordTrace]
  refine ⟨51852309448565226555157643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34568206299043484370105095 51852309448565226555157643)
  ·
    refine ⟨77778464172847839832736465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51852309448565226555157643 77778464172847839832736465)
    ·
      refine ⟨58333848129635879874552349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77778464172847839832736465 58333848129635879874552349)
      ·
        refine ⟨21875193048613454952957131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58333848129635879874552349 21875193048613454952957131)
        ·
          refine ⟨32812789572920182429435697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21875193048613454952957131 32812789572920182429435697)
          ·
            refine ⟨24609592179690136822076773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32812789572920182429435697 24609592179690136822076773)
            ·
              refine ⟨4614298533691900654139395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24609592179690136822076773 4614298533691900654139395)
              ·
                refine ⟨6921447800537850981209093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614298533691900654139395 6921447800537850981209093)
                ·
                  refine ⟨1297771462600847058976705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6921447800537850981209093 1297771462600847058976705)
                  ·
                    refine ⟨973328596950635294232529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297771462600847058976705 973328596950635294232529)
                    ·
                      refine ⟨729996447712976470674397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973328596950635294232529 729996447712976470674397)
                      ·
                        rfl

theorem cell23_1421663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_1421663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421663 prefixEnd_1421663 := by exact prefixLift 1421663
  have htrace : WordTrace (prefixWord ++ tailWord_1421663) baseStart_1421663 baseEnd_1421663 := by
    simpa [prefixWord, tailWord_1421663, baseEnd_1421663] using wordTrace_append hprefix tailTrace_1421663
  have hstable : (prefixWord ++ tailWord_1421663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421663).length < 2 ^ (prefixWord ++ tailWord_1421663).sum := by decide
  have hdescent : baseEnd_1421663 < baseStart_1421663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421680 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 2, 2, 2]
def baseStart_1421680 : Nat := 118140960795 + 1421680 * 2 ^ 59
def prefixEnd_1421680 : Nat := 4983230072969 + 3 ^ 40 * 1421680 * 2
def baseEnd_1421680 : Nat := 730005176884102904161819

theorem tailTrace_1421680 : CollatzResearch.WordTrace tailWord_1421680 prefixEnd_1421680 730005176884102904161819 := by
  unfold tailWord_1421680
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926464744751819229263247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34568619659669092305684329 25926464744751819229263247)
  ·
    refine ⟨38889697117127728843894871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25926464744751819229263247 38889697117127728843894871)
    ·
      refine ⟨58334545675691593265842307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38889697117127728843894871 58334545675691593265842307)
      ·
        refine ⟨87501818513537389898763461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58334545675691593265842307 87501818513537389898763461)
        ·
          refine ⟨16406590971288260606018149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87501818513537389898763461 16406590971288260606018149)
          ·
            refine ⟨3076235807116548863628403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16406590971288260606018149 3076235807116548863628403)
            ·
              refine ⟨4614353710674823295442605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076235807116548863628403 4614353710674823295442605)
              ·
                refine ⟨1730382641503058735790977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4614353710674823295442605 1730382641503058735790977)
                ·
                  refine ⟨1297786981127294051843233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1730382641503058735790977 1297786981127294051843233)
                  ·
                    refine ⟨973340235845470538882425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297786981127294051843233 973340235845470538882425)
                    ·
                      refine ⟨730005176884102904161819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973340235845470538882425 730005176884102904161819)
                      ·
                        rfl

theorem cell23_1421680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 2, 2].length) (baseStart_1421680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421680 prefixEnd_1421680 := by exact prefixLift 1421680
  have htrace : WordTrace (prefixWord ++ tailWord_1421680) baseStart_1421680 baseEnd_1421680 := by
    simpa [prefixWord, tailWord_1421680, baseEnd_1421680] using wordTrace_append hprefix tailTrace_1421680
  have hstable : (prefixWord ++ tailWord_1421680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421680).length < 2 ^ (prefixWord ++ tailWord_1421680).sum := by decide
  have hdescent : baseEnd_1421680 < baseStart_1421680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421720 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 5]
def baseStart_1421720 : Nat := 118140960795 + 1421720 * 2 ^ 59
def prefixEnd_1421720 : Nat := 4983230072969 + 3 ^ 40 * 1421720 * 2
def baseEnd_1421720 : Nat := 81113968456698083073515

theorem tailTrace_1421720 : CollatzResearch.WordTrace tailWord_1421720 prefixEnd_1421720 81113968456698083073515 := by
  unfold tailWord_1421720
  simp only [CollatzResearch.WordTrace]
  refine ⟨25927194204679362644991307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34569592272905816859988409 25927194204679362644991307)
  ·
    refine ⟨38890791307019043967486961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25927194204679362644991307 38890791307019043967486961)
    ·
      refine ⟨29168093480264282975615221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38890791307019043967486961 29168093480264282975615221)
      ·
        refine ⟨2734508763774776528963927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29168093480264282975615221 2734508763774776528963927)
        ·
          refine ⟨4101763145662164793445891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734508763774776528963927 4101763145662164793445891)
          ·
            refine ⟨6152644718493247190168837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101763145662164793445891 6152644718493247190168837)
            ·
              refine ⟨1153620884717483848156657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6152644718493247190168837 1153620884717483848156657)
              ·
                refine ⟨865215663538112886117493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153620884717483848156657 865215663538112886117493)
                ·
                  refine ⟨81113968456698083073515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 865215663538112886117493 81113968456698083073515)
                  ·
                    rfl

theorem cell23_1421720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 5].length) (baseStart_1421720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421720 prefixEnd_1421720 := by exact prefixLift 1421720
  have htrace : WordTrace (prefixWord ++ tailWord_1421720) baseStart_1421720 baseEnd_1421720 := by
    simpa [prefixWord, tailWord_1421720, baseEnd_1421720] using wordTrace_append hprefix tailTrace_1421720
  have hstable : (prefixWord ++ tailWord_1421720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421720).length < 2 ^ (prefixWord ++ tailWord_1421720).sum := by decide
  have hdescent : baseEnd_1421720 < baseStart_1421720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421753 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1421753 : Nat := 118140960795 + 1421753 * 2 ^ 59
def prefixEnd_1421753 : Nat := 4983230072969 + 3 ^ 40 * 1421753 * 2
def baseEnd_1421753 : Nat := 730042660971881118548983

theorem tailTrace_1421753 : CollatzResearch.WordTrace tailWord_1421753 prefixEnd_1421753 730042660971881118548983 := by
  unfold tailWord_1421753
  simp only [CollatzResearch.WordTrace]
  refine ⟨51855592018239171925933913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34570394678826114617289275 51855592018239171925933913)
  ·
    refine ⟨38891694013679378944450435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51855592018239171925933913 38891694013679378944450435)
    ·
      refine ⟨58337541020519068416675653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38891694013679378944450435 58337541020519068416675653)
      ·
        refine ⟨10938288941347325328126685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58337541020519068416675653 10938288941347325328126685)
        ·
          refine ⟨4101858353005246998047507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10938288941347325328126685 4101858353005246998047507)
          ·
            refine ⟨6152787529507870497071261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101858353005246998047507 6152787529507870497071261)
            ·
              refine ⟨2307295323565451436401723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6152787529507870497071261 2307295323565451436401723)
              ·
                refine ⟨3460942985348177154602585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307295323565451436401723 3460942985348177154602585)
                ·
                  refine ⟨2595707239011132865951939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3460942985348177154602585 2595707239011132865951939)
                  ·
                    refine ⟨3893560858516699298927909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595707239011132865951939 3893560858516699298927909)
                    ·
                      refine ⟨730042660971881118548983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3893560858516699298927909 730042660971881118548983)
                      ·
                        rfl

theorem cell23_1421753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1421753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421753 prefixEnd_1421753 := by exact prefixLift 1421753
  have htrace : WordTrace (prefixWord ++ tailWord_1421753) baseStart_1421753 baseEnd_1421753 := by
    simpa [prefixWord, tailWord_1421753, baseEnd_1421753] using wordTrace_append hprefix tailTrace_1421753
  have hstable : (prefixWord ++ tailWord_1421753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421753).length < 2 ^ (prefixWord ++ tailWord_1421753).sum := by decide
  have hdescent : baseEnd_1421753 < baseStart_1421753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421780 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1421780 : Nat := 118140960795 + 1421780 * 2 ^ 59
def prefixEnd_1421780 : Nat := 4983230072969 + 3 ^ 40 * 1421780 * 2
def baseEnd_1421780 : Nat := 243352174983184170970453

theorem tailTrace_1421780 : CollatzResearch.WordTrace tailWord_1421780 prefixEnd_1421780 243352174983184170970453 := by
  unfold tailWord_1421780
  simp only [CollatzResearch.WordTrace]
  refine ⟨25928288394570677768583397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34571051192760903691444529 25928288394570677768583397)
  ·
    refine ⟨4861554073982002081609387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25928288394570677768583397 4861554073982002081609387)
    ·
      refine ⟨7292331110973003122414081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861554073982002081609387 7292331110973003122414081)
      ·
        refine ⟨5469248333229752341810561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7292331110973003122414081 5469248333229752341810561)
        ·
          refine ⟨4101936249922314256357921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5469248333229752341810561 4101936249922314256357921)
          ·
            refine ⟨3076452187441735692268441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4101936249922314256357921 3076452187441735692268441)
            ·
              refine ⟨2307339140581301769201331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3076452187441735692268441 2307339140581301769201331)
              ·
                refine ⟨3461008710871952653801997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307339140581301769201331 3461008710871952653801997)
                ·
                  refine ⟨1297878266576982245175749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3461008710871952653801997 1297878266576982245175749)
                  ·
                    refine ⟨243352174983184170970453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1297878266576982245175749 243352174983184170970453)
                    ·
                      rfl

theorem cell23_1421780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1421780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421780 prefixEnd_1421780 := by exact prefixLift 1421780
  have htrace : WordTrace (prefixWord ++ tailWord_1421780) baseStart_1421780 baseEnd_1421780 := by
    simpa [prefixWord, tailWord_1421780, baseEnd_1421780] using wordTrace_append hprefix tailTrace_1421780
  have hstable : (prefixWord ++ tailWord_1421780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421780).length < 2 ^ (prefixWord ++ tailWord_1421780).sum := by decide
  have hdescent : baseEnd_1421780 < baseStart_1421780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421793 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 6]
def baseStart_1421793 : Nat := 118140960795 + 1421793 * 2 ^ 59
def prefixEnd_1421793 : Nat := 4983230072969 + 3 ^ 40 * 1421793 * 2
def baseEnd_1421793 : Nat := 81118133355340106894311

theorem tailTrace_1421793 : CollatzResearch.WordTrace tailWord_1421793 prefixEnd_1421793 81118133355340106894311 := by
  unfold tailWord_1421793
  simp only [CollatzResearch.WordTrace]
  refine ⟨51857050938094258757390033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34571367292062839171593355 51857050938094258757390033)
  ·
    refine ⟨38892788203570694068042525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51857050938094258757390033 38892788203570694068042525)
    ·
      refine ⟨14584795576339010275515947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38892788203570694068042525 14584795576339010275515947)
      ·
        refine ⟨21877193364508515413273921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14584795576339010275515947 21877193364508515413273921)
        ·
          refine ⟨16407895023381386559955441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21877193364508515413273921 16407895023381386559955441)
          ·
            refine ⟨12305921267536039919966581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16407895023381386559955441 12305921267536039919966581)
            ·
              refine ⟨1153680118831503742496867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12305921267536039919966581 1153680118831503742496867)
              ·
                refine ⟨1730520178247255613745301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153680118831503742496867 1730520178247255613745301)
                ·
                  refine ⟨81118133355340106894311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1730520178247255613745301 81118133355340106894311)
                  ·
                    rfl

theorem cell23_1421793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 6].length) (baseStart_1421793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421793 prefixEnd_1421793 := by exact prefixLift 1421793
  have htrace : WordTrace (prefixWord ++ tailWord_1421793) baseStart_1421793 baseEnd_1421793 := by
    simpa [prefixWord, tailWord_1421793, baseEnd_1421793] using wordTrace_append hprefix tailTrace_1421793
  have hstable : (prefixWord ++ tailWord_1421793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421793).length < 2 ^ (prefixWord ++ tailWord_1421793).sum := by decide
  have hdescent : baseEnd_1421793 < baseStart_1421793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421803 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 3]
def baseStart_1421803 : Nat := 118140960795 + 1421803 * 2 ^ 59
def prefixEnd_1421803 : Nat := 4983230072969 + 3 ^ 40 * 1421803 * 2
def baseEnd_1421803 : Nat := 730068335004605922923753

theorem tailTrace_1421803 : CollatzResearch.WordTrace tailWord_1421803 prefixEnd_1421803 730068335004605922923753 := by
  unfold tailWord_1421803
  simp only [CollatzResearch.WordTrace]
  refine ⟨51857415668058030465254063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34571610445372020310169375 51857415668058030465254063)
  ·
    refine ⟨77786123502087045697881095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51857415668058030465254063 77786123502087045697881095)
    ·
      refine ⟨116679185253130568546821643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77786123502087045697881095 116679185253130568546821643)
      ·
        refine ⟨175018777879695852820232465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116679185253130568546821643 175018777879695852820232465)
        ·
          refine ⟨131264083409771889615174349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175018777879695852820232465 131264083409771889615174349)
          ·
            refine ⟨49224031278664458605690381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131264083409771889615174349 49224031278664458605690381)
            ·
              refine ⟨18459011729499171977133893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49224031278664458605690381 18459011729499171977133893)
              ·
                refine ⟨3461064699281094745712605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18459011729499171977133893 3461064699281094745712605)
                ·
                  refine ⟨1297899262230410529642227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3461064699281094745712605 1297899262230410529642227)
                  ·
                    refine ⟨1946848893345615794463341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297899262230410529642227 1946848893345615794463341)
                    ·
                      refine ⟨730068335004605922923753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1946848893345615794463341 730068335004605922923753)
                      ·
                        rfl

theorem cell23_1421803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 3].length) (baseStart_1421803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421803 prefixEnd_1421803 := by exact prefixLift 1421803
  have htrace : WordTrace (prefixWord ++ tailWord_1421803) baseStart_1421803 baseEnd_1421803 := by
    simpa [prefixWord, tailWord_1421803, baseEnd_1421803] using wordTrace_append hprefix tailTrace_1421803
  have hstable : (prefixWord ++ tailWord_1421803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421803).length < 2 ^ (prefixWord ++ tailWord_1421803).sum := by decide
  have hdescent : baseEnd_1421803 < baseStart_1421803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421870 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1421870 : Nat := 118140960795 + 1421870 * 2 ^ 59
def prefixEnd_1421870 : Nat := 4983230072969 + 3 ^ 40 * 1421870 * 2
def baseEnd_1421870 : Nat := 243367579402819053595315

theorem tailTrace_1421870 : CollatzResearch.WordTrace tailWord_1421870 prefixEnd_1421870 243367579402819053595315 := by
  unfold tailWord_1421870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6482482419851912613492883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34573239572543533938628709 6482482419851912613492883)
  ·
    refine ⟨9723723629777868920239325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6482482419851912613492883 9723723629777868920239325)
    ·
      refine ⟨3646396361166700845089747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9723723629777868920239325 3646396361166700845089747)
      ·
        refine ⟨5469594541750051267634621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3646396361166700845089747 5469594541750051267634621)
        ·
          refine ⟨2051097953156269225362983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5469594541750051267634621 2051097953156269225362983)
          ·
            refine ⟨3076646929734403838044475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051097953156269225362983 3076646929734403838044475)
            ·
              refine ⟨4614970394601605757066713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076646929734403838044475 4614970394601605757066713)
              ·
                refine ⟨3461227795951204317800035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614970394601605757066713 3461227795951204317800035)
                ·
                  refine ⟨5191841693926806476700053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461227795951204317800035 5191841693926806476700053)
                  ·
                    refine ⟨243367579402819053595315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5191841693926806476700053 243367579402819053595315)
                    ·
                      rfl

theorem cell23_1421870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1421870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421870 prefixEnd_1421870 := by exact prefixLift 1421870
  have htrace : WordTrace (prefixWord ++ tailWord_1421870) baseStart_1421870 baseEnd_1421870 := by
    simpa [prefixWord, tailWord_1421870, baseEnd_1421870] using wordTrace_append hprefix tailTrace_1421870
  have hstable : (prefixWord ++ tailWord_1421870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421870).length < 2 ^ (prefixWord ++ tailWord_1421870).sum := by decide
  have hdescent : baseEnd_1421870 < baseStart_1421870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421920 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 3, 3, 2]
def baseStart_1421920 : Nat := 118140960795 + 1421920 * 2 ^ 59
def prefixEnd_1421920 : Nat := 4983230072969 + 3 ^ 40 * 1421920 * 2
def baseEnd_1421920 : Nat := 730128412241181965160715

theorem tailTrace_1421920 : CollatzResearch.WordTrace tailWord_1421920 prefixEnd_1421920 730128412241181965160715 := by
  unfold tailWord_1421920
  simp only [CollatzResearch.WordTrace]
  refine ⟨25930841504317079723631607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34574455339089439631508809 25930841504317079723631607)
  ·
    refine ⟨38896262256475619585447411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25930841504317079723631607 38896262256475619585447411)
    ·
      refine ⟨58344393384713429378171117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38896262256475619585447411 58344393384713429378171117)
      ·
        refine ⟨21879147519267536016814169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58344393384713429378171117 21879147519267536016814169)
        ·
          refine ⟨16409360639450652012610627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21879147519267536016814169 16409360639450652012610627)
          ·
            refine ⟨24614040959175978018915941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16409360639450652012610627 24614040959175978018915941)
            ·
              refine ⟨4615132679845495878546739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24614040959175978018915941 4615132679845495878546739)
              ·
                refine ⟨6922699019768243817820109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615132679845495878546739 6922699019768243817820109)
                ·
                  refine ⟨2596012132413091431682541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6922699019768243817820109 2596012132413091431682541)
                  ·
                    refine ⟨973504549654909286880953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596012132413091431682541 973504549654909286880953)
                    ·
                      refine ⟨730128412241181965160715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973504549654909286880953 730128412241181965160715)
                      ·
                        rfl

theorem cell23_1421920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_1421920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1421920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1421920 prefixEnd_1421920 := by exact prefixLift 1421920
  have htrace : WordTrace (prefixWord ++ tailWord_1421920) baseStart_1421920 baseEnd_1421920 := by
    simpa [prefixWord, tailWord_1421920, baseEnd_1421920] using wordTrace_append hprefix tailTrace_1421920
  have hstable : (prefixWord ++ tailWord_1421920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421920).length < 2 ^ (prefixWord ++ tailWord_1421920).sum := by decide
  have hdescent : baseEnd_1421920 < baseStart_1421920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422003 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 4, 5]
def baseStart_1422003 : Nat := 118140960795 + 1422003 * 2 ^ 59
def prefixEnd_1422003 : Nat := 4983230072969 + 3 ^ 40 * 1422003 * 2
def baseEnd_1422003 : Nat := 243390343711835046807611

theorem tailTrace_1422003 : CollatzResearch.WordTrace tailWord_1422003 prefixEnd_1422003 243390343711835046807611 := by
  unfold tailWord_1422003
  simp only [CollatzResearch.WordTrace]
  refine ⟨51864710267333464622534663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34576473511555643081689775 51864710267333464622534663)
  ·
    refine ⟨77797065401000196933801995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51864710267333464622534663 77797065401000196933801995)
    ·
      refine ⟨116695598101500295400702993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77797065401000196933801995 116695598101500295400702993)
      ·
        refine ⟨87521698576125221550527245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116695598101500295400702993 87521698576125221550527245)
        ·
          refine ⟨32820636966046958081447717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87521698576125221550527245 32820636966046958081447717)
          ·
            refine ⟨6153869431133804640271447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32820636966046958081447717 6153869431133804640271447)
            ·
              refine ⟨9230804146700706960407171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153869431133804640271447 9230804146700706960407171)
              ·
                refine ⟨13846206220051060440610757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9230804146700706960407171 13846206220051060440610757)
                ·
                  refine ⟨2596163666259573832614517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13846206220051060440610757 2596163666259573832614517)
                  ·
                    refine ⟨243390343711835046807611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2596163666259573832614517 243390343711835046807611)
                    ·
                      rfl

theorem cell23_1422003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 5].length) (baseStart_1422003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422003 prefixEnd_1422003 := by exact prefixLift 1422003
  have htrace : WordTrace (prefixWord ++ tailWord_1422003) baseStart_1422003 baseEnd_1422003 := by
    simpa [prefixWord, tailWord_1422003, baseEnd_1422003] using wordTrace_append hprefix tailTrace_1422003
  have hstable : (prefixWord ++ tailWord_1422003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422003).length < 2 ^ (prefixWord ++ tailWord_1422003).sum := by decide
  have hdescent : baseEnd_1422003 < baseStart_1422003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422007 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 7]
def baseStart_1422007 : Nat := 118140960795 + 1422007 * 2 ^ 59
def prefixEnd_1422007 : Nat := 4983230072969 + 3 ^ 40 * 1422007 * 2
def baseEnd_1422007 : Nat := 81130342784235902752535

theorem tailTrace_1422007 : CollatzResearch.WordTrace tailWord_1422007 prefixEnd_1422007 81130342784235902752535 := by
  unfold tailWord_1422007
  simp only [CollatzResearch.WordTrace]
  refine ⟨51864856159318973305680275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34576570772879315537120183 51864856159318973305680275)
  ·
    refine ⟨77797284238978459958520413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51864856159318973305680275 77797284238978459958520413)
    ·
      refine ⟨29173981589616922484445155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77797284238978459958520413 29173981589616922484445155)
      ·
        refine ⟨43760972384425383726667733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29173981589616922484445155 43760972384425383726667733)
        ·
          refine ⟨1025647790259969931093775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43760972384425383726667733 1025647790259969931093775)
          ·
            refine ⟨1538471685389954896640663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025647790259969931093775 1538471685389954896640663)
            ·
              refine ⟨2307707528084932344960995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538471685389954896640663 2307707528084932344960995)
              ·
                refine ⟨3461561292127398517441493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307707528084932344960995 3461561292127398517441493)
                ·
                  refine ⟨81130342784235902752535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3461561292127398517441493 81130342784235902752535)
                  ·
                    rfl

theorem cell23_1422007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 7].length) (baseStart_1422007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422007 prefixEnd_1422007 := by exact prefixLift 1422007
  have htrace : WordTrace (prefixWord ++ tailWord_1422007) baseStart_1422007 baseEnd_1422007 := by
    simpa [prefixWord, tailWord_1422007, baseEnd_1422007] using wordTrace_append hprefix tailTrace_1422007
  have hstable : (prefixWord ++ tailWord_1422007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422007).length < 2 ^ (prefixWord ++ tailWord_1422007).sum := by decide
  have hdescent : baseEnd_1422007 < baseStart_1422007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422010 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2]
def baseStart_1422010 : Nat := 118140960795 + 1422010 * 2 ^ 59
def prefixEnd_1422010 : Nat := 4983230072969 + 3 ^ 40 * 1422010 * 2
def baseEnd_1422010 : Nat := 730174625500086613035301

theorem tailTrace_1422010 : CollatzResearch.WordTrace tailWord_1422010 prefixEnd_1422010 730174625500086613035301 := by
  unfold tailWord_1422010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12966241394577026204509871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34576643718872069878692989 12966241394577026204509871)
  ·
    refine ⟨19449362091865539306764807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12966241394577026204509871 19449362091865539306764807)
    ·
      refine ⟨29174043137798308960147211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19449362091865539306764807 29174043137798308960147211)
      ·
        refine ⟨43761064706697463440220817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29174043137798308960147211 43761064706697463440220817)
        ·
          refine ⟨32820798530023097580165613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43761064706697463440220817 32820798530023097580165613)
          ·
            refine ⟨12307799448758661592562105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32820798530023097580165613 12307799448758661592562105)
            ·
              refine ⟨9230849586568996194421579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12307799448758661592562105 9230849586568996194421579)
              ·
                refine ⟨13846274379853494291632369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9230849586568996194421579 13846274379853494291632369)
                ·
                  refine ⟨10384705784890120718724277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13846274379853494291632369 10384705784890120718724277)
                  ·
                    refine ⟨973566167333448817380401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10384705784890120718724277 973566167333448817380401)
                    ·
                      refine ⟨730174625500086613035301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973566167333448817380401 730174625500086613035301)
                      ·
                        rfl

theorem cell23_1422010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_1422010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422010 prefixEnd_1422010 := by exact prefixLift 1422010
  have htrace : WordTrace (prefixWord ++ tailWord_1422010) baseStart_1422010 baseEnd_1422010 := by
    simpa [prefixWord, tailWord_1422010, baseEnd_1422010] using wordTrace_append hprefix tailTrace_1422010
  have hstable : (prefixWord ++ tailWord_1422010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422010).length < 2 ^ (prefixWord ++ tailWord_1422010).sum := by decide
  have hdescent : baseEnd_1422010 < baseStart_1422010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422013 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1422013 : Nat := 118140960795 + 1422013 * 2 ^ 59
def prefixEnd_1422013 : Nat := 4983230072969 + 3 ^ 40 * 1422013 * 2
def baseEnd_1422013 : Nat := 730176165942050101297787

theorem tailTrace_1422013 : CollatzResearch.WordTrace tailWord_1422013 prefixEnd_1422013 730176165942050101297787 := by
  unfold tailWord_1422013
  simp only [CollatzResearch.WordTrace]
  refine ⟨51865074997297236330398693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34576716664864824220265795 51865074997297236330398693)
  ·
    refine ⟨9724701561993231811949755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51865074997297236330398693 9724701561993231811949755)
    ·
      refine ⟨14587052342989847717924633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9724701561993231811949755 14587052342989847717924633)
      ·
        refine ⟨10940289257242385788443475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14587052342989847717924633 10940289257242385788443475)
        ·
          refine ⟨16410433885863578682665213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10940289257242385788443475 16410433885863578682665213)
          ·
            refine ⟨6153912707198842005999455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16410433885863578682665213 6153912707198842005999455)
            ·
              refine ⟨9230869060798263008999183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153912707198842005999455 9230869060798263008999183)
              ·
                refine ⟨13846303591197394513498775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9230869060798263008999183 13846303591197394513498775)
                ·
                  refine ⟨20769455386796091770248163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13846303591197394513498775 20769455386796091770248163)
                  ·
                    refine ⟨31154183080194137655372245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20769455386796091770248163 31154183080194137655372245)
                    ·
                      refine ⟨730176165942050101297787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31154183080194137655372245 730176165942050101297787)
                      ·
                        rfl

theorem cell23_1422013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1422013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422013 prefixEnd_1422013 := by exact prefixLift 1422013
  have htrace : WordTrace (prefixWord ++ tailWord_1422013) baseStart_1422013 baseEnd_1422013 := by
    simpa [prefixWord, tailWord_1422013, baseEnd_1422013] using wordTrace_append hprefix tailTrace_1422013
  have hstable : (prefixWord ++ tailWord_1422013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422013).length < 2 ^ (prefixWord ++ tailWord_1422013).sum := by decide
  have hdescent : baseEnd_1422013 < baseStart_1422013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422023 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1422023 : Nat := 118140960795 + 1422023 * 2 ^ 59
def prefixEnd_1422023 : Nat := 4983230072969 + 3 ^ 40 * 1422023 * 2
def baseEnd_1422023 : Nat := 730181300748595062172741

theorem tailTrace_1422023 : CollatzResearch.WordTrace tailWord_1422023 prefixEnd_1422023 730181300748595062172741 := by
  unfold tailWord_1422023
  simp only [CollatzResearch.WordTrace]
  refine ⟨51865439727261008038262723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34576959818174005358841815 51865439727261008038262723)
  ·
    refine ⟨77798159590891512057394085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51865439727261008038262723 77798159590891512057394085)
    ·
      refine ⟨14587154923292158510761391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77798159590891512057394085 14587154923292158510761391)
      ·
        refine ⟨21880732384938237766142087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14587154923292158510761391 21880732384938237766142087)
        ·
          refine ⟨32821098577407356649213131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21880732384938237766142087 32821098577407356649213131)
          ·
            refine ⟨49231647866111034973819697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32821098577407356649213131 49231647866111034973819697)
            ·
              refine ⟨36923735899583276230364773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49231647866111034973819697 36923735899583276230364773)
              ·
                refine ⟨6923200481171864293193395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36923735899583276230364773 6923200481171864293193395)
                ·
                  refine ⟨10384800721757796439790093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923200481171864293193395 10384800721757796439790093)
                  ·
                    refine ⟨3894300270659173664921285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10384800721757796439790093 3894300270659173664921285)
                    ·
                      refine ⟨730181300748595062172741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3894300270659173664921285 730181300748595062172741)
                      ·
                        rfl

theorem cell23_1422023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1422023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422023 prefixEnd_1422023 := by exact prefixLift 1422023
  have htrace : WordTrace (prefixWord ++ tailWord_1422023) baseStart_1422023 baseEnd_1422023 := by
    simpa [prefixWord, tailWord_1422023, baseEnd_1422023] using wordTrace_append hprefix tailTrace_1422023
  have hstable : (prefixWord ++ tailWord_1422023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422023).length < 2 ^ (prefixWord ++ tailWord_1422023).sum := by decide
  have hdescent : baseEnd_1422023 < baseStart_1422023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422040 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1422040 : Nat := 118140960795 + 1422040 * 2 ^ 59
def prefixEnd_1422040 : Nat := 4983230072969 + 3 ^ 40 * 1422040 * 2
def baseEnd_1422040 : Nat := 730190029919721495660163

theorem tailTrace_1422040 : CollatzResearch.WordTrace tailWord_1422040 prefixEnd_1422040 730190029919721495660163 := by
  unfold tailWord_1422040
  simp only [CollatzResearch.WordTrace]
  refine ⟨25933029884099709970815787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34577373178799613294421049 25933029884099709970815787)
  ·
    refine ⟨38899544826149564956223681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25933029884099709970815787 38899544826149564956223681)
    ·
      refine ⟨29174658619612173717167761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38899544826149564956223681 29174658619612173717167761)
      ·
        refine ⟨21880993964709130287875821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29174658619612173717167761 21880993964709130287875821)
        ·
          refine ⟨8205372736765923857953433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21880993964709130287875821 8205372736765923857953433)
          ·
            refine ⟨6154029552574442893465075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8205372736765923857953433 6154029552574442893465075)
            ·
              refine ⟨9231044328861664340197613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154029552574442893465075 9231044328861664340197613)
              ·
                refine ⟨3461641623323124127574105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9231044328861664340197613 3461641623323124127574105)
                ·
                  refine ⟨2596231217492343095680579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461641623323124127574105 2596231217492343095680579)
                  ·
                    refine ⟨3894346826238514643520869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2596231217492343095680579 3894346826238514643520869)
                    ·
                      refine ⟨730190029919721495660163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3894346826238514643520869 730190029919721495660163)
                      ·
                        rfl

theorem cell23_1422040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1422040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422040 prefixEnd_1422040 := by exact prefixLift 1422040
  have htrace : WordTrace (prefixWord ++ tailWord_1422040) baseStart_1422040 baseEnd_1422040 := by
    simpa [prefixWord, tailWord_1422040, baseEnd_1422040] using wordTrace_append hprefix tailTrace_1422040
  have hstable : (prefixWord ++ tailWord_1422040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422040).length < 2 ^ (prefixWord ++ tailWord_1422040).sum := by decide
  have hdescent : baseEnd_1422040 < baseStart_1422040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422117 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 4, 3, 2]
def baseStart_1422117 : Nat := 118140960795 + 1422117 * 2 ^ 59
def prefixEnd_1422117 : Nat := 4983230072969 + 3 ^ 40 * 1422117 * 2
def baseEnd_1422117 : Nat := 730229567930117694397309

theorem tailTrace_1422117 : CollatzResearch.WordTrace tailWord_1422117 prefixEnd_1422117 730229567930117694397309 := by
  unfold tailWord_1422117
  simp only [CollatzResearch.WordTrace]
  refine ⟨51868868188920462092184605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34579245459280308061456403 51868868188920462092184605)
  ·
    refine ⟨19450825570845173284569227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51868868188920462092184605 19450825570845173284569227)
    ·
      refine ⟨29176238356267759926853841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19450825570845173284569227 29176238356267759926853841)
      ·
        refine ⟨21882178767200819945140381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29176238356267759926853841 21882178767200819945140381)
        ·
          refine ⟨8205817037700307479427643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21882178767200819945140381 8205817037700307479427643)
          ·
            refine ⟨12308725556550461219141465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8205817037700307479427643 12308725556550461219141465)
            ·
              refine ⟨9231544167412845914356099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12308725556550461219141465 9231544167412845914356099)
              ·
                refine ⟨13847316251119268871534149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231544167412845914356099 13847316251119268871534149)
                ·
                  refine ⟨2596371797084862913412653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13847316251119268871534149 2596371797084862913412653)
                  ·
                    refine ⟨973639423906823592529745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596371797084862913412653 973639423906823592529745)
                    ·
                      refine ⟨730229567930117694397309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973639423906823592529745 730229567930117694397309)
                      ·
                        rfl

theorem cell23_1422117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_1422117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422117 prefixEnd_1422117 := by exact prefixLift 1422117
  have htrace : WordTrace (prefixWord ++ tailWord_1422117) baseStart_1422117 baseEnd_1422117 := by
    simpa [prefixWord, tailWord_1422117, baseEnd_1422117] using wordTrace_append hprefix tailTrace_1422117
  have hstable : (prefixWord ++ tailWord_1422117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422117).length < 2 ^ (prefixWord ++ tailWord_1422117).sum := by decide
  have hdescent : baseEnd_1422117 < baseStart_1422117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422123 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 5, 6]
def baseStart_1422123 : Nat := 118140960795 + 1422123 * 2 ^ 59
def prefixEnd_1422123 : Nat := 4983230072969 + 3 ^ 40 * 1422123 * 2
def baseEnd_1422123 : Nat := 243410882938014890307427

theorem tailTrace_1422123 : CollatzResearch.WordTrace tailWord_1422123 prefixEnd_1422123 243410882938014890307427 := by
  unfold tailWord_1422123
  simp only [CollatzResearch.WordTrace]
  refine ⟨51869087026898725116903023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34579391351265816744602015 51869087026898725116903023)
  ·
    refine ⟨77803630540348087675354535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51869087026898725116903023 77803630540348087675354535)
    ·
      refine ⟨116705445810522131513031803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77803630540348087675354535 116705445810522131513031803)
      ·
        refine ⟨175058168715783197269547705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116705445810522131513031803 175058168715783197269547705)
        ·
          refine ⟨131293626536837397952160779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175058168715783197269547705 131293626536837397952160779)
          ·
            refine ⟨196940439805256096928241169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131293626536837397952160779 196940439805256096928241169)
            ·
              refine ⟨147705329853942072696180877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196940439805256096928241169 147705329853942072696180877)
              ·
                refine ⟨55389498695228277261067829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147705329853942072696180877 55389498695228277261067829)
                ·
                  refine ⟨5192765502677650993225109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55389498695228277261067829 5192765502677650993225109)
                  ·
                    refine ⟨243410882938014890307427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5192765502677650993225109 243410882938014890307427)
                    ·
                      rfl

theorem cell23_1422123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_1422123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422123 prefixEnd_1422123 := by exact prefixLift 1422123
  have htrace : WordTrace (prefixWord ++ tailWord_1422123) baseStart_1422123 baseEnd_1422123 := by
    simpa [prefixWord, tailWord_1422123, baseEnd_1422123] using wordTrace_append hprefix tailTrace_1422123
  have hstable : (prefixWord ++ tailWord_1422123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422123).length < 2 ^ (prefixWord ++ tailWord_1422123).sum := by decide
  have hdescent : baseEnd_1422123 < baseStart_1422123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422124 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 1, 1, 3]
def baseStart_1422124 : Nat := 118140960795 + 1422124 * 2 ^ 59
def prefixEnd_1422124 : Nat := 4983230072969 + 3 ^ 40 * 1422124 * 2
def baseEnd_1422124 : Nat := 730233162294699167009777

theorem tailTrace_1422124 : CollatzResearch.WordTrace tailWord_1422124 prefixEnd_1422124 730233162294699167009777 := by
  unfold tailWord_1422124
  simp only [CollatzResearch.WordTrace]
  refine ⟨25934561749947551143844713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34579415666596734858459617 25934561749947551143844713)
  ·
    refine ⟨19450921312460663357883535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25934561749947551143844713 19450921312460663357883535)
    ·
      refine ⟨29176381968690995036825303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19450921312460663357883535 29176381968690995036825303)
      ·
        refine ⟨43764572953036492555237955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29176381968690995036825303 43764572953036492555237955)
        ·
          refine ⟨65646859429554738832856933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43764572953036492555237955 65646859429554738832856933)
          ·
            refine ⟨12308786143041513531160675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65646859429554738832856933 12308786143041513531160675)
            ·
              refine ⟨18463179214562270296741013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12308786143041513531160675 18463179214562270296741013)
              ·
                refine ⟨865461525682606420159735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18463179214562270296741013 865461525682606420159735)
                ·
                  refine ⟨1298192288523909630239603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865461525682606420159735 1298192288523909630239603)
                  ·
                    refine ⟨1947288432785864445359405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1298192288523909630239603 1947288432785864445359405)
                    ·
                      refine ⟨730233162294699167009777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1947288432785864445359405 730233162294699167009777)
                      ·
                        rfl

theorem cell23_1422124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_1422124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422124 prefixEnd_1422124 := by exact prefixLift 1422124
  have htrace : WordTrace (prefixWord ++ tailWord_1422124) baseStart_1422124 baseEnd_1422124 := by
    simpa [prefixWord, tailWord_1422124, baseEnd_1422124] using wordTrace_append hprefix tailTrace_1422124
  have hstable : (prefixWord ++ tailWord_1422124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422124).length < 2 ^ (prefixWord ++ tailWord_1422124).sum := by decide
  have hdescent : baseEnd_1422124 < baseStart_1422124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422147 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 4]
def baseStart_1422147 : Nat := 118140960795 + 1422147 * 2 ^ 59
def prefixEnd_1422147 : Nat := 4983230072969 + 3 ^ 40 * 1422147 * 2
def baseEnd_1422147 : Nat := 730244972349752577022171

theorem tailTrace_1422147 : CollatzResearch.WordTrace tailWord_1422147 prefixEnd_1422147 730244972349752577022171 := by
  unfold tailWord_1422147
  simp only [CollatzResearch.WordTrace]
  refine ⟨51869962378811777215776695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34579974919207851477184463 51869962378811777215776695)
  ·
    refine ⟨77804943568217665823665043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51869962378811777215776695 77804943568217665823665043)
    ·
      refine ⟨116707415352326498735497565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77804943568217665823665043 116707415352326498735497565)
      ·
        refine ⟨43765280757122437025811587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116707415352326498735497565 43765280757122437025811587)
        ·
          refine ⟨65647921135683655538717381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43765280757122437025811587 65647921135683655538717381)
          ·
            refine ⟨12308985212940685413509509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65647921135683655538717381 12308985212940685413509509)
            ·
              refine ⟨2307934727426378515033033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12308985212940685413509509 2307934727426378515033033)
              ·
                refine ⟨1730951045569783886274775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307934727426378515033033 1730951045569783886274775)
                ·
                  refine ⟨2596426568354675829412163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730951045569783886274775 2596426568354675829412163)
                  ·
                    refine ⟨3894639852532013744118245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2596426568354675829412163 3894639852532013744118245)
                    ·
                      refine ⟨730244972349752577022171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3894639852532013744118245 730244972349752577022171)
                      ·
                        rfl

theorem cell23_1422147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_1422147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422147 prefixEnd_1422147 := by exact prefixLift 1422147
  have htrace : WordTrace (prefixWord ++ tailWord_1422147) baseStart_1422147 baseEnd_1422147 := by
    simpa [prefixWord, tailWord_1422147, baseEnd_1422147] using wordTrace_append hprefix tailTrace_1422147
  have hstable : (prefixWord ++ tailWord_1422147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422147).length < 2 ^ (prefixWord ++ tailWord_1422147).sum := by decide
  have hdescent : baseEnd_1422147 < baseStart_1422147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422160 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_1422160 : Nat := 118140960795 + 1422160 * 2 ^ 59
def prefixEnd_1422160 : Nat := 4983230072969 + 3 ^ 40 * 1422160 * 2
def baseEnd_1422160 : Nat := 730251647598261026159611

theorem tailTrace_1422160 : CollatzResearch.WordTrace tailWord_1422160 prefixEnd_1422160 730251647598261026159611 := by
  unfold tailWord_1422160
  simp only [CollatzResearch.WordTrace]
  refine ⟨25935218263882340217999967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34580291018509786957333289 25935218263882340217999967)
  ·
    refine ⟨38902827395823510326999951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25935218263882340217999967 38902827395823510326999951)
    ·
      refine ⟨58354241093735265490499927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38902827395823510326999951 58354241093735265490499927)
      ·
        refine ⟨87531361640602898235749891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58354241093735265490499927 87531361640602898235749891)
        ·
          refine ⟨131297042460904347353624837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87531361640602898235749891 131297042460904347353624837)
          ·
            refine ⟨24618195461419565128804657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131297042460904347353624837 24618195461419565128804657)
            ·
              refine ⟨18463646596064673846603493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24618195461419565128804657 18463646596064673846603493)
              ·
                refine ⟨3461933736762126346238155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18463646596064673846603493 3461933736762126346238155)
                ·
                  refine ⟨5192900605143189519357233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461933736762126346238155 5192900605143189519357233)
                  ·
                    refine ⟨3894675453857392139517925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192900605143189519357233 3894675453857392139517925)
                    ·
                      refine ⟨730251647598261026159611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3894675453857392139517925 730251647598261026159611)
                      ·
                        rfl

theorem cell23_1422160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_1422160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422160 prefixEnd_1422160 := by exact prefixLift 1422160
  have htrace : WordTrace (prefixWord ++ tailWord_1422160) baseStart_1422160 baseEnd_1422160 := by
    simpa [prefixWord, tailWord_1422160, baseEnd_1422160] using wordTrace_append hprefix tailTrace_1422160
  have hstable : (prefixWord ++ tailWord_1422160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422160).length < 2 ^ (prefixWord ++ tailWord_1422160).sum := by decide
  have hdescent : baseEnd_1422160 < baseStart_1422160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422167 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_1422167 : Nat := 118140960795 + 1422167 * 2 ^ 59
def prefixEnd_1422167 : Nat := 4983230072969 + 3 ^ 40 * 1422167 * 2
def baseEnd_1422167 : Nat := 730255241962842498772079

theorem tailTrace_1422167 : CollatzResearch.WordTrace tailWord_1422167 prefixEnd_1422167 730255241962842498772079 := by
  unfold tailWord_1422167
  simp only [CollatzResearch.WordTrace]
  refine ⟨51870691838739320631504755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34580461225826213754336503 51870691838739320631504755)
  ·
    refine ⟨77806037758108980947257133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51870691838739320631504755 77806037758108980947257133)
    ·
      refine ⟨29177264159290867855221425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77806037758108980947257133 29177264159290867855221425)
      ·
        refine ⟨21882948119468150891416069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29177264159290867855221425 21882948119468150891416069)
        ·
          refine ⟨4103052772400278292140513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21882948119468150891416069 4103052772400278292140513)
          ·
            refine ⟨3077289579300208719105385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4103052772400278292140513 3077289579300208719105385)
            ·
              refine ⟨2307967184475156539329039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077289579300208719105385 2307967184475156539329039)
              ·
                refine ⟨3461950776712734808993559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307967184475156539329039 3461950776712734808993559)
                ·
                  refine ⟨5192926165069102213490339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461950776712734808993559 5192926165069102213490339)
                  ·
                    refine ⟨7789389247603653320235509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5192926165069102213490339 7789389247603653320235509)
                    ·
                      refine ⟨730255241962842498772079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7789389247603653320235509 730255241962842498772079)
                      ·
                        rfl

theorem cell23_1422167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_1422167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422167 prefixEnd_1422167 := by exact prefixLift 1422167
  have htrace : WordTrace (prefixWord ++ tailWord_1422167) baseStart_1422167 baseEnd_1422167 := by
    simpa [prefixWord, tailWord_1422167, baseEnd_1422167] using wordTrace_append hprefix tailTrace_1422167
  have hstable : (prefixWord ++ tailWord_1422167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422167).length < 2 ^ (prefixWord ++ tailWord_1422167).sum := by decide
  have hdescent : baseEnd_1422167 < baseStart_1422167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422170 : List Nat := [3, 1, 1, 2, 1, 6, 9]
def baseStart_1422170 : Nat := 118140960795 + 1422170 * 2 ^ 59
def prefixEnd_1422170 : Nat := 4983230072969 + 3 ^ 40 * 1422170 * 2
def baseEnd_1422170 : Nat := 9015515832158098605365

theorem tailTrace_1422170 : CollatzResearch.WordTrace tailWord_1422170 prefixEnd_1422170 9015515832158098605365 := by
  unfold tailWord_1422170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12967700314432113035965991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34580534171818968095909309 12967700314432113035965991)
  ·
    refine ⟨19451550471648169553948987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12967700314432113035965991 19451550471648169553948987)
    ·
      refine ⟨29177325707472254330923481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19451550471648169553948987 29177325707472254330923481)
      ·
        refine ⟨21882994280604190748192611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29177325707472254330923481 21882994280604190748192611)
        ·
          refine ⟨32824491420906286122288917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882994280604190748192611 32824491420906286122288917)
          ·
            refine ⟨1538648035354982161982293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32824491420906286122288917 1538648035354982161982293)
            ·
              refine ⟨9015515832158098605365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1538648035354982161982293 9015515832158098605365)
              ·
                rfl

theorem cell23_1422170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 9].length) (baseStart_1422170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422170 prefixEnd_1422170 := by exact prefixLift 1422170
  have htrace : WordTrace (prefixWord ++ tailWord_1422170) baseStart_1422170 baseEnd_1422170 := by
    simpa [prefixWord, tailWord_1422170, baseEnd_1422170] using wordTrace_append hprefix tailTrace_1422170
  have hstable : (prefixWord ++ tailWord_1422170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422170).length < 2 ^ (prefixWord ++ tailWord_1422170).sum := by decide
  have hdescent : baseEnd_1422170 < baseStart_1422170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422181 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 1, 2, 2]
def baseStart_1422181 : Nat := 118140960795 + 1422181 * 2 ^ 59
def prefixEnd_1422181 : Nat := 4983230072969 + 3 ^ 40 * 1422181 * 2
def baseEnd_1422181 : Nat := 730262430692005443997015

theorem tailTrace_1422181 : CollatzResearch.WordTrace tailWord_1422181 prefixEnd_1422181 730262430692005443997015 := by
  unfold tailWord_1422181
  simp only [CollatzResearch.WordTrace]
  refine ⟨51871202460688601022514397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34580801640459067348342931 51871202460688601022514397)
  ·
    refine ⟨19451700922758225383442899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51871202460688601022514397 19451700922758225383442899)
    ·
      refine ⟨29177551384137338075164349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19451700922758225383442899 29177551384137338075164349)
      ·
        refine ⟨10941581769051501778186631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29177551384137338075164349 10941581769051501778186631)
        ·
          refine ⟨16412372653577252667279947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941581769051501778186631 16412372653577252667279947)
          ·
            refine ⟨24618558980365879000919921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16412372653577252667279947 24618558980365879000919921)
            ·
              refine ⟨18463919235274409250689941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24618558980365879000919921 18463919235274409250689941)
              ·
                refine ⟨865496214153487933626091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18463919235274409250689941 865496214153487933626091)
                ·
                  refine ⟨1298244321230231900439137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865496214153487933626091 1298244321230231900439137)
                  ·
                    refine ⟨973683240922673925329353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1298244321230231900439137 973683240922673925329353)
                    ·
                      refine ⟨730262430692005443997015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973683240922673925329353 730262430692005443997015)
                      ·
                        rfl

theorem cell23_1422181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_1422181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422181 prefixEnd_1422181 := by exact prefixLift 1422181
  have htrace : WordTrace (prefixWord ++ tailWord_1422181) baseStart_1422181 baseEnd_1422181 := by
    simpa [prefixWord, tailWord_1422181, baseEnd_1422181] using wordTrace_append hprefix tailTrace_1422181
  have hstable : (prefixWord ++ tailWord_1422181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422181).length < 2 ^ (prefixWord ++ tailWord_1422181).sum := by decide
  have hdescent : baseEnd_1422181 < baseStart_1422181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422240 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1422240 : Nat := 118140960795 + 1422240 * 2 ^ 59
def prefixEnd_1422240 : Nat := 4983230072969 + 3 ^ 40 * 1422240 * 2
def baseEnd_1422240 : Nat := 730292726050620713159243

theorem tailTrace_1422240 : CollatzResearch.WordTrace tailWord_1422240 prefixEnd_1422240 730292726050620713159243 := by
  unfold tailWord_1422240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25936677183737427049456087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34582236244983236065941449 25936677183737427049456087)
  ·
    refine ⟨38905015775606140574184131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25936677183737427049456087 38905015775606140574184131)
    ·
      refine ⟨58357523663409210861276197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38905015775606140574184131 58357523663409210861276197)
      ·
        refine ⟨10942035686889227036489287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58357523663409210861276197 10942035686889227036489287)
        ·
          refine ⟨16413053530333840554733931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10942035686889227036489287 16413053530333840554733931)
          ·
            refine ⟨24619580295500760832100897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16413053530333840554733931 24619580295500760832100897)
            ·
              refine ⟨18464685221625570624075673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24619580295500760832100897 18464685221625570624075673)
              ·
                refine ⟨13848513916219177968056755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18464685221625570624075673 13848513916219177968056755)
                ·
                  refine ⟨20772770874328766952085133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13848513916219177968056755 20772770874328766952085133)
                  ·
                    refine ⟨7789789077873287607031925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20772770874328766952085133 7789789077873287607031925)
                    ·
                      refine ⟨730292726050620713159243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7789789077873287607031925 730292726050620713159243)
                      ·
                        rfl

theorem cell23_1422240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1422240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422240 prefixEnd_1422240 := by exact prefixLift 1422240
  have htrace : WordTrace (prefixWord ++ tailWord_1422240) baseStart_1422240 baseEnd_1422240 := by
    simpa [prefixWord, tailWord_1422240, baseEnd_1422240] using wordTrace_append hprefix tailTrace_1422240
  have hstable : (prefixWord ++ tailWord_1422240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422240).length < 2 ^ (prefixWord ++ tailWord_1422240).sum := by decide
  have hdescent : baseEnd_1422240 < baseStart_1422240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422287 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_1422287 : Nat := 118140960795 + 1422287 * 2 ^ 59
def prefixEnd_1422287 : Nat := 4983230072969 + 3 ^ 40 * 1422287 * 2
def baseEnd_1422287 : Nat := 730316859641382029271527

theorem tailTrace_1422287 : CollatzResearch.WordTrace tailWord_1422287 prefixEnd_1422287 730316859641382029271527 := by
  unfold tailWord_1422287
  simp only [CollatzResearch.WordTrace]
  refine ⟨51875068598304581125873115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34583379065536387417248743 51875068598304581125873115)
  ·
    refine ⟨77812602897456871688809673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51875068598304581125873115 77812602897456871688809673)
    ·
      refine ⟨58359452173092653766607255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77812602897456871688809673 58359452173092653766607255)
      ·
        refine ⟨87539178259638980649910883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58359452173092653766607255 87539178259638980649910883)
        ·
          refine ⟨131308767389458470974866325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87539178259638980649910883 131308767389458470974866325)
          ·
            refine ⟨6155098471380865826946859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131308767389458470974866325 6155098471380865826946859)
            ·
              refine ⟨9232647707071298740420289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155098471380865826946859 9232647707071298740420289)
              ·
                refine ⟨6924485780303474055315217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232647707071298740420289 6924485780303474055315217)
                ·
                  refine ⟨5193364335227605541486413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924485780303474055315217 5193364335227605541486413)
                  ·
                    refine ⟨1947511625710352078057405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5193364335227605541486413 1947511625710352078057405)
                    ·
                      refine ⟨730316859641382029271527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1947511625710352078057405 730316859641382029271527)
                      ·
                        rfl

theorem cell23_1422287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_1422287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422287 prefixEnd_1422287 := by exact prefixLift 1422287
  have htrace : WordTrace (prefixWord ++ tailWord_1422287) baseStart_1422287 baseEnd_1422287 := by
    simpa [prefixWord, tailWord_1422287, baseEnd_1422287] using wordTrace_append hprefix tailTrace_1422287
  have hstable : (prefixWord ++ tailWord_1422287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422287).length < 2 ^ (prefixWord ++ tailWord_1422287).sum := by decide
  have hdescent : baseEnd_1422287 < baseStart_1422287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422294 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1422294 : Nat := 118140960795 + 1422294 * 2 ^ 59
def prefixEnd_1422294 : Nat := 4983230072969 + 3 ^ 40 * 1422294 * 2
def baseEnd_1422294 : Nat := 81146717111773722431555

theorem tailTrace_1422294 : CollatzResearch.WordTrace tailWord_1422294 prefixEnd_1422294 81146717111773722431555 := by
  unfold tailWord_1422294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242207744329951332586121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34583549272852814214251957 3242207744329951332586121)
  ·
    refine ⟨2431655808247463499439591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3242207744329951332586121 2431655808247463499439591)
    ·
      refine ⟨3647483712371195249159387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431655808247463499439591 3647483712371195249159387)
      ·
        refine ⟨5471225568556792873739081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647483712371195249159387 5471225568556792873739081)
        ·
          refine ⟨4103419176417594655304311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5471225568556792873739081 4103419176417594655304311)
          ·
            refine ⟨6155128764626391982956467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103419176417594655304311 6155128764626391982956467)
            ·
              refine ⟨9232693146939587974434701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155128764626391982956467 9232693146939587974434701)
              ·
                refine ⟨3462259930102345490413013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9232693146939587974434701 3462259930102345490413013)
                ·
                  refine ⟨81146717111773722431555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3462259930102345490413013 81146717111773722431555)
                  ·
                    rfl

theorem cell23_1422294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1422294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422294 prefixEnd_1422294 := by exact prefixLift 1422294
  have htrace : WordTrace (prefixWord ++ tailWord_1422294) baseStart_1422294 baseEnd_1422294 := by
    simpa [prefixWord, tailWord_1422294, baseEnd_1422294] using wordTrace_append hprefix tailTrace_1422294
  have hstable : (prefixWord ++ tailWord_1422294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422294).length < 2 ^ (prefixWord ++ tailWord_1422294).sum := by decide
  have hdescent : baseEnd_1422294 < baseStart_1422294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422320 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_1422320 : Nat := 118140960795 + 1422320 * 2 ^ 59
def prefixEnd_1422320 : Nat := 4983230072969 + 3 ^ 40 * 1422320 * 2
def baseEnd_1422320 : Nat := 243444601500993466719625

theorem tailTrace_1422320 : CollatzResearch.WordTrace tailWord_1422320 prefixEnd_1422320 243444601500993466719625 := by
  unfold tailWord_1422320
  simp only [CollatzResearch.WordTrace]
  refine ⟨25938136103592513880912207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34584181471456685174549609 25938136103592513880912207)
  ·
    refine ⟨38907204155388770821368311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25938136103592513880912207 38907204155388770821368311)
    ·
      refine ⟨58360806233083156232052467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38907204155388770821368311 58360806233083156232052467)
      ·
        refine ⟨87541209349624734348078701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58360806233083156232052467 87541209349624734348078701)
        ·
          refine ⟨32827953506109275380529513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87541209349624734348078701 32827953506109275380529513)
          ·
            refine ⟨24620965129581956535397135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32827953506109275380529513 24620965129581956535397135)
            ·
              refine ⟨36931447694372934803095703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24620965129581956535397135 36931447694372934803095703)
              ·
                refine ⟨55397171541559402204643555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36931447694372934803095703 55397171541559402204643555)
                ·
                  refine ⟨83095757312339103306965333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55397171541559402204643555 83095757312339103306965333)
                  ·
                    refine ⟨243444601500993466719625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 83095757312339103306965333 243444601500993466719625)
                    ·
                      rfl

theorem cell23_1422320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_1422320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422320 prefixEnd_1422320 := by exact prefixLift 1422320
  have htrace : WordTrace (prefixWord ++ tailWord_1422320) baseStart_1422320 baseEnd_1422320 := by
    simpa [prefixWord, tailWord_1422320, baseEnd_1422320] using wordTrace_append hprefix tailTrace_1422320
  have hstable : (prefixWord ++ tailWord_1422320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422320).length < 2 ^ (prefixWord ++ tailWord_1422320).sum := by decide
  have hdescent : baseEnd_1422320 < baseStart_1422320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422344 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1422344 : Nat := 118140960795 + 1422344 * 2 ^ 59
def prefixEnd_1422344 : Nat := 4983230072969 + 3 ^ 40 * 1422344 * 2
def baseEnd_1422344 : Nat := 730346128038688306258765

theorem tailTrace_1422344 : CollatzResearch.WordTrace tailWord_1422344 prefixEnd_1422344 730346128038688306258765 := by
  unfold tailWord_1422344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25938573779549039930349043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34584765039398719907132057 25938573779549039930349043)
  ·
    refine ⟨38907860669323559895523565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25938573779549039930349043 38907860669323559895523565)
    ·
      refine ⟨14590447750996334960821337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38907860669323559895523565 14590447750996334960821337)
      ·
        refine ⟨10942835813247251220616003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14590447750996334960821337 10942835813247251220616003)
        ·
          refine ⟨16414253719870876830924005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10942835813247251220616003 16414253719870876830924005)
          ·
            refine ⟨3077672572475789405798251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16414253719870876830924005 3077672572475789405798251)
            ·
              refine ⟨4616508858713684108697377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3077672572475789405798251 4616508858713684108697377)
              ·
                refine ⟨3462381644035263081523033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4616508858713684108697377 3462381644035263081523033)
                ·
                  refine ⟨2596786233026447311142275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462381644035263081523033 2596786233026447311142275)
                  ·
                    refine ⟨3895179349539670966713413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2596786233026447311142275 3895179349539670966713413)
                    ·
                      refine ⟨730346128038688306258765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3895179349539670966713413 730346128038688306258765)
                      ·
                        rfl

theorem cell23_1422344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1422344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422344 prefixEnd_1422344 := by exact prefixLift 1422344
  have htrace : WordTrace (prefixWord ++ tailWord_1422344) baseStart_1422344 baseEnd_1422344 := by
    simpa [prefixWord, tailWord_1422344, baseEnd_1422344] using wordTrace_append hprefix tailTrace_1422344
  have hstable : (prefixWord ++ tailWord_1422344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422344).length < 2 ^ (prefixWord ++ tailWord_1422344).sum := by decide
  have hdescent : baseEnd_1422344 < baseStart_1422344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422401 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 6]
def baseStart_1422401 : Nat := 118140960795 + 1422401 * 2 ^ 59
def prefixEnd_1422401 : Nat := 4983230072969 + 3 ^ 40 * 1422401 * 2
def baseEnd_1422401 : Nat := 81152821826221620360667

theorem tailTrace_1422401 : CollatzResearch.WordTrace tailWord_1422401 prefixEnd_1422401 81152821826221620360667 := by
  unfold tailWord_1422401
  simp only [CollatzResearch.WordTrace]
  refine ⟨51879226519891578595523057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34586151013261052397015371 51879226519891578595523057)
  ·
    refine ⟨38909419889918683946642293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51879226519891578595523057 38909419889918683946642293)
    ·
      refine ⟨3647758114679876619997715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38909419889918683946642293 3647758114679876619997715)
      ·
        refine ⟨5471637172019814929996573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647758114679876619997715 5471637172019814929996573)
        ·
          refine ⟨2051863939507430598748715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5471637172019814929996573 2051863939507430598748715)
          ·
            refine ⟨3077795909261145898123073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051863939507430598748715 3077795909261145898123073)
            ·
              refine ⟨2308346931945859423592305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077795909261145898123073 2308346931945859423592305)
              ·
                refine ⟨1731260198959394567694229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2308346931945859423592305 1731260198959394567694229)
                ·
                  refine ⟨81152821826221620360667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1731260198959394567694229 81152821826221620360667)
                  ·
                    rfl

theorem cell23_1422401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 6].length) (baseStart_1422401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422401 prefixEnd_1422401 := by exact prefixLift 1422401
  have htrace : WordTrace (prefixWord ++ tailWord_1422401) baseStart_1422401 baseEnd_1422401 := by
    simpa [prefixWord, tailWord_1422401, baseEnd_1422401] using wordTrace_append hprefix tailTrace_1422401
  have hstable : (prefixWord ++ tailWord_1422401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422401).length < 2 ^ (prefixWord ++ tailWord_1422401).sum := by decide
  have hdescent : baseEnd_1422401 < baseStart_1422401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422444 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_1422444 : Nat := 118140960795 + 1422444 * 2 ^ 59
def prefixEnd_1422444 : Nat := 4983230072969 + 3 ^ 40 * 1422444 * 2
def baseEnd_1422444 : Nat := 243465825368045971669435

theorem tailTrace_1422444 : CollatzResearch.WordTrace tailWord_1422444 prefixEnd_1422444 243465825368045971669435 := by
  unfold tailWord_1422444
  simp only [CollatzResearch.WordTrace]
  refine ⟨25940397429367898469669193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34587196572490531292892257 25940397429367898469669193)
  ·
    refine ⟨19455298072025923852251895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25940397429367898469669193 19455298072025923852251895)
    ·
      refine ⟨29182947108038885778377843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19455298072025923852251895 29182947108038885778377843)
      ·
        refine ⟨43774420662058328667566765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29182947108038885778377843 43774420662058328667566765)
        ·
          refine ⟨16415407748271873250337537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43774420662058328667566765 16415407748271873250337537)
          ·
            refine ⟨12311555811203904937753153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16415407748271873250337537 12311555811203904937753153)
            ·
              refine ⟨9233666858402928703314865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12311555811203904937753153 9233666858402928703314865)
              ·
                refine ⟨6925250143802196527486149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9233666858402928703314865 6925250143802196527486149)
                ·
                  refine ⟨1298484401962911848903653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6925250143802196527486149 1298484401962911848903653)
                  ·
                    refine ⟨243465825368045971669435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298484401962911848903653 243465825368045971669435)
                    ·
                      rfl

theorem cell23_1422444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_1422444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422444 prefixEnd_1422444 := by exact prefixLift 1422444
  have htrace : WordTrace (prefixWord ++ tailWord_1422444) baseStart_1422444 baseEnd_1422444 := by
    simpa [prefixWord, tailWord_1422444, baseEnd_1422444] using wordTrace_append hprefix tailTrace_1422444
  have hstable : (prefixWord ++ tailWord_1422444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422444).length < 2 ^ (prefixWord ++ tailWord_1422444).sum := by decide
  have hdescent : baseEnd_1422444 < baseStart_1422444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422445 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_1422445 : Nat := 118140960795 + 1422445 * 2 ^ 59
def prefixEnd_1422445 : Nat := 4983230072969 + 3 ^ 40 * 1422445 * 2
def baseEnd_1422445 : Nat := 730397989584792411095801

theorem tailTrace_1422445 : CollatzResearch.WordTrace tailWord_1422445 prefixEnd_1422445 730397989584792411095801 := by
  unfold tailWord_1422445
  simp only [CollatzResearch.WordTrace]
  refine ⟨51880831331732174110124789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34587220887821449406749859 51880831331732174110124789)
  ·
    refine ⟨4863827937349891322824199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51880831331732174110124789 4863827937349891322824199)
    ·
      refine ⟨7295741906024836984236299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863827937349891322824199 7295741906024836984236299)
      ·
        refine ⟨10943612859037255476354449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295741906024836984236299 10943612859037255476354449)
        ·
          refine ⟨8207709644277941607265837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10943612859037255476354449 8207709644277941607265837)
          ·
            refine ⟨3077891116604228102724689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8207709644277941607265837 3077891116604228102724689)
            ·
              refine ⟨2308418337453171077043517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077891116604228102724689 2308418337453171077043517)
              ·
                refine ⟨865656876544939153891319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308418337453171077043517 865656876544939153891319)
                ·
                  refine ⟨1298485314817408730836979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865656876544939153891319 1298485314817408730836979)
                  ·
                    refine ⟨1947727972226113096255469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1298485314817408730836979 1947727972226113096255469)
                    ·
                      refine ⟨730397989584792411095801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1947727972226113096255469 730397989584792411095801)
                      ·
                        rfl

theorem cell23_1422445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_1422445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422445 prefixEnd_1422445 := by exact prefixLift 1422445
  have htrace : WordTrace (prefixWord ++ tailWord_1422445) baseStart_1422445 baseEnd_1422445 := by
    simpa [prefixWord, tailWord_1422445, baseEnd_1422445] using wordTrace_append hprefix tailTrace_1422445
  have hstable : (prefixWord ++ tailWord_1422445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422445).length < 2 ^ (prefixWord ++ tailWord_1422445).sum := by decide
  have hdescent : baseEnd_1422445 < baseStart_1422445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422468 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_1422468 : Nat := 118140960795 + 1422468 * 2 ^ 59
def prefixEnd_1422468 : Nat := 4983230072969 + 3 ^ 40 * 1422468 * 2
def baseEnd_1422468 : Nat := 730409799639845821108195

theorem tailTrace_1422468 : CollatzResearch.WordTrace tailWord_1422468 prefixEnd_1422468 730409799639845821108195 := by
  unfold tailWord_1422468
  simp only [CollatzResearch.WordTrace]
  refine ⟨25940835105324424519106029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34587780140432566025474705 25940835105324424519106029)
  ·
    refine ⟨9727813164496659194664761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25940835105324424519106029 9727813164496659194664761)
    ·
      refine ⟨7295859873372494395998571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9727813164496659194664761 7295859873372494395998571)
      ·
        refine ⟨10943789810058741593997857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295859873372494395998571 10943789810058741593997857)
        ·
          refine ⟨8207842357544056195498393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10943789810058741593997857 8207842357544056195498393)
          ·
            refine ⟨6155881768158042146623795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8207842357544056195498393 6155881768158042146623795)
            ·
              refine ⟨9233822652237063219935693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155881768158042146623795 9233822652237063219935693)
              ·
                refine ⟨3462683494588898707475885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9233822652237063219935693 3462683494588898707475885)
                ·
                  refine ⟨1298506310470837015303457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3462683494588898707475885 1298506310470837015303457)
                  ·
                    refine ⟨973879732853127761477593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1298506310470837015303457 973879732853127761477593)
                    ·
                      refine ⟨730409799639845821108195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973879732853127761477593 730409799639845821108195)
                      ·
                        rfl

theorem cell23_1422468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_1422468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422468 prefixEnd_1422468 := by exact prefixLift 1422468
  have htrace : WordTrace (prefixWord ++ tailWord_1422468) baseStart_1422468 baseEnd_1422468 := by
    simpa [prefixWord, tailWord_1422468, baseEnd_1422468] using wordTrace_append hprefix tailTrace_1422468
  have hstable : (prefixWord ++ tailWord_1422468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422468).length < 2 ^ (prefixWord ++ tailWord_1422468).sum := by decide
  have hdescent : baseEnd_1422468 < baseStart_1422468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422488 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1422488 : Nat := 118140960795 + 1422488 * 2 ^ 59
def prefixEnd_1422488 : Nat := 4983230072969 + 3 ^ 40 * 1422488 * 2
def baseEnd_1422488 : Nat := 730420069252935742858103

theorem tailTrace_1422488 : CollatzResearch.WordTrace tailWord_1422488 prefixEnd_1422488 730420069252935742858103 := by
  unfold tailWord_1422488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25941199835288196226970059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34588266447050928302626745 25941199835288196226970059)
  ·
    refine ⟨38911799752932294340455089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25941199835288196226970059 38911799752932294340455089)
    ·
      refine ⟨29183849814699220755341317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38911799752932294340455089 29183849814699220755341317)
      ·
        refine ⟨5471971840256103891626497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29183849814699220755341317 5471971840256103891626497)
        ·
          refine ⟨4103978880192077918719873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5471971840256103891626497 4103978880192077918719873)
          ·
            refine ⟨3077984160144058439039905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4103978880192077918719873 3077984160144058439039905)
            ·
              refine ⟨2308488120108043829279929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077984160144058439039905 2308488120108043829279929)
              ·
                refine ⟨1731366090081032871959947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2308488120108043829279929 1731366090081032871959947)
                ·
                  refine ⟨2597049135121549307939921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731366090081032871959947 2597049135121549307939921)
                  ·
                    refine ⟨1947786851341161980954941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2597049135121549307939921 1947786851341161980954941)
                    ·
                      refine ⟨730420069252935742858103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1947786851341161980954941 730420069252935742858103)
                      ·
                        rfl

theorem cell23_1422488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1422488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422488 prefixEnd_1422488 := by exact prefixLift 1422488
  have htrace : WordTrace (prefixWord ++ tailWord_1422488) baseStart_1422488 baseEnd_1422488 := by
    simpa [prefixWord, tailWord_1422488, baseEnd_1422488] using wordTrace_append hprefix tailTrace_1422488
  have hstable : (prefixWord ++ tailWord_1422488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422488).length < 2 ^ (prefixWord ++ tailWord_1422488).sum := by decide
  have hdescent : baseEnd_1422488 < baseStart_1422488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422501 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_1422501 : Nat := 118140960795 + 1422501 * 2 ^ 59
def prefixEnd_1422501 : Nat := 4983230072969 + 3 ^ 40 * 1422501 * 2
def baseEnd_1422501 : Nat := 730426744501444191995543

theorem tailTrace_1422501 : CollatzResearch.WordTrace tailWord_1422501 prefixEnd_1422501 730426744501444191995543 := by
  unfold tailWord_1422501
  simp only [CollatzResearch.WordTrace]
  refine ⟨51882873819529295674163357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34588582546352863782775571 51882873819529295674163357)
  ·
    refine ⟨19456077682323485877811259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51882873819529295674163357 19456077682323485877811259)
    ·
      refine ⟨29184116523485228816716889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19456077682323485877811259 29184116523485228816716889)
      ·
        refine ⟨21888087392613921612537667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29184116523485228816716889 21888087392613921612537667)
        ·
          refine ⟨32832131088920882418806501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21888087392613921612537667 32832131088920882418806501)
          ·
            refine ⟨6156024579172665453526219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32832131088920882418806501 6156024579172665453526219)
            ·
              refine ⟨9234036868758998180289329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156024579172665453526219 9234036868758998180289329)
              ·
                refine ⟨6925527651569248635216997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9234036868758998180289329 6925527651569248635216997)
                ·
                  refine ⟨1298536434669234119103187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6925527651569248635216997 1298536434669234119103187)
                  ·
                    refine ⟨1947804652003851178654781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1298536434669234119103187 1947804652003851178654781)
                    ·
                      refine ⟨730426744501444191995543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1947804652003851178654781 730426744501444191995543)
                      ·
                        rfl

theorem cell23_1422501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_1422501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422501 prefixEnd_1422501 := by exact prefixLift 1422501
  have htrace : WordTrace (prefixWord ++ tailWord_1422501) baseStart_1422501 baseEnd_1422501 := by
    simpa [prefixWord, tailWord_1422501, baseEnd_1422501] using wordTrace_append hprefix tailTrace_1422501
  have hstable : (prefixWord ++ tailWord_1422501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422501).length < 2 ^ (prefixWord ++ tailWord_1422501).sum := by decide
  have hdescent : baseEnd_1422501 < baseStart_1422501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422554 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1422554 : Nat := 118140960795 + 1422554 * 2 ^ 59
def prefixEnd_1422554 : Nat := 4983230072969 + 3 ^ 40 * 1422554 * 2
def baseEnd_1422554 : Nat := 730453958976132484632799

theorem tailTrace_1422554 : CollatzResearch.WordTrace tailWord_1422554 prefixEnd_1422554 730453958976132484632799 := by
  unfold tailWord_1422554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12971201722084321431460679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34589871258891523817228477 12971201722084321431460679)
  ·
    refine ⟨19456802583126482147191019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12971201722084321431460679 19456802583126482147191019)
    ·
      refine ⟨29185203874689723220786529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19456802583126482147191019 29185203874689723220786529)
      ·
        refine ⟨21888902906017292415589897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29185203874689723220786529 21888902906017292415589897)
        ·
          refine ⟨16416677179512969311692423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21888902906017292415589897 16416677179512969311692423)
          ·
            refine ⟨24625015769269453967538635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16416677179512969311692423 24625015769269453967538635)
            ·
              refine ⟨36937523653904180951307953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24625015769269453967538635 36937523653904180951307953)
              ·
                refine ⟨27703142740428135713480965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36937523653904180951307953 27703142740428135713480965)
                ·
                  refine ⟨5194339263830275446277681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27703142740428135713480965 5194339263830275446277681)
                  ·
                    refine ⟨3895754447872706584708261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5194339263830275446277681 3895754447872706584708261)
                    ·
                      refine ⟨730453958976132484632799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3895754447872706584708261 730453958976132484632799)
                      ·
                        rfl

theorem cell23_1422554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1422554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422554 prefixEnd_1422554 := by exact prefixLift 1422554
  have htrace : WordTrace (prefixWord ++ tailWord_1422554) baseStart_1422554 baseEnd_1422554 := by
    simpa [prefixWord, tailWord_1422554, baseEnd_1422554] using wordTrace_append hprefix tailTrace_1422554
  have hstable : (prefixWord ++ tailWord_1422554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422554).length < 2 ^ (prefixWord ++ tailWord_1422554).sum := by decide
  have hdescent : baseEnd_1422554 < baseStart_1422554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422574 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1422574 : Nat := 118140960795 + 1422574 * 2 ^ 59
def prefixEnd_1422574 : Nat := 4983230072969 + 3 ^ 40 * 1422574 * 2
def baseEnd_1422574 : Nat := 730464228589222406382707

theorem tailTrace_1422574 : CollatzResearch.WordTrace tailWord_1422574 prefixEnd_1422574 730464228589222406382707 := by
  unfold tailWord_1422574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6485692043533103642696347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34590357565509886094380517 6485692043533103642696347)
  ·
    refine ⟨9728538065299655464044521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6485692043533103642696347 9728538065299655464044521)
    ·
      refine ⟨7296403548974741598033391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9728538065299655464044521 7296403548974741598033391)
      ·
        refine ⟨10944605323462112397050087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7296403548974741598033391 10944605323462112397050087)
        ·
          refine ⟨16416907985193168595575131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10944605323462112397050087 16416907985193168595575131)
          ·
            refine ⟨24625361977789752893362697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16416907985193168595575131 24625361977789752893362697)
            ·
              refine ⟨18469021483342314670022023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24625361977789752893362697 18469021483342314670022023)
              ·
                refine ⟨27703532225013472005033035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18469021483342314670022023 27703532225013472005033035)
                ·
                  refine ⟨41555298337520208007549553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27703532225013472005033035 41555298337520208007549553)
                  ·
                    refine ⟨31166473753140156005662165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41555298337520208007549553 31166473753140156005662165)
                    ·
                      refine ⟨730464228589222406382707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31166473753140156005662165 730464228589222406382707)
                      ·
                        rfl

theorem cell23_1422574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1422574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422574 prefixEnd_1422574 := by exact prefixLift 1422574
  have htrace : WordTrace (prefixWord ++ tailWord_1422574) baseStart_1422574 baseEnd_1422574 := by
    simpa [prefixWord, tailWord_1422574, baseEnd_1422574] using wordTrace_append hprefix tailTrace_1422574
  have hstable : (prefixWord ++ tailWord_1422574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422574).length < 2 ^ (prefixWord ++ tailWord_1422574).sum := by decide
  have hdescent : baseEnd_1422574 < baseStart_1422574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422591 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_1422591 : Nat := 118140960795 + 1422591 * 2 ^ 59
def prefixEnd_1422591 : Nat := 4983230072969 + 3 ^ 40 * 1422591 * 2
def baseEnd_1422591 : Nat := 730472957760348839870129

theorem tailTrace_1422591 : CollatzResearch.WordTrace tailWord_1422591 prefixEnd_1422591 730472957760348839870129 := by
  unfold tailWord_1422591
  simp only [CollatzResearch.WordTrace]
  refine ⟨51886156389203241044939627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34590770926135494029959751 51886156389203241044939627)
  ·
    refine ⟨77829234583804861567409441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51886156389203241044939627 77829234583804861567409441)
    ·
      refine ⟨58371925937853646175557081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77829234583804861567409441 58371925937853646175557081)
      ·
        refine ⟨43778944453390234631667811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58371925937853646175557081 43778944453390234631667811)
        ·
          refine ⟨65668416680085351947501717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43778944453390234631667811 65668416680085351947501717)
          ·
            refine ⟨3078207031879000872539143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65668416680085351947501717 3078207031879000872539143)
            ·
              refine ⟨4617310547818501308808715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078207031879000872539143 4617310547818501308808715)
              ·
                refine ⟨6925965821727751963213073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617310547818501308808715 6925965821727751963213073)
                ·
                  refine ⟨5194474366295813972409805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6925965821727751963213073 5194474366295813972409805)
                  ·
                    refine ⟨1947927887360930239653677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5194474366295813972409805 1947927887360930239653677)
                    ·
                      refine ⟨730472957760348839870129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1947927887360930239653677 730472957760348839870129)
                      ·
                        rfl

theorem cell23_1422591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_1422591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422591 prefixEnd_1422591 := by exact prefixLift 1422591
  have htrace : WordTrace (prefixWord ++ tailWord_1422591) baseStart_1422591 baseEnd_1422591 := by
    simpa [prefixWord, tailWord_1422591, baseEnd_1422591] using wordTrace_append hprefix tailTrace_1422591
  have hstable : (prefixWord ++ tailWord_1422591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422591).length < 2 ^ (prefixWord ++ tailWord_1422591).sum := by decide
  have hdescent : baseEnd_1422591 < baseStart_1422591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422601 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 2, 5, 2]
def baseStart_1422601 : Nat := 118140960795 + 1422601 * 2 ^ 59
def prefixEnd_1422601 : Nat := 4983230072969 + 3 ^ 40 * 1422601 * 2
def baseEnd_1422601 : Nat := 730478092566893800745083

theorem tailTrace_1422601 : CollatzResearch.WordTrace tailWord_1422601 prefixEnd_1422601 730478092566893800745083 := by
  unfold tailWord_1422601
  simp only [CollatzResearch.WordTrace]
  refine ⟨51886521119167012752803657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34591014079444675168535771 51886521119167012752803657)
  ·
    refine ⟨38914890839375259564602743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51886521119167012752803657 38914890839375259564602743)
    ·
      refine ⟨58372336259062889346904115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38914890839375259564602743 58372336259062889346904115)
      ·
        refine ⟨87558504388594334020356173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58372336259062889346904115 87558504388594334020356173)
        ·
          refine ⟨32834439145722875257633565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87558504388594334020356173 32834439145722875257633565)
          ·
            refine ⟨12312914679646078221612587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32834439145722875257633565 12312914679646078221612587)
            ·
              refine ⟨18469372019469117332418881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12312914679646078221612587 18469372019469117332418881)
              ·
                refine ⟨13852029014601837999314161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18469372019469117332418881 13852029014601837999314161)
                ·
                  refine ⟨10389021760951378499485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13852029014601837999314161 10389021760951378499485621)
                  ·
                    refine ⟨973970790089191734326777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10389021760951378499485621 973970790089191734326777)
                    ·
                      refine ⟨730478092566893800745083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 973970790089191734326777 730478092566893800745083)
                      ·
                        rfl

theorem cell23_1422601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 5, 2].length) (baseStart_1422601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422601 prefixEnd_1422601 := by exact prefixLift 1422601
  have htrace : WordTrace (prefixWord ++ tailWord_1422601) baseStart_1422601 baseEnd_1422601 := by
    simpa [prefixWord, tailWord_1422601, baseEnd_1422601] using wordTrace_append hprefix tailTrace_1422601
  have hstable : (prefixWord ++ tailWord_1422601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422601).length < 2 ^ (prefixWord ++ tailWord_1422601).sum := by decide
  have hdescent : baseEnd_1422601 < baseStart_1422601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422692 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_1422692 : Nat := 118140960795 + 1422692 * 2 ^ 59
def prefixEnd_1422692 : Nat := 4983230072969 + 3 ^ 40 * 1422692 * 2
def baseEnd_1422692 : Nat := 243508273102150981569055

theorem tailTrace_1422692 : CollatzResearch.WordTrace tailWord_1422692 prefixEnd_1422692 243508273102150981569055 := by
  unfold tailWord_1422692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25944920080918667647183165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34593226774558223529577553 25944920080918667647183165)
  ·
    refine ⟨9729345030344500367693687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25944920080918667647183165 9729345030344500367693687)
    ·
      refine ⟨14594017545516750551540531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9729345030344500367693687 14594017545516750551540531)
      ·
        refine ⟨21891026318275125827310797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14594017545516750551540531 21891026318275125827310797)
        ·
          refine ⟨8209134869353172185241549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21891026318275125827310797 8209134869353172185241549)
          ·
            refine ⟨3078425576007439569465581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8209134869353172185241549 3078425576007439569465581)
            ·
              refine ⟨1154409591002789838549593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3078425576007439569465581 1154409591002789838549593)
              ·
                refine ⟨865807193252092378912195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154409591002789838549593 865807193252092378912195)
                ·
                  refine ⟨1298710789878138568368293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865807193252092378912195 1298710789878138568368293)
                  ·
                    refine ⟨243508273102150981569055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298710789878138568368293 243508273102150981569055)
                    ·
                      rfl

theorem cell23_1422692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_1422692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422692 prefixEnd_1422692 := by exact prefixLift 1422692
  have htrace : WordTrace (prefixWord ++ tailWord_1422692) baseStart_1422692 baseEnd_1422692 := by
    simpa [prefixWord, tailWord_1422692, baseEnd_1422692] using wordTrace_append hprefix tailTrace_1422692
  have hstable : (prefixWord ++ tailWord_1422692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422692).length < 2 ^ (prefixWord ++ tailWord_1422692).sum := by decide
  have hdescent : baseEnd_1422692 < baseStart_1422692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422731 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 1, 6]
def baseStart_1422731 : Nat := 118140960795 + 1422731 * 2 ^ 59
def prefixEnd_1422731 : Nat := 4983230072969 + 3 ^ 40 * 1422731 * 2
def baseEnd_1422731 : Nat := 243514948350659430706495

theorem tailTrace_1422731 : CollatzResearch.WordTrace tailWord_1422731 prefixEnd_1422731 243514948350659430706495 := by
  unfold tailWord_1422731
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891262608696044955036047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34594175072464029970024031 51891262608696044955036047)
  ·
    refine ⟨77836893913044067432554071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51891262608696044955036047 77836893913044067432554071)
    ·
      refine ⟨116755340869566101148831107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77836893913044067432554071 116755340869566101148831107)
      ·
        refine ⟨175133011304349151723246661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116755340869566101148831107 175133011304349151723246661)
        ·
          refine ⟨32837439619565465948108749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175133011304349151723246661 32837439619565465948108749)
          ·
            refine ⟨12314039857337049730540781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32837439619565465948108749 12314039857337049730540781)
            ·
              refine ⟨4617764946501393648952793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12314039857337049730540781 4617764946501393648952793)
              ·
                refine ⟨3463323709876045236714595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617764946501393648952793 3463323709876045236714595)
                ·
                  refine ⟨5194985564814067855071893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463323709876045236714595 5194985564814067855071893)
                  ·
                    refine ⟨243514948350659430706495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5194985564814067855071893 243514948350659430706495)
                    ·
                      rfl

theorem cell23_1422731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 6].length) (baseStart_1422731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422731 prefixEnd_1422731 := by exact prefixLift 1422731
  have htrace : WordTrace (prefixWord ++ tailWord_1422731) baseStart_1422731 baseEnd_1422731 := by
    simpa [prefixWord, tailWord_1422731, baseEnd_1422731] using wordTrace_append hprefix tailTrace_1422731
  have hstable : (prefixWord ++ tailWord_1422731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422731).length < 2 ^ (prefixWord ++ tailWord_1422731).sum := by decide
  have hdescent : baseEnd_1422731 < baseStart_1422731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422749 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_1422749 : Nat := 118140960795 + 1422749 * 2 ^ 59
def prefixEnd_1422749 : Nat := 4983230072969 + 3 ^ 40 * 1422749 * 2
def baseEnd_1422749 : Nat := 730554087703759221694403

theorem tailTrace_1422749 : CollatzResearch.WordTrace tailWord_1422749 prefixEnd_1422749 730554087703759221694403 := by
  unfold tailWord_1422749
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891919122630834029191301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34594612748420556019460867 51891919122630834029191301)
  ·
    refine ⟨9729734835493281380473369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51891919122630834029191301 9729734835493281380473369)
    ·
      refine ⟨7297301126619961035355027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9729734835493281380473369 7297301126619961035355027)
      ·
        refine ⟨10945951689929941553032541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297301126619961035355027 10945951689929941553032541)
        ·
          refine ⟨4104731883723728082387203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10945951689929941553032541 4104731883723728082387203)
          ·
            refine ⟨6157097825585592123580805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104731883723728082387203 6157097825585592123580805)
            ·
              refine ⟨1154455842297298523171401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6157097825585592123580805 1154455842297298523171401)
              ·
                refine ⟨865841881722973892378551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154455842297298523171401 865841881722973892378551)
                ·
                  refine ⟨1298762822584460838567827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865841881722973892378551 1298762822584460838567827)
                  ·
                    refine ⟨1948144233876691257851741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1298762822584460838567827 1948144233876691257851741)
                    ·
                      refine ⟨730554087703759221694403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1948144233876691257851741 730554087703759221694403)
                      ·
                        rfl

theorem cell23_1422749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_1422749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422749 prefixEnd_1422749 := by exact prefixLift 1422749
  have htrace : WordTrace (prefixWord ++ tailWord_1422749) baseStart_1422749 baseEnd_1422749 := by
    simpa [prefixWord, tailWord_1422749, baseEnd_1422749] using wordTrace_append hprefix tailTrace_1422749
  have hstable : (prefixWord ++ tailWord_1422749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422749).length < 2 ^ (prefixWord ++ tailWord_1422749).sum := by decide
  have hdescent : baseEnd_1422749 < baseStart_1422749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422755 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 3, 2, 2]
def baseStart_1422755 : Nat := 118140960795 + 1422755 * 2 ^ 59
def prefixEnd_1422755 : Nat := 4983230072969 + 3 ^ 40 * 1422755 * 2
def baseEnd_1422755 : Nat := 730557168587686198219375

theorem tailTrace_1422755 : CollatzResearch.WordTrace tailWord_1422755 prefixEnd_1422755 730557168587686198219375 := by
  unfold tailWord_1422755
  simp only [CollatzResearch.WordTrace]
  refine ⟨51892137960609097053909719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34594758640406064702606479 51892137960609097053909719)
  ·
    refine ⟨77838206940913645580864579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51892137960609097053909719 77838206940913645580864579)
    ·
      refine ⟨116757310411370468371296869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77838206940913645580864579 116757310411370468371296869)
      ·
        refine ⟨21891995702131962819618163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116757310411370468371296869 21891995702131962819618163)
        ·
          refine ⟨32837993553197944229427245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21891995702131962819618163 32837993553197944229427245)
          ·
            refine ⟨12314247582449229086035217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32837993553197944229427245 12314247582449229086035217)
            ·
              refine ⟨9235685686836921814526413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12314247582449229086035217 9235685686836921814526413)
              ·
                refine ⟨3463382132563845680447405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9235685686836921814526413 3463382132563845680447405)
                ·
                  refine ⟨1298768299711442130167777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3463382132563845680447405 1298768299711442130167777)
                  ·
                    refine ⟨974076224783581597625833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1298768299711442130167777 974076224783581597625833)
                    ·
                      refine ⟨730557168587686198219375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974076224783581597625833 730557168587686198219375)
                      ·
                        rfl

theorem cell23_1422755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_1422755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422755 prefixEnd_1422755 := by exact prefixLift 1422755
  have htrace : WordTrace (prefixWord ++ tailWord_1422755) baseStart_1422755 baseEnd_1422755 := by
    simpa [prefixWord, tailWord_1422755, baseEnd_1422755] using wordTrace_append hprefix tailTrace_1422755
  have hstable : (prefixWord ++ tailWord_1422755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422755).length < 2 ^ (prefixWord ++ tailWord_1422755).sum := by decide
  have hdescent : baseEnd_1422755 < baseStart_1422755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422765 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1422765 : Nat := 118140960795 + 1422765 * 2 ^ 59
def prefixEnd_1422765 : Nat := 4983230072969 + 3 ^ 40 * 1422765 * 2
def baseEnd_1422765 : Nat := 243520767798077053031443

theorem tailTrace_1422765 : CollatzResearch.WordTrace tailWord_1422765 prefixEnd_1422765 243520767798077053031443 := by
  unfold tailWord_1422765
  simp only [CollatzResearch.WordTrace]
  refine ⟨51892502690572868761773749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34595001793715245841182499 51892502690572868761773749)
  ·
    refine ⟨4864922127241206446416289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51892502690572868761773749 4864922127241206446416289)
    ·
      refine ⟨3648691595430904834812217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4864922127241206446416289 3648691595430904834812217)
      ·
        refine ⟨2736518696573178626109163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3648691595430904834812217 2736518696573178626109163)
        ·
          refine ⟨4104778044859767939163745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736518696573178626109163 4104778044859767939163745)
          ·
            refine ⟨3078583533644825954372809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4104778044859767939163745 3078583533644825954372809)
            ·
              refine ⟨2308937650233619465779607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3078583533644825954372809 2308937650233619465779607)
              ·
                refine ⟨3463406475350429198669411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308937650233619465779607 3463406475350429198669411)
                ·
                  refine ⟨5195109713025643798004117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463406475350429198669411 5195109713025643798004117)
                  ·
                    refine ⟨243520767798077053031443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5195109713025643798004117 243520767798077053031443)
                    ·
                      rfl

theorem cell23_1422765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1422765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422765 prefixEnd_1422765 := by exact prefixLift 1422765
  have htrace : WordTrace (prefixWord ++ tailWord_1422765) baseStart_1422765 baseEnd_1422765 := by
    simpa [prefixWord, tailWord_1422765, baseEnd_1422765] using wordTrace_append hprefix tailTrace_1422765
  have hstable : (prefixWord ++ tailWord_1422765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422765).length < 2 ^ (prefixWord ++ tailWord_1422765).sum := by decide
  have hdescent : baseEnd_1422765 < baseStart_1422765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422786 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1422786 : Nat := 118140960795 + 1422786 * 2 ^ 59
def prefixEnd_1422786 : Nat := 4983230072969 + 3 ^ 40 * 1422786 * 2
def baseEnd_1422786 : Nat := 243524362162658525643911

theorem tailTrace_1422786 : CollatzResearch.WordTrace tailWord_1422786 prefixEnd_1422786 243524362162658525643911 := by
  unfold tailWord_1422786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12973317155874197337072053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34595512415664526232192141 12973317155874197337072053)
  ·
    refine ⟨1216248483363206000350505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12973317155874197337072053 1216248483363206000350505)
    ·
      refine ⟨912186362522404500262879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1216248483363206000350505 912186362522404500262879)
      ·
        refine ⟨1368279543783606750394319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912186362522404500262879 1368279543783606750394319)
        ·
          refine ⟨2052419315675410125591479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368279543783606750394319 2052419315675410125591479)
          ·
            refine ⟨3078628973513115188387219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052419315675410125591479 3078628973513115188387219)
            ·
              refine ⟨4617943460269672782580829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078628973513115188387219 4617943460269672782580829)
              ·
                refine ⟨1731728797601127293467811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4617943460269672782580829 1731728797601127293467811)
                ·
                  refine ⟨2597593196401690940201717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731728797601127293467811 2597593196401690940201717)
                  ·
                    refine ⟨243524362162658525643911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2597593196401690940201717 243524362162658525643911)
                    ·
                      rfl

theorem cell23_1422786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1422786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422786 prefixEnd_1422786 := by exact prefixLift 1422786
  have htrace : WordTrace (prefixWord ++ tailWord_1422786) baseStart_1422786 baseEnd_1422786 := by
    simpa [prefixWord, tailWord_1422786, baseEnd_1422786] using wordTrace_append hprefix tailTrace_1422786
  have hstable : (prefixWord ++ tailWord_1422786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422786).length < 2 ^ (prefixWord ++ tailWord_1422786).sum := by decide
  have hdescent : baseEnd_1422786 < baseStart_1422786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422805 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1422805 : Nat := 118140960795 + 1422805 * 2 ^ 59
def prefixEnd_1422805 : Nat := 4983230072969 + 3 ^ 40 * 1422805 * 2
def baseEnd_1422805 : Nat := 730582842620411002594145

theorem tailTrace_1422805 : CollatzResearch.WordTrace tailWord_1422805 prefixEnd_1422805 730582842620411002594145 := by
  unfold tailWord_1422805
  simp only [CollatzResearch.WordTrace]
  refine ⟨51893961610427955593229869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34595974406951970395486579 51893961610427955593229869)
  ·
    refine ⟨19460235603910483347461201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51893961610427955593229869 19460235603910483347461201)
    ·
      refine ⟨14595176702932862510595901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19460235603910483347461201 14595176702932862510595901)
      ·
        refine ⟨5473191263599823441473463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14595176702932862510595901 5473191263599823441473463)
        ·
          refine ⟨8209786895399735162210195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473191263599823441473463 8209786895399735162210195)
          ·
            refine ⟨12314680343099602743315293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209786895399735162210195 12314680343099602743315293)
            ·
              refine ⟨4618005128662351028743235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12314680343099602743315293 4618005128662351028743235)
              ·
                refine ⟨6927007692993526543114853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618005128662351028743235 6927007692993526543114853)
                ·
                  refine ⟨1298813942436286226834035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6927007692993526543114853 1298813942436286226834035)
                  ·
                    refine ⟨1948220913654429340251053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1298813942436286226834035 1948220913654429340251053)
                    ·
                      refine ⟨730582842620411002594145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1948220913654429340251053 730582842620411002594145)
                      ·
                        rfl

theorem cell23_1422805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1422805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422805 prefixEnd_1422805 := by exact prefixLift 1422805
  have htrace : WordTrace (prefixWord ++ tailWord_1422805) baseStart_1422805 baseEnd_1422805 := by
    simpa [prefixWord, tailWord_1422805, baseEnd_1422805] using wordTrace_append hprefix tailTrace_1422805
  have hstable : (prefixWord ++ tailWord_1422805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422805).length < 2 ^ (prefixWord ++ tailWord_1422805).sum := by decide
  have hdescent : baseEnd_1422805 < baseStart_1422805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422806 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1422806 : Nat := 118140960795 + 1422806 * 2 ^ 59
def prefixEnd_1422806 : Nat := 4983230072969 + 3 ^ 40 * 1422806 * 2
def baseEnd_1422806 : Nat := 730583356101065498681641

theorem tailTrace_1422806 : CollatzResearch.WordTrace tailWord_1422806 prefixEnd_1422806 730583356101065498681641 := by
  unfold tailWord_1422806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243374880214020797751017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34595998722282888509344181 3243374880214020797751017)
  ·
    refine ⟨2432531160160515598313263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3243374880214020797751017 2432531160160515598313263)
    ·
      refine ⟨3648796740240773397469895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2432531160160515598313263 3648796740240773397469895)
      ·
        refine ⟨5473195110361160096204843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648796740240773397469895 5473195110361160096204843)
        ·
          refine ⟨8209792665541740144307265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473195110361160096204843 8209792665541740144307265)
          ·
            refine ⟨6157344499156305108230449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209792665541740144307265 6157344499156305108230449)
            ·
              refine ⟨4618008374367228831172837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157344499156305108230449 4618008374367228831172837)
              ·
                refine ⟨865876570193855405844907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4618008374367228831172837 865876570193855405844907)
                ·
                  refine ⟨1298814855290783108767361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865876570193855405844907 1298814855290783108767361)
                  ·
                    refine ⟨974111141468087331575521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1298814855290783108767361 974111141468087331575521)
                    ·
                      refine ⟨730583356101065498681641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974111141468087331575521 730583356101065498681641)
                      ·
                        rfl

theorem cell23_1422806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1422806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422806 prefixEnd_1422806 := by exact prefixLift 1422806
  have htrace : WordTrace (prefixWord ++ tailWord_1422806) baseStart_1422806 baseEnd_1422806 := by
    simpa [prefixWord, tailWord_1422806, baseEnd_1422806] using wordTrace_append hprefix tailTrace_1422806
  have hstable : (prefixWord ++ tailWord_1422806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422806).length < 2 ^ (prefixWord ++ tailWord_1422806).sum := by decide
  have hdescent : baseEnd_1422806 < baseStart_1422806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422832 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 1, 3, 2]
def baseStart_1422832 : Nat := 118140960795 + 1422832 * 2 ^ 59
def prefixEnd_1422832 : Nat := 4983230072969 + 3 ^ 40 * 1422832 * 2
def baseEnd_1422832 : Nat := 730596706598082396956521

theorem tailTrace_1422832 : CollatzResearch.WordTrace tailWord_1422832 prefixEnd_1422832 730596706598082396956521 := by
  unfold tailWord_1422832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25947473190665069602231375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34596630920886759469641833 25947473190665069602231375)
  ·
    refine ⟨38921209785997604403347063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25947473190665069602231375 38921209785997604403347063)
    ·
      refine ⟨58381814678996406605020595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38921209785997604403347063 58381814678996406605020595)
      ·
        refine ⟨87572722018494609907530893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58381814678996406605020595 87572722018494609907530893)
        ·
          refine ⟨32839770756935478715324085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87572722018494609907530893 32839770756935478715324085)
          ·
            refine ⟨3078728508462701129561633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32839770756935478715324085 3078728508462701129561633)
            ·
              refine ⟨2309046381347025847171225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3078728508462701129561633 2309046381347025847171225)
              ·
                refine ⟨1731784786010269385378419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309046381347025847171225 1731784786010269385378419)
                ·
                  refine ⟨2597677179015404078067629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731784786010269385378419 2597677179015404078067629)
                  ·
                    refine ⟨974128942130776529275361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2597677179015404078067629 974128942130776529275361)
                    ·
                      refine ⟨730596706598082396956521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974128942130776529275361 730596706598082396956521)
                      ·
                        rfl

theorem cell23_1422832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 3, 2].length) (baseStart_1422832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422832 prefixEnd_1422832 := by exact prefixLift 1422832
  have htrace : WordTrace (prefixWord ++ tailWord_1422832) baseStart_1422832 baseEnd_1422832 := by
    simpa [prefixWord, tailWord_1422832, baseEnd_1422832] using wordTrace_append hprefix tailTrace_1422832
  have hstable : (prefixWord ++ tailWord_1422832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422832).length < 2 ^ (prefixWord ++ tailWord_1422832).sum := by decide
  have hdescent : baseEnd_1422832 < baseStart_1422832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422879 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 2, 2, 2]
def baseStart_1422879 : Nat := 118140960795 + 1422879 * 2 ^ 59
def prefixEnd_1422879 : Nat := 4983230072969 + 3 ^ 40 * 1422879 * 2
def baseEnd_1422879 : Nat := 730620840188843713068805

theorem tailTrace_1422879 : CollatzResearch.WordTrace tailWord_1422879 prefixEnd_1422879 730620840188843713068805 := by
  unfold tailWord_1422879
  simp only [CollatzResearch.WordTrace]
  refine ⟨51896660612159866231423691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34597773741439910820949127 51896660612159866231423691)
  ·
    refine ⟨77844990918239799347135537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51896660612159866231423691 77844990918239799347135537)
    ·
      refine ⟨58383743188679849510351653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77844990918239799347135537 58383743188679849510351653)
      ·
        refine ⟨10946951847877471783190935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58383743188679849510351653 10946951847877471783190935)
        ·
          refine ⟨16420427771816207674786403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10946951847877471783190935 16420427771816207674786403)
          ·
            refine ⟨24630641657724311512179605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16420427771816207674786403 24630641657724311512179605)
            ·
              refine ⟨1154561327705827102133419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24630641657724311512179605 1154561327705827102133419)
              ·
                refine ⟨1731841991558740653200129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154561327705827102133419 1731841991558740653200129)
                ·
                  refine ⟨1298881493669055489900097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1731841991558740653200129 1298881493669055489900097)
                  ·
                    refine ⟨974161120251791617425073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1298881493669055489900097 974161120251791617425073)
                    ·
                      refine ⟨730620840188843713068805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974161120251791617425073 730620840188843713068805)
                      ·
                        rfl

theorem cell23_1422879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_1422879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422879 prefixEnd_1422879 := by exact prefixLift 1422879
  have htrace : WordTrace (prefixWord ++ tailWord_1422879) baseStart_1422879 baseEnd_1422879 := by
    simpa [prefixWord, tailWord_1422879, baseEnd_1422879] using wordTrace_append hprefix tailTrace_1422879
  have hstable : (prefixWord ++ tailWord_1422879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422879).length < 2 ^ (prefixWord ++ tailWord_1422879).sum := by decide
  have hdescent : baseEnd_1422879 < baseStart_1422879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422919 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 5]
def baseStart_1422919 : Nat := 118140960795 + 1422919 * 2 ^ 59
def prefixEnd_1422919 : Nat := 4983230072969 + 3 ^ 40 * 1422919 * 2
def baseEnd_1422919 : Nat := 81182375490558172952069

theorem tailTrace_1422919 : CollatzResearch.WordTrace tailWord_1422919 prefixEnd_1422919 81182375490558172952069 := by
  unfold tailWord_1422919
  simp only [CollatzResearch.WordTrace]
  refine ⟨51898119532014953062879811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34598746354676635375253207 51898119532014953062879811)
  ·
    refine ⟨77847179298022429594319717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51898119532014953062879811 77847179298022429594319717)
    ·
      refine ⟨14596346118379205548934947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77847179298022429594319717 14596346118379205548934947)
      ·
        refine ⟨21894519177568808323402421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14596346118379205548934947 21894519177568808323402421)
        ·
          refine ⟨2052611172897075780318977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21894519177568808323402421 2052611172897075780318977)
          ·
            refine ⟨1539458379672806835239233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052611172897075780318977 1539458379672806835239233)
            ·
              refine ⟨1154593784754605126429425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539458379672806835239233 1154593784754605126429425)
              ·
                refine ⟨865945338565953844822069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154593784754605126429425 865945338565953844822069)
                ·
                  refine ⟨81182375490558172952069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 865945338565953844822069 81182375490558172952069)
                  ·
                    rfl

theorem cell23_1422919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 5].length) (baseStart_1422919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422919 prefixEnd_1422919 := by exact prefixLift 1422919
  have htrace : WordTrace (prefixWord ++ tailWord_1422919) baseStart_1422919 baseEnd_1422919 := by
    simpa [prefixWord, tailWord_1422919, baseEnd_1422919] using wordTrace_append hprefix tailTrace_1422919
  have hstable : (prefixWord ++ tailWord_1422919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422919).length < 2 ^ (prefixWord ++ tailWord_1422919).sum := by decide
  have hdescent : baseEnd_1422919 < baseStart_1422919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422935 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 6, 2]
def baseStart_1422935 : Nat := 118140960795 + 1422935 * 2 ^ 59
def prefixEnd_1422935 : Nat := 4983230072969 + 3 ^ 40 * 1422935 * 2
def baseEnd_1422935 : Nat := 730649595105495493968547

theorem tailTrace_1422935 : CollatzResearch.WordTrace tailWord_1422935 prefixEnd_1422935 730649595105495493968547 := by
  unfold tailWord_1422935
  simp only [CollatzResearch.WordTrace]
  refine ⟨51898703099956987795462259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34599135399971325196974839 51898703099956987795462259)
  ·
    refine ⟨77848054649935481693193389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51898703099956987795462259 77848054649935481693193389)
    ·
      refine ⟨29193020493725805634947521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77848054649935481693193389 29193020493725805634947521)
      ·
        refine ⟨21894765370294354226210641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29193020493725805634947521 21894765370294354226210641)
        ·
          refine ⟨16421074027720765669657981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21894765370294354226210641 16421074027720765669657981)
          ·
            refine ⟨6157902760395287126121743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16421074027720765669657981 6157902760395287126121743)
            ·
              refine ⟨9236854140592930689182615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157902760395287126121743 9236854140592930689182615)
              ·
                refine ⟨13855281210889396033773923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9236854140592930689182615 13855281210889396033773923)
                ·
                  refine ⟨20782921816334094050660885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13855281210889396033773923 20782921816334094050660885)
                  ·
                    refine ⟨974199460140660658624729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20782921816334094050660885 974199460140660658624729)
                    ·
                      refine ⟨730649595105495493968547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974199460140660658624729 730649595105495493968547)
                      ·
                        rfl

theorem cell23_1422935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_1422935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422935 prefixEnd_1422935 := by exact prefixLift 1422935
  have htrace : WordTrace (prefixWord ++ tailWord_1422935) baseStart_1422935 baseEnd_1422935 := by
    simpa [prefixWord, tailWord_1422935, baseEnd_1422935] using wordTrace_append hprefix tailTrace_1422935
  have hstable : (prefixWord ++ tailWord_1422935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422935).length < 2 ^ (prefixWord ++ tailWord_1422935).sum := by decide
  have hdescent : baseEnd_1422935 < baseStart_1422935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422945 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 3, 4]
def baseStart_1422945 : Nat := 118140960795 + 1422945 * 2 ^ 59
def prefixEnd_1422945 : Nat := 4983230072969 + 3 ^ 40 * 1422945 * 2
def baseEnd_1422945 : Nat := 243551576637346818281167

theorem tailTrace_1422945 : CollatzResearch.WordTrace tailWord_1422945 prefixEnd_1422945 243551576637346818281167 := by
  unfold tailWord_1422945
  simp only [CollatzResearch.WordTrace]
  refine ⟨51899067829920759503326289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34599378553280506335550859 51899067829920759503326289)
  ·
    refine ⟨38924300872440569627494717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51899067829920759503326289 38924300872440569627494717)
    ·
      refine ⟨14596612827165213610310519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38924300872440569627494717 14596612827165213610310519)
      ·
        refine ⟨21894919240747820415465779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14596612827165213610310519 21894919240747820415465779)
        ·
          refine ⟨32842378861121730623198669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21894919240747820415465779 32842378861121730623198669)
          ·
            refine ⟨12315892072920648983699501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32842378861121730623198669 12315892072920648983699501)
            ·
              refine ⟨4618459527345243368887313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12315892072920648983699501 4618459527345243368887313)
              ·
                refine ⟨3463844645508932526665485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4618459527345243368887313 3463844645508932526665485)
                ·
                  refine ⟨1298941742065849697499557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3463844645508932526665485 1298941742065849697499557)
                  ·
                    refine ⟨243551576637346818281167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298941742065849697499557 243551576637346818281167)
                    ·
                      rfl

theorem cell23_1422945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_1422945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422945 prefixEnd_1422945 := by exact prefixLift 1422945
  have htrace : WordTrace (prefixWord ++ tailWord_1422945) baseStart_1422945 baseEnd_1422945 := by
    simpa [prefixWord, tailWord_1422945, baseEnd_1422945] using wordTrace_append hprefix tailTrace_1422945
  have hstable : (prefixWord ++ tailWord_1422945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422945).length < 2 ^ (prefixWord ++ tailWord_1422945).sum := by decide
  have hdescent : baseEnd_1422945 < baseStart_1422945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422952 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1422952 : Nat := 118140960795 + 1422952 * 2 ^ 59
def prefixEnd_1422952 : Nat := 4983230072969 + 3 ^ 40 * 1422952 * 2
def baseEnd_1422952 : Nat := 730658324276621927455969

theorem tailTrace_1422952 : CollatzResearch.WordTrace tailWord_1422952 prefixEnd_1422952 730658324276621927455969 := by
  unfold tailWord_1422952
  simp only [CollatzResearch.WordTrace]
  refine ⟨25949661570447699849415555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34599548760596933132554073 25949661570447699849415555)
  ·
    refine ⟨38924492355671549774123333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25949661570447699849415555 38924492355671549774123333)
    ·
      refine ⟨7298342316688415582648125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38924492355671549774123333 7298342316688415582648125)
      ·
        refine ⟨2736878368758155843493047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7298342316688415582648125 2736878368758155843493047)
        ·
          refine ⟨4105317553137233765239571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736878368758155843493047 4105317553137233765239571)
          ·
            refine ⟨6157976329705850647859357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105317553137233765239571 6157976329705850647859357)
            ·
              refine ⟨2309241123639693992947259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6157976329705850647859357 2309241123639693992947259)
              ·
                refine ⟨3463861685459540989420889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2309241123639693992947259 3463861685459540989420889)
                ·
                  refine ⟨2597896264094655742065667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3463861685459540989420889 2597896264094655742065667)
                  ·
                    refine ⟨3896844396141983613098501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597896264094655742065667 3896844396141983613098501)
                    ·
                      refine ⟨730658324276621927455969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3896844396141983613098501 730658324276621927455969)
                      ·
                        rfl

theorem cell23_1422952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1422952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422952 prefixEnd_1422952 := by exact prefixLift 1422952
  have htrace : WordTrace (prefixWord ++ tailWord_1422952) baseStart_1422952 baseEnd_1422952 := by
    simpa [prefixWord, tailWord_1422952, baseEnd_1422952] using wordTrace_append hprefix tailTrace_1422952
  have hstable : (prefixWord ++ tailWord_1422952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422952).length < 2 ^ (prefixWord ++ tailWord_1422952).sum := by decide
  have hdescent : baseEnd_1422952 < baseStart_1422952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422965 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1422965 : Nat := 118140960795 + 1422965 * 2 ^ 59
def prefixEnd_1422965 : Nat := 4983230072969 + 3 ^ 40 * 1422965 * 2
def baseEnd_1422965 : Nat := 730664999525130376593409

theorem tailTrace_1422965 : CollatzResearch.WordTrace tailWord_1422965 prefixEnd_1422965 730664999525130376593409 := by
  unfold tailWord_1422965
  simp only [CollatzResearch.WordTrace]
  refine ⟨51899797289848302919054349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34599864859898868612702899 51899797289848302919054349)
  ·
    refine ⟨19462423983693113594645381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51899797289848302919054349 19462423983693113594645381)
    ·
      refine ⟨3649204496942458798996009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19462423983693113594645381 3649204496942458798996009)
      ·
        refine ⟨2736903372706844099247007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3649204496942458798996009 2736903372706844099247007)
        ·
          refine ⟨4105355059060266148870511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736903372706844099247007 4105355059060266148870511)
          ·
            refine ⟨6158032588590399223305767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105355059060266148870511 6158032588590399223305767)
            ·
              refine ⟨9237048882885598834958651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158032588590399223305767 9237048882885598834958651)
              ·
                refine ⟨13855573324328398252437977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9237048882885598834958651 13855573324328398252437977)
                ·
                  refine ⟨10391679993246298689328483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13855573324328398252437977 10391679993246298689328483)
                  ·
                    refine ⟨15587519989869448033992725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10391679993246298689328483 15587519989869448033992725)
                    ·
                      refine ⟨730664999525130376593409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15587519989869448033992725 730664999525130376593409)
                      ·
                        rfl

theorem cell23_1422965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1422965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1422965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1422965 prefixEnd_1422965 := by exact prefixLift 1422965
  have htrace : WordTrace (prefixWord ++ tailWord_1422965) baseStart_1422965 baseEnd_1422965 := by
    simpa [prefixWord, tailWord_1422965, baseEnd_1422965] using wordTrace_append hprefix tailTrace_1422965
  have hstable : (prefixWord ++ tailWord_1422965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422965).length < 2 ^ (prefixWord ++ tailWord_1422965).sum := by decide
  have hdescent : baseEnd_1422965 < baseStart_1422965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423012 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_1423012 : Nat := 118140960795 + 1423012 * 2 ^ 59
def prefixEnd_1423012 : Nat := 4983230072969 + 3 ^ 40 * 1423012 * 2
def baseEnd_1423012 : Nat := 730689133115891692705693

theorem tailTrace_1423012 : CollatzResearch.WordTrace tailWord_1423012 prefixEnd_1423012 730689133115891692705693 := by
  unfold tailWord_1423012
  simp only [CollatzResearch.WordTrace]
  refine ⟨25950755760339014973007645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34601007680452019964010193 25950755760339014973007645)
  ·
    refine ⟨9731533410127130614877867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25950755760339014973007645 9731533410127130614877867)
    ·
      refine ⟨14597300115190695922316801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9731533410127130614877867 14597300115190695922316801)
      ·
        refine ⟨10947975086393021941737601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14597300115190695922316801 10947975086393021941737601)
        ·
          refine ⟨8210981314794766456303201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10947975086393021941737601 8210981314794766456303201)
          ·
            refine ⟨6158235986096074842227401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8210981314794766456303201 6158235986096074842227401)
            ·
              refine ⟨4618676989572056131670551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6158235986096074842227401 4618676989572056131670551)
              ·
                refine ⟨6928015484358084197505827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618676989572056131670551 6928015484358084197505827)
                ·
                  refine ⟨10392023226537126296258741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928015484358084197505827 10392023226537126296258741)
                  ·
                    refine ⟨974252177487855590274257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10392023226537126296258741 974252177487855590274257)
                    ·
                      refine ⟨730689133115891692705693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974252177487855590274257 730689133115891692705693)
                      ·
                        rfl

theorem cell23_1423012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_1423012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423012 prefixEnd_1423012 := by exact prefixLift 1423012
  have htrace : WordTrace (prefixWord ++ tailWord_1423012) baseStart_1423012 baseEnd_1423012 := by
    simpa [prefixWord, tailWord_1423012, baseEnd_1423012] using wordTrace_append hprefix tailTrace_1423012
  have hstable : (prefixWord ++ tailWord_1423012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423012).length < 2 ^ (prefixWord ++ tailWord_1423012).sum := by decide
  have hdescent : baseEnd_1423012 < baseStart_1423012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423045 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_1423045 : Nat := 118140960795 + 1423045 * 2 ^ 59
def prefixEnd_1423045 : Nat := 4983230072969 + 3 ^ 40 * 1423045 * 2
def baseEnd_1423045 : Nat := 730706077977490063593041

theorem tailTrace_1423045 : CollatzResearch.WordTrace tailWord_1423045 prefixEnd_1423045 730706077977490063593041 := by
  unfold tailWord_1423045
  simp only [CollatzResearch.WordTrace]
  refine ⟨51902715129558476581966589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34601810086372317721311059 51902715129558476581966589)
  ·
    refine ⟨19463518173584428718237471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51902715129558476581966589 19463518173584428718237471)
    ·
      refine ⟨29195277260376643077356207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19463518173584428718237471 29195277260376643077356207)
      ·
        refine ⟨43792915890564964616034311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29195277260376643077356207 43792915890564964616034311)
        ·
          refine ⟨65689373835847446924051467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43792915890564964616034311 65689373835847446924051467)
          ·
            refine ⟨98534060753771170386077201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65689373835847446924051467 98534060753771170386077201)
            ·
              refine ⟨73900545565328377789557901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98534060753771170386077201 73900545565328377789557901)
              ·
                refine ⟨27712704586998141671084213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73900545565328377789557901 27712704586998141671084213)
                ·
                  refine ⟨2598066055031075781664145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27712704586998141671084213 2598066055031075781664145)
                  ·
                    refine ⟨1948549541273306836248109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2598066055031075781664145 1948549541273306836248109)
                    ·
                      refine ⟨730706077977490063593041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1948549541273306836248109 730706077977490063593041)
                      ·
                        rfl

theorem cell23_1423045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_1423045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423045 prefixEnd_1423045 := by exact prefixLift 1423045
  have htrace : WordTrace (prefixWord ++ tailWord_1423045) baseStart_1423045 baseEnd_1423045 := by
    simpa [prefixWord, tailWord_1423045, baseEnd_1423045] using wordTrace_append hprefix tailTrace_1423045
  have hstable : (prefixWord ++ tailWord_1423045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423045).length < 2 ^ (prefixWord ++ tailWord_1423045).sum := by decide
  have hdescent : baseEnd_1423045 < baseStart_1423045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423069 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1423069 : Nat := 118140960795 + 1423069 * 2 ^ 59
def prefixEnd_1423069 : Nat := 4983230072969 + 3 ^ 40 * 1423069 * 2
def baseEnd_1423069 : Nat := 243572800504399323230977

theorem tailTrace_1423069 : CollatzResearch.WordTrace tailWord_1423069 prefixEnd_1423069 243572800504399323230977 := by
  unfold tailWord_1423069
  simp only [CollatzResearch.WordTrace]
  refine ⟨51903590481471528680840261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34602393654314352453893507 51903590481471528680840261)
  ·
    refine ⟨9731923215275911627657549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51903590481471528680840261 9731923215275911627657549)
    ·
      refine ⟨3649471205728466860371581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9731923215275911627657549 3649471205728466860371581)
      ·
        refine ⟨1368551702148175072639343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3649471205728466860371581 1368551702148175072639343)
        ·
          refine ⟨2052827553222262608959015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368551702148175072639343 2052827553222262608959015)
          ·
            refine ⟨3079241329833393913438523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052827553222262608959015 3079241329833393913438523)
            ·
              refine ⟨4618861994750090870157785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079241329833393913438523 4618861994750090870157785)
              ·
                refine ⟨3464146496062568152618339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4618861994750090870157785 3464146496062568152618339)
                ·
                  refine ⟨5196219744093852228927509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464146496062568152618339 5196219744093852228927509)
                  ·
                    refine ⟨243572800504399323230977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5196219744093852228927509 243572800504399323230977)
                    ·
                      rfl

theorem cell23_1423069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1423069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423069 prefixEnd_1423069 := by exact prefixLift 1423069
  have htrace : WordTrace (prefixWord ++ tailWord_1423069) baseStart_1423069 baseEnd_1423069 := by
    simpa [prefixWord, tailWord_1423069, baseEnd_1423069] using wordTrace_append hprefix tailTrace_1423069
  have hstable : (prefixWord ++ tailWord_1423069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423069).length < 2 ^ (prefixWord ++ tailWord_1423069).sum := by decide
  have hdescent : baseEnd_1423069 < baseStart_1423069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423076 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_1423076 : Nat := 118140960795 + 1423076 * 2 ^ 59
def prefixEnd_1423076 : Nat := 4983230072969 + 3 ^ 40 * 1423076 * 2
def baseEnd_1423076 : Nat := 730721995877779442305399

theorem tailTrace_1423076 : CollatzResearch.WordTrace tailWord_1423076 prefixEnd_1423076 730721995877779442305399 := by
  unfold tailWord_1423076
  simp only [CollatzResearch.WordTrace]
  refine ⟨25951922896223084438172541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34602563861630779250896721 25951922896223084438172541)
  ·
    refine ⟨9731971086083656664314703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25951922896223084438172541 9731971086083656664314703)
    ·
      refine ⟨14597956629125484996472055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9731971086083656664314703 14597956629125484996472055)
      ·
        refine ⟨21896934943688227494708083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14597956629125484996472055 21896934943688227494708083)
        ·
          refine ⟨32845402415532341242062125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21896934943688227494708083 32845402415532341242062125)
          ·
            refine ⟨12317025905824627965773297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32845402415532341242062125 12317025905824627965773297)
            ·
              refine ⟨9237769429368470974329973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12317025905824627965773297 9237769429368470974329973)
              ·
                refine ⟨866040884003294153843435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9237769429368470974329973 866040884003294153843435)
                ·
                  refine ⟨1299061326004941230765153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866040884003294153843435 1299061326004941230765153)
                  ·
                    refine ⟨974295994503705923073865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1299061326004941230765153 974295994503705923073865)
                    ·
                      refine ⟨730721995877779442305399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974295994503705923073865 730721995877779442305399)
                      ·
                        rfl

theorem cell23_1423076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_1423076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423076 prefixEnd_1423076 := by exact prefixLift 1423076
  have htrace : WordTrace (prefixWord ++ tailWord_1423076) baseStart_1423076 baseEnd_1423076 := by
    simpa [prefixWord, tailWord_1423076, baseEnd_1423076] using wordTrace_append hprefix tailTrace_1423076
  have hstable : (prefixWord ++ tailWord_1423076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423076).length < 2 ^ (prefixWord ++ tailWord_1423076).sum := by decide
  have hdescent : baseEnd_1423076 < baseStart_1423076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423135 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1423135 : Nat := 118140960795 + 1423135 * 2 ^ 59
def prefixEnd_1423135 : Nat := 4983230072969 + 3 ^ 40 * 1423135 * 2
def baseEnd_1423135 : Nat := 730752291236394711467627

theorem tailTrace_1423135 : CollatzResearch.WordTrace tailWord_1423135 prefixEnd_1423135 730752291236394711467627 := by
  unfold tailWord_1423135
  simp only [CollatzResearch.WordTrace]
  refine ⟨51905997699232421952742859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34603998466154947968495239 51905997699232421952742859)
  ·
    refine ⟨77858996548848632929114289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51905997699232421952742859 77858996548848632929114289)
    ·
      refine ⟨58394247411636474696835717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77858996548848632929114289 58394247411636474696835717)
      ·
        refine ⟨10948921389681839005656697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58394247411636474696835717 10948921389681839005656697)
        ·
          refine ⟨8211691042261379254242523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10948921389681839005656697 8211691042261379254242523)
          ·
            refine ⟨12317536563392068881363785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8211691042261379254242523 12317536563392068881363785)
            ·
              refine ⟨9238152422544051661022839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12317536563392068881363785 9238152422544051661022839)
              ·
                refine ⟨13857228633816077491534259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9238152422544051661022839 13857228633816077491534259)
                ·
                  refine ⟨20785842950724116237301389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13857228633816077491534259 20785842950724116237301389)
                  ·
                    refine ⟨7794691106521543588988021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20785842950724116237301389 7794691106521543588988021)
                    ·
                      refine ⟨730752291236394711467627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7794691106521543588988021 730752291236394711467627)
                      ·
                        rfl

theorem cell23_1423135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1423135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423135 prefixEnd_1423135 := by exact prefixLift 1423135
  have htrace : WordTrace (prefixWord ++ tailWord_1423135) baseStart_1423135 baseEnd_1423135 := by
    simpa [prefixWord, tailWord_1423135, baseEnd_1423135] using wordTrace_append hprefix tailTrace_1423135
  have hstable : (prefixWord ++ tailWord_1423135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423135).length < 2 ^ (prefixWord ++ tailWord_1423135).sum := by decide
  have hdescent : baseEnd_1423135 < baseStart_1423135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423162 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_1423162 : Nat := 118140960795 + 1423162 * 2 ^ 59
def prefixEnd_1423162 : Nat := 4983230072969 + 3 ^ 40 * 1423162 * 2
def baseEnd_1423162 : Nat := 730766155214066105830003

theorem tailTrace_1423162 : CollatzResearch.WordTrace tailWord_1423162 prefixEnd_1423162 730766155214066105830003 := by
  unfold tailWord_1423162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976745617533651390993935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34604654980089737042650493 12976745617533651390993935)
  ·
    refine ⟨19465118426300477086490903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12976745617533651390993935 19465118426300477086490903)
    ·
      refine ⟨29197677639450715629736355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19465118426300477086490903 29197677639450715629736355)
      ·
        refine ⟨43796516459176073444604533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29197677639450715629736355 43796516459176073444604533)
        ·
          refine ⟨4105923418047756885431675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43796516459176073444604533 4105923418047756885431675)
          ·
            refine ⟨6158885127071635328147513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105923418047756885431675 6158885127071635328147513)
            ·
              refine ⟨4619163845303726496110635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6158885127071635328147513 4619163845303726496110635)
              ·
                refine ⟨6928745767955589744165953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619163845303726496110635 6928745767955589744165953)
                ·
                  refine ⟨5196559325966692308124465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6928745767955589744165953 5196559325966692308124465)
                  ·
                    refine ⟨3897419494475019231093349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5196559325966692308124465 3897419494475019231093349)
                    ·
                      refine ⟨730766155214066105830003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3897419494475019231093349 730766155214066105830003)
                      ·
                        rfl

theorem cell23_1423162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_1423162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423162 prefixEnd_1423162 := by exact prefixLift 1423162
  have htrace : WordTrace (prefixWord ++ tailWord_1423162) baseStart_1423162 baseEnd_1423162 := by
    simpa [prefixWord, tailWord_1423162, baseEnd_1423162] using wordTrace_append hprefix tailTrace_1423162
  have hstable : (prefixWord ++ tailWord_1423162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423162).length < 2 ^ (prefixWord ++ tailWord_1423162).sum := by decide
  have hdescent : baseEnd_1423162 < baseStart_1423162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423166 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_1423166 : Nat := 118140960795 + 1423166 * 2 ^ 59
def prefixEnd_1423166 : Nat := 4983230072969 + 3 ^ 40 * 1423166 * 2
def baseEnd_1423166 : Nat := 730768209136684090179985

theorem tailTrace_1423166 : CollatzResearch.WordTrace tailWord_1423166 prefixEnd_1423166 730768209136684090179985 := by
  unfold tailWord_1423166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488391045265014280890169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34604752241413409498080901 6488391045265014280890169)
  ·
    refine ⟨4866293283948760710667627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6488391045265014280890169 4866293283948760710667627)
    ·
      refine ⟨7299439925923141066001441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4866293283948760710667627 7299439925923141066001441)
      ·
        refine ⟨5474579944442355799501081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7299439925923141066001441 5474579944442355799501081)
        ·
          refine ⟨4105934958331766849625811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5474579944442355799501081 4105934958331766849625811)
          ·
            refine ⟨6158902437497650274438717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105934958331766849625811 6158902437497650274438717)
            ·
              refine ⟨2309588414061618852914519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6158902437497650274438717 2309588414061618852914519)
              ·
                refine ⟨3464382621092428279371779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2309588414061618852914519 3464382621092428279371779)
                ·
                  refine ⟨5196573931638642419057669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464382621092428279371779 5196573931638642419057669)
                  ·
                    refine ⟨974357612182245453573313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5196573931638642419057669 974357612182245453573313)
                    ·
                      refine ⟨730768209136684090179985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974357612182245453573313 730768209136684090179985)
                      ·
                        rfl

theorem cell23_1423166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_1423166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423166 prefixEnd_1423166 := by exact prefixLift 1423166
  have htrace : WordTrace (prefixWord ++ tailWord_1423166) baseStart_1423166 baseEnd_1423166 := by
    simpa [prefixWord, tailWord_1423166, baseEnd_1423166] using wordTrace_append hprefix tailTrace_1423166
  have hstable : (prefixWord ++ tailWord_1423166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423166).length < 2 ^ (prefixWord ++ tailWord_1423166).sum := by decide
  have hdescent : baseEnd_1423166 < baseStart_1423166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423189 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 5]
def baseStart_1423189 : Nat := 118140960795 + 1423189 * 2 ^ 59
def prefixEnd_1423189 : Nat := 4983230072969 + 3 ^ 40 * 1423189 * 2
def baseEnd_1423189 : Nat := 81197779910193055576931

theorem tailTrace_1423189 : CollatzResearch.WordTrace tailWord_1423189 prefixEnd_1423189 81197779910193055576931 := by
  unfold tailWord_1423189
  simp only [CollatzResearch.WordTrace]
  refine ⟨51907967241036789175208621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34605311494024526116805747 51907967241036789175208621)
  ·
    refine ⟨19465487715388795940703233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51907967241036789175208621 19465487715388795940703233)
    ·
      refine ⟨14599115786541596955527425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19465487715388795940703233 14599115786541596955527425)
      ·
        refine ⟨10949336839906197716645569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14599115786541596955527425 10949336839906197716645569)
        ·
          refine ⟨8212002629929648287484177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10949336839906197716645569 8212002629929648287484177)
          ·
            refine ⟨6159001972447236215613133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8212002629929648287484177 6159001972447236215613133)
            ·
              refine ⟨2309625739667713580854925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6159001972447236215613133 2309625739667713580854925)
              ·
                refine ⟨866109652375392592820597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2309625739667713580854925 866109652375392592820597)
                ·
                  refine ⟨81197779910193055576931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866109652375392592820597 81197779910193055576931)
                  ·
                    rfl

theorem cell23_1423189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_1423189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423189 prefixEnd_1423189 := by exact prefixLift 1423189
  have htrace : WordTrace (prefixWord ++ tailWord_1423189) baseStart_1423189 baseEnd_1423189 := by
    simpa [prefixWord, tailWord_1423189, baseEnd_1423189] using wordTrace_append hprefix tailTrace_1423189
  have hstable : (prefixWord ++ tailWord_1423189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423189).length < 2 ^ (prefixWord ++ tailWord_1423189).sum := by decide
  have hdescent : baseEnd_1423189 < baseStart_1423189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423192 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 7, 2]
def baseStart_1423192 : Nat := 118140960795 + 1423192 * 2 ^ 59
def prefixEnd_1423192 : Nat := 4983230072969 + 3 ^ 40 * 1423192 * 2
def baseEnd_1423192 : Nat := 730781559633700988454865

theorem tailTrace_1423192 : CollatzResearch.WordTrace tailWord_1423192 prefixEnd_1423192 730781559633700988454865 := by
  unfold tailWord_1423192
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954038330012960343783915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34605384440017280458378553 25954038330012960343783915)
  ·
    refine ⟨38931057495019440515675873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25954038330012960343783915 38931057495019440515675873)
    ·
      refine ⟨29198293121264580386756905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38931057495019440515675873 29198293121264580386756905)
      ·
        refine ⟨21898719840948435290067679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29198293121264580386756905 21898719840948435290067679)
        ·
          refine ⟨32848079761422652935101519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21898719840948435290067679 32848079761422652935101519)
          ·
            refine ⟨49272119642133979402652279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32848079761422652935101519 49272119642133979402652279)
            ·
              refine ⟨73908179463200969103978419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49272119642133979402652279 73908179463200969103978419)
              ·
                refine ⟨110862269194801453655967629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73908179463200969103978419 110862269194801453655967629)
                ·
                  refine ⟨41573350948050545120987861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110862269194801453655967629 41573350948050545120987861)
                  ·
                    refine ⟨974375412844934651273153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41573350948050545120987861 974375412844934651273153)
                    ·
                      refine ⟨730781559633700988454865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974375412844934651273153 730781559633700988454865)
                      ·
                        rfl

theorem cell23_1423192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_1423192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423192 prefixEnd_1423192 := by exact prefixLift 1423192
  have htrace : WordTrace (prefixWord ++ tailWord_1423192) baseStart_1423192 baseEnd_1423192 := by
    simpa [prefixWord, tailWord_1423192, baseEnd_1423192] using wordTrace_append hprefix tailTrace_1423192
  have hstable : (prefixWord ++ tailWord_1423192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423192).length < 2 ^ (prefixWord ++ tailWord_1423192).sum := by decide
  have hdescent : baseEnd_1423192 < baseStart_1423192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423212 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_1423212 : Nat := 118140960795 + 1423212 * 2 ^ 59
def prefixEnd_1423212 : Nat := 4983230072969 + 3 ^ 40 * 1423212 * 2
def baseEnd_1423212 : Nat := 730791829246790910204773

theorem tailTrace_1423212 : CollatzResearch.WordTrace tailWord_1423212 prefixEnd_1423212 730791829246790910204773 := by
  unfold tailWord_1423212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954403059976732051647945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34605870746635642735530593 25954403059976732051647945)
  ·
    refine ⟨19465802294982549038735959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25954403059976732051647945 19465802294982549038735959)
    ·
      refine ⟨29198703442473823558103939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19465802294982549038735959 29198703442473823558103939)
      ·
        refine ⟨43798055163710735337155909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29198703442473823558103939 43798055163710735337155909)
        ·
          refine ⟨8212135343195762875716733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43798055163710735337155909 8212135343195762875716733)
          ·
            refine ⟨3079550753698411078393775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8212135343195762875716733 3079550753698411078393775)
            ·
              refine ⟨4619326130547616617590663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079550753698411078393775 4619326130547616617590663)
              ·
                refine ⟨6928989195821424926385995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619326130547616617590663 6928989195821424926385995)
                ·
                  refine ⟨10393483793732137389578993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928989195821424926385995 10393483793732137389578993)
                  ·
                    refine ⟨7795112845299103042184245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10393483793732137389578993 7795112845299103042184245)
                    ·
                      refine ⟨730791829246790910204773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7795112845299103042184245 730791829246790910204773)
                      ·
                        rfl

theorem cell23_1423212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_1423212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423212 prefixEnd_1423212 := by exact prefixLift 1423212
  have htrace : WordTrace (prefixWord ++ tailWord_1423212) baseStart_1423212 baseEnd_1423212 := by
    simpa [prefixWord, tailWord_1423212, baseEnd_1423212] using wordTrace_append hprefix tailTrace_1423212
  have hstable : (prefixWord ++ tailWord_1423212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423212).length < 2 ^ (prefixWord ++ tailWord_1423212).sum := by decide
  have hdescent : baseEnd_1423212 < baseStart_1423212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423232 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 5, 4]
def baseStart_1423232 : Nat := 118140960795 + 1423232 * 2 ^ 59
def prefixEnd_1423232 : Nat := 4983230072969 + 3 ^ 40 * 1423232 * 2
def baseEnd_1423232 : Nat := 243600699619960277318227

theorem tailTrace_1423232 : CollatzResearch.WordTrace tailWord_1423232 prefixEnd_1423232 243600699619960277318227 := by
  unfold tailWord_1423232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954767789940503759511975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34606357053254005012682633 25954767789940503759511975)
  ·
    refine ⟨38932151684910755639267963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25954767789940503759511975 38932151684910755639267963)
    ·
      refine ⟨58398227527366133458901945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38932151684910755639267963 58398227527366133458901945)
      ·
        refine ⟨43798670645524600094176459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58398227527366133458901945 43798670645524600094176459)
        ·
          refine ⟨65698005968286900141264689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43798670645524600094176459 65698005968286900141264689)
          ·
            refine ⟨49273504476215175105948517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65698005968286900141264689 49273504476215175105948517)
            ·
              refine ⟨9238782089290345332365347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49273504476215175105948517 9238782089290345332365347)
              ·
                refine ⟨13858173133935517998548021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9238782089290345332365347 13858173133935517998548021)
                ·
                  refine ⟨1299203731306454812363877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13858173133935517998548021 1299203731306454812363877)
                  ·
                    refine ⟨243600699619960277318227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299203731306454812363877 243600699619960277318227)
                    ·
                      rfl

theorem cell23_1423232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_1423232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423232 prefixEnd_1423232 := by exact prefixLift 1423232
  have htrace : WordTrace (prefixWord ++ tailWord_1423232) baseStart_1423232 baseEnd_1423232 := by
    simpa [prefixWord, tailWord_1423232, baseEnd_1423232] using wordTrace_append hprefix tailTrace_1423232
  have hstable : (prefixWord ++ tailWord_1423232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423232).length < 2 ^ (prefixWord ++ tailWord_1423232).sum := by decide
  have hdescent : baseEnd_1423232 < baseStart_1423232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423275 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 11]
def baseStart_1423275 : Nat := 118140960795 + 1423275 * 2 ^ 59
def prefixEnd_1423275 : Nat := 4983230072969 + 3 ^ 40 * 1423275 * 2
def baseEnd_1423275 : Nat := 243608059509341387905661

theorem tailTrace_1423275 : CollatzResearch.WordTrace tailWord_1423275 prefixEnd_1423275 243608059509341387905661 := by
  unfold tailWord_1423275
  simp only [CollatzResearch.WordTrace]
  refine ⟨51911103918725225862839279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34607402612483483908559519 51911103918725225862839279)
  ·
    refine ⟨77866655878087838794258919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51911103918725225862839279 77866655878087838794258919)
    ·
      refine ⟨116799983817131758191388379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77866655878087838794258919 116799983817131758191388379)
      ·
        refine ⟨175199975725697637287082569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116799983817131758191388379 175199975725697637287082569)
        ·
          refine ⟨131399981794273227965311927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175199975725697637287082569 131399981794273227965311927)
          ·
            refine ⟨197099972691409841947967891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131399981794273227965311927 197099972691409841947967891)
            ·
              refine ⟨295649959037114762921951837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197099972691409841947967891 295649959037114762921951837)
              ·
                refine ⟨110868734638918036095731939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295649959037114762921951837 110868734638918036095731939)
                ·
                  refine ⟨166303101958377054143597909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110868734638918036095731939 166303101958377054143597909)
                  ·
                    refine ⟨243608059509341387905661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 166303101958377054143597909 243608059509341387905661)
                    ·
                      rfl

theorem cell23_1423275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_1423275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423275 prefixEnd_1423275 := by exact prefixLift 1423275
  have htrace : WordTrace (prefixWord ++ tailWord_1423275) baseStart_1423275 baseEnd_1423275 := by
    simpa [prefixWord, tailWord_1423275, baseEnd_1423275] using wordTrace_append hprefix tailTrace_1423275
  have hstable : (prefixWord ++ tailWord_1423275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423275).length < 2 ^ (prefixWord ++ tailWord_1423275).sum := by decide
  have hdescent : baseEnd_1423275 < baseStart_1423275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423316 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_1423316 : Nat := 118140960795 + 1423316 * 2 ^ 59
def prefixEnd_1423316 : Nat := 4983230072969 + 3 ^ 40 * 1423316 * 2
def baseEnd_1423316 : Nat := 730845231234858503304295

theorem tailTrace_1423316 : CollatzResearch.WordTrace tailWord_1423316 prefixEnd_1423316 730845231234858503304295 := by
  unfold tailWord_1423316
  simp only [CollatzResearch.WordTrace]
  refine ⟨25956299655788344932540901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34608399541051126576721201 25956299655788344932540901)
  ·
    refine ⟨4866806185460314674851419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25956299655788344932540901 4866806185460314674851419)
    ·
      refine ⟨7300209278190472012277129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4866806185460314674851419 7300209278190472012277129)
      ·
        refine ⟨5475156958642854009207847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7300209278190472012277129 5475156958642854009207847)
        ·
          refine ⟨8212735437964281013811771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5475156958642854009207847 8212735437964281013811771)
          ·
            refine ⟨12319103156946421520717657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212735437964281013811771 12319103156946421520717657)
            ·
              refine ⟨9239327367709816140538243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12319103156946421520717657 9239327367709816140538243)
              ·
                refine ⟨13858991051564724210807365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239327367709816140538243 13858991051564724210807365)
                ·
                  refine ⟨2598560822168385789526381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13858991051564724210807365 2598560822168385789526381)
                  ·
                    refine ⟨974460308313144671072393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598560822168385789526381 974460308313144671072393)
                    ·
                      refine ⟨730845231234858503304295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974460308313144671072393 730845231234858503304295)
                      ·
                        rfl

theorem cell23_1423316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_1423316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423316 prefixEnd_1423316 := by exact prefixLift 1423316
  have htrace : WordTrace (prefixWord ++ tailWord_1423316) baseStart_1423316 baseEnd_1423316 := by
    simpa [prefixWord, tailWord_1423316, baseEnd_1423316] using wordTrace_append hprefix tailTrace_1423316
  have hstable : (prefixWord ++ tailWord_1423316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423316).length < 2 ^ (prefixWord ++ tailWord_1423316).sum := by decide
  have hdescent : baseEnd_1423316 < baseStart_1423316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423339 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 2, 4]
def baseStart_1423339 : Nat := 118140960795 + 1423339 * 2 ^ 59
def prefixEnd_1423339 : Nat := 4983230072969 + 3 ^ 40 * 1423339 * 2
def baseEnd_1423339 : Nat := 243619013763303971105563

theorem tailTrace_1423339 : CollatzResearch.WordTrace tailWord_1423339 prefixEnd_1423339 243619013763303971105563 := by
  unfold tailWord_1423339
  simp only [CollatzResearch.WordTrace]
  refine ⟨51913438190493364793169071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34608958793662243195446047 51913438190493364793169071)
  ·
    refine ⟨77870157285740047189753607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51913438190493364793169071 77870157285740047189753607)
    ·
      refine ⟨116805235928610070784630411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77870157285740047189753607 116805235928610070784630411)
      ·
        refine ⟨175207853892915106176945617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116805235928610070784630411 175207853892915106176945617)
        ·
          refine ⟨131405890419686329632709213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175207853892915106176945617 131405890419686329632709213)
          ·
            refine ⟨49277208907382373612265955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131405890419686329632709213 49277208907382373612265955)
            ·
              refine ⟨73915813361073560418398933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49277208907382373612265955 73915813361073560418398933)
              ·
                refine ⟨1732401875650161572306225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73915813361073560418398933 1732401875650161572306225)
                ·
                  refine ⟨1299301406737621179229669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1732401875650161572306225 1299301406737621179229669)
                  ·
                    refine ⟨243619013763303971105563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299301406737621179229669 243619013763303971105563)
                    ·
                      rfl

theorem cell23_1423339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 4].length) (baseStart_1423339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423339 prefixEnd_1423339 := by exact prefixLift 1423339
  have htrace : WordTrace (prefixWord ++ tailWord_1423339) baseStart_1423339 baseEnd_1423339 := by
    simpa [prefixWord, tailWord_1423339, baseEnd_1423339] using wordTrace_append hprefix tailTrace_1423339
  have hstable : (prefixWord ++ tailWord_1423339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423339).length < 2 ^ (prefixWord ++ tailWord_1423339).sum := by decide
  have hdescent : baseEnd_1423339 < baseStart_1423339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423449 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1423449 : Nat := 118140960795 + 1423449 * 2 ^ 59
def prefixEnd_1423449 : Nat := 4983230072969 + 3 ^ 40 * 1423449 * 2
def baseEnd_1423449 : Nat := 730913524161906482941183

theorem tailTrace_1423449 : CollatzResearch.WordTrace tailWord_1423449 prefixEnd_1423449 730913524161906482941183 := by
  unfold tailWord_1423449
  simp only [CollatzResearch.WordTrace]
  refine ⟨51917450220094853579673401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34611633480063235719782267 51917450220094853579673401)
  ·
    refine ⟨38938087665071140184755051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51917450220094853579673401 38938087665071140184755051)
    ·
      refine ⟨58407131497606710277132577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38938087665071140184755051 58407131497606710277132577)
      ·
        refine ⟨43805348623205032707849433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58407131497606710277132577 43805348623205032707849433)
        ·
          refine ⟨32854011467403774530887075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43805348623205032707849433 32854011467403774530887075)
          ·
            refine ⟨49281017201105661796330613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32854011467403774530887075 49281017201105661796330613)
            ·
              refine ⟨4620095362603655793405995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49281017201105661796330613 4620095362603655793405995)
              ·
                refine ⟨6930143043905483690108993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620095362603655793405995 6930143043905483690108993)
                ·
                  refine ⟨5197607282929112767581745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6930143043905483690108993 5197607282929112767581745)
                  ·
                    refine ⟨3898205462196834575686309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5197607282929112767581745 3898205462196834575686309)
                    ·
                      refine ⟨730913524161906482941183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3898205462196834575686309 730913524161906482941183)
                      ·
                        rfl

theorem cell23_1423449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1423449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423449 prefixEnd_1423449 := by exact prefixLift 1423449
  have htrace : WordTrace (prefixWord ++ tailWord_1423449) baseStart_1423449 baseEnd_1423449 := by
    simpa [prefixWord, tailWord_1423449, baseEnd_1423449] using wordTrace_append hprefix tailTrace_1423449
  have hstable : (prefixWord ++ tailWord_1423449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423449).length < 2 ^ (prefixWord ++ tailWord_1423449).sum := by decide
  have hdescent : baseEnd_1423449 < baseStart_1423449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423509 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1423509 : Nat := 118140960795 + 1423509 * 2 ^ 59
def prefixEnd_1423509 : Nat := 4983230072969 + 3 ^ 40 * 1423509 * 2
def baseEnd_1423509 : Nat := 730944333001176248190907

theorem tailTrace_1423509 : CollatzResearch.WordTrace tailWord_1423509 prefixEnd_1423509 730944333001176248190907 := by
  unfold tailWord_1423509
  simp only [CollatzResearch.WordTrace]
  refine ⟨51919638599877483826857581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34613092399918322551238387 51919638599877483826857581)
  ·
    refine ⟨19469864474954056435071593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51919638599877483826857581 19469864474954056435071593)
    ·
      refine ⟨14602398356215542326303695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19469864474954056435071593 14602398356215542326303695)
      ·
        refine ⟨21903597534323313489455543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14602398356215542326303695 21903597534323313489455543)
        ·
          refine ⟨32855396301484970234183315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21903597534323313489455543 32855396301484970234183315)
          ·
            refine ⟨49283094452227455351274973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32855396301484970234183315 49283094452227455351274973)
            ·
              refine ⟨18481160419585295756728115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49283094452227455351274973 18481160419585295756728115)
              ·
                refine ⟨27721740629377943635092173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18481160419585295756728115 27721740629377943635092173)
                ·
                  refine ⟨10395652736016728863159565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27721740629377943635092173 10395652736016728863159565)
                  ·
                    refine ⟨3898369776006273323684837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10395652736016728863159565 3898369776006273323684837)
                    ·
                      refine ⟨730944333001176248190907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3898369776006273323684837 730944333001176248190907)
                      ·
                        rfl

theorem cell23_1423509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1423509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423509 prefixEnd_1423509 := by exact prefixLift 1423509
  have htrace : WordTrace (prefixWord ++ tailWord_1423509) baseStart_1423509 baseEnd_1423509 := by
    simpa [prefixWord, tailWord_1423509, baseEnd_1423509] using wordTrace_append hprefix tailTrace_1423509
  have hstable : (prefixWord ++ tailWord_1423509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423509).length < 2 ^ (prefixWord ++ tailWord_1423509).sum := by decide
  have hdescent : baseEnd_1423509 < baseStart_1423509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423527 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 5]
def baseStart_1423527 : Nat := 118140960795 + 1423527 * 2 ^ 59
def prefixEnd_1423527 : Nat := 4983230072969 + 3 ^ 40 * 1423527 * 2
def baseEnd_1423527 : Nat := 81217063961439686418425

theorem tailTrace_1423527 : CollatzResearch.WordTrace tailWord_1423527 prefixEnd_1423527 81217063961439686418425 := by
  unfold tailWord_1423527
  simp only [CollatzResearch.WordTrace]
  refine ⟨51920295113812272901012835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34613530075874848600675223 51920295113812272901012835)
  ·
    refine ⟨77880442670718409351519253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51920295113812272901012835 77880442670718409351519253)
    ·
      refine ⟨3650645750189925438352465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77880442670718409351519253 3650645750189925438352465)
      ·
        refine ⟨2737984312642444078764349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3650645750189925438352465 2737984312642444078764349)
        ·
          refine ⟨1026744117240916529536631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2737984312642444078764349 1026744117240916529536631)
          ·
            refine ⟨1540116175861374794304947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026744117240916529536631 1540116175861374794304947)
            ·
              refine ⟨2310174263792062191457421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540116175861374794304947 2310174263792062191457421)
              ·
                refine ⟨866315348922023321796533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2310174263792062191457421 866315348922023321796533)
                ·
                  refine ⟨81217063961439686418425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866315348922023321796533 81217063961439686418425)
                  ·
                    rfl

theorem cell23_1423527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 5].length) (baseStart_1423527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423527 prefixEnd_1423527 := by exact prefixLift 1423527
  have htrace : WordTrace (prefixWord ++ tailWord_1423527) baseStart_1423527 baseEnd_1423527 := by
    simpa [prefixWord, tailWord_1423527, baseEnd_1423527] using wordTrace_append hprefix tailTrace_1423527
  have hstable : (prefixWord ++ tailWord_1423527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423527).length < 2 ^ (prefixWord ++ tailWord_1423527).sum := by decide
  have hdescent : baseEnd_1423527 < baseStart_1423527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423546 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_1423546 : Nat := 118140960795 + 1423546 * 2 ^ 59
def prefixEnd_1423546 : Nat := 4983230072969 + 3 ^ 40 * 1423546 * 2
def baseEnd_1423546 : Nat := 730963331785392603428237

theorem tailTrace_1423546 : CollatzResearch.WordTrace tailWord_1423546 prefixEnd_1423546 730963331785392603428237 := by
  unfold tailWord_1423546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12980247025185859786488623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34613992067162292763969661 12980247025185859786488623)
  ·
    refine ⟨19470370537778789679732935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12980247025185859786488623 19470370537778789679732935)
    ·
      refine ⟨29205555806668184519599403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19470370537778789679732935 29205555806668184519599403)
      ·
        refine ⟨43808333710002276779399105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29205555806668184519599403 43808333710002276779399105)
        ·
          refine ⟨32856250282501707584549329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43808333710002276779399105 32856250282501707584549329)
          ·
            refine ⟨24642187711876280688411997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32856250282501707584549329 24642187711876280688411997)
            ·
              refine ⟨9240820391953605258154499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24642187711876280688411997 9240820391953605258154499)
              ·
                refine ⟨13861230587930407887231749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9240820391953605258154499 13861230587930407887231749)
                ·
                  refine ⟨2598980735236951478855953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13861230587930407887231749 2598980735236951478855953)
                  ·
                    refine ⟨1949235551427713609141965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2598980735236951478855953 1949235551427713609141965)
                    ·
                      refine ⟨730963331785392603428237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1949235551427713609141965 730963331785392603428237)
                      ·
                        rfl

theorem cell23_1423546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_1423546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423546 prefixEnd_1423546 := by exact prefixLift 1423546
  have htrace : WordTrace (prefixWord ++ tailWord_1423546) baseStart_1423546 baseEnd_1423546 := by
    simpa [prefixWord, tailWord_1423546, baseEnd_1423546] using wordTrace_append hprefix tailTrace_1423546
  have hstable : (prefixWord ++ tailWord_1423546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423546).length < 2 ^ (prefixWord ++ tailWord_1423546).sum := by decide
  have hdescent : baseEnd_1423546 < baseStart_1423546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423569 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1423569 : Nat := 118140960795 + 1423569 * 2 ^ 59
def prefixEnd_1423569 : Nat := 4983230072969 + 3 ^ 40 * 1423569 * 2
def baseEnd_1423569 : Nat := 730975141840446013440631

theorem tailTrace_1423569 : CollatzResearch.WordTrace tailWord_1423569 prefixEnd_1423569 730975141840446013440631 := by
  unfold tailWord_1423569
  simp only [CollatzResearch.WordTrace]
  refine ⟨51921826979660114074041761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34614551319773409382694507 51921826979660114074041761)
  ·
    refine ⟨38941370234745085555531321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51921826979660114074041761 38941370234745085555531321)
    ·
      refine ⟨29206027676058814166648491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38941370234745085555531321 29206027676058814166648491)
      ·
        refine ⟨43809041514088221249972737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29206027676058814166648491 43809041514088221249972737)
        ·
          refine ⟨32856781135566165937479553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43809041514088221249972737 32856781135566165937479553)
          ·
            refine ⟨24642585851674624453109665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32856781135566165937479553 24642585851674624453109665)
            ·
              refine ⟨18481939388755968339832249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24642585851674624453109665 18481939388755968339832249)
              ·
                refine ⟨13861454541566976254874187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18481939388755968339832249 13861454541566976254874187)
                ·
                  refine ⟨20792181812350464382311281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13861454541566976254874187 20792181812350464382311281)
                  ·
                    refine ⟨15594136359262848286733461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20792181812350464382311281 15594136359262848286733461)
                    ·
                      refine ⟨730975141840446013440631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15594136359262848286733461 730975141840446013440631)
                      ·
                        rfl

theorem cell23_1423569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1423569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423569 prefixEnd_1423569 := by exact prefixLift 1423569
  have htrace : WordTrace (prefixWord ++ tailWord_1423569) baseStart_1423569 baseEnd_1423569 := by
    simpa [prefixWord, tailWord_1423569, baseEnd_1423569] using wordTrace_append hprefix tailTrace_1423569
  have hstable : (prefixWord ++ tailWord_1423569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423569).length < 2 ^ (prefixWord ++ tailWord_1423569).sum := by decide
  have hdescent : baseEnd_1423569 < baseStart_1423569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423603 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 2, 3, 2]
def baseStart_1423603 : Nat := 118140960795 + 1423603 * 2 ^ 59
def prefixEnd_1423603 : Nat := 4983230072969 + 3 ^ 40 * 1423603 * 2
def baseEnd_1423603 : Nat := 730992600182698880415475

theorem tailTrace_1423603 : CollatzResearch.WordTrace tailWord_1423603 prefixEnd_1423603 730992600182698880415475 := by
  unfold tailWord_1423603
  simp only [CollatzResearch.WordTrace]
  refine ⟨51923067061536937880779463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34615378041024625253852975 51923067061536937880779463)
  ·
    refine ⟨77884600592305406821169195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51923067061536937880779463 77884600592305406821169195)
    ·
      refine ⟨116826900888458110231753793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77884600592305406821169195 116826900888458110231753793)
      ·
        refine ⟨87620175666343582673815345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116826900888458110231753793 87620175666343582673815345)
        ·
          refine ⟨65715131749757687005361509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87620175666343582673815345 65715131749757687005361509)
          ·
            refine ⟨12321587203079566313505283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65715131749757687005361509 12321587203079566313505283)
            ·
              refine ⟨18482380804619349470257925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12321587203079566313505283 18482380804619349470257925)
              ·
                refine ⟨3465446400866128025673361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18482380804619349470257925 3465446400866128025673361)
                ·
                  refine ⟨2599084800649596019255021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465446400866128025673361 2599084800649596019255021)
                  ·
                    refine ⟨974656800243598507220633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599084800649596019255021 974656800243598507220633)
                    ·
                      refine ⟨730992600182698880415475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974656800243598507220633 730992600182698880415475)
                      ·
                        rfl

theorem cell23_1423603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3, 2].length) (baseStart_1423603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423603 prefixEnd_1423603 := by exact prefixLift 1423603
  have htrace : WordTrace (prefixWord ++ tailWord_1423603) baseStart_1423603 baseEnd_1423603 := by
    simpa [prefixWord, tailWord_1423603, baseEnd_1423603] using wordTrace_append hprefix tailTrace_1423603
  have hstable : (prefixWord ++ tailWord_1423603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423603).length < 2 ^ (prefixWord ++ tailWord_1423603).sum := by decide
  have hdescent : baseEnd_1423603 < baseStart_1423603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423616 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_1423616 : Nat := 118140960795 + 1423616 * 2 ^ 59
def prefixEnd_1423616 : Nat := 4983230072969 + 3 ^ 40 * 1423616 * 2
def baseEnd_1423616 : Nat := 730999275431207329552915

theorem tailTrace_1423616 : CollatzResearch.WordTrace tailWord_1423616 prefixEnd_1423616 730999275431207329552915 := by
  unfold tailWord_1423616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25961770605244920550501351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34615694140326560734001801 25961770605244920550501351)
  ·
    refine ⟨38942655907867380825752027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25961770605244920550501351 38942655907867380825752027)
    ·
      refine ⟨58413983861801071238628041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38942655907867380825752027 58413983861801071238628041)
      ·
        refine ⟨43810487896350803428971031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58413983861801071238628041 43810487896350803428971031)
        ·
          refine ⟨65715731844526205143456547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43810487896350803428971031 65715731844526205143456547)
          ·
            refine ⟨98573597766789307715184821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65715731844526205143456547 98573597766789307715184821)
            ·
              refine ⟨9241274790636497598298577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98573597766789307715184821 9241274790636497598298577)
              ·
                refine ⟨6930956092977373198723933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9241274790636497598298577 6930956092977373198723933)
                ·
                  refine ⟨2599108534866514949521475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6930956092977373198723933 2599108534866514949521475)
                  ·
                    refine ⟨3898662802299772424282213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2599108534866514949521475 3898662802299772424282213)
                    ·
                      refine ⟨730999275431207329552915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3898662802299772424282213 730999275431207329552915)
                      ·
                        rfl

theorem cell23_1423616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_1423616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423616 prefixEnd_1423616 := by exact prefixLift 1423616
  have htrace : WordTrace (prefixWord ++ tailWord_1423616) baseStart_1423616 baseEnd_1423616 := by
    simpa [prefixWord, tailWord_1423616, baseEnd_1423616] using wordTrace_append hprefix tailTrace_1423616
  have hstable : (prefixWord ++ tailWord_1423616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423616).length < 2 ^ (prefixWord ++ tailWord_1423616).sum := by decide
  have hdescent : baseEnd_1423616 < baseStart_1423616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423626 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1423626 : Nat := 118140960795 + 1423626 * 2 ^ 59
def prefixEnd_1423626 : Nat := 4983230072969 + 3 ^ 40 * 1423626 * 2
def baseEnd_1423626 : Nat := 243668136745917430142623

theorem tailTrace_1423626 : CollatzResearch.WordTrace tailWord_1423626 prefixEnd_1423626 243668136745917430142623 := by
  unfold tailWord_1423626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12980976485113403202216683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34615937293635741872577821 12980976485113403202216683)
  ·
    refine ⟨19471464727670104803325025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12980976485113403202216683 19471464727670104803325025)
    ·
      refine ⟨14603598545752578602493769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19471464727670104803325025 14603598545752578602493769)
      ·
        refine ⟨10952698909314433951870327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14603598545752578602493769 10952698909314433951870327)
        ·
          refine ⟨16429048363971650927805491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10952698909314433951870327 16429048363971650927805491)
          ·
            refine ⟨24643572545957476391708237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16429048363971650927805491 24643572545957476391708237)
            ·
              refine ⟨9241339704734053646890589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24643572545957476391708237 9241339704734053646890589)
              ·
                refine ⟨3465502389275270117583971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9241339704734053646890589 3465502389275270117583971)
                ·
                  refine ⟨5198253583912905176375957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465502389275270117583971 5198253583912905176375957)
                  ·
                    refine ⟨243668136745917430142623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5198253583912905176375957 243668136745917430142623)
                    ·
                      rfl

theorem cell23_1423626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1423626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423626 prefixEnd_1423626 := by exact prefixLift 1423626
  have htrace : WordTrace (prefixWord ++ tailWord_1423626) baseStart_1423626 baseEnd_1423626 := by
    simpa [prefixWord, tailWord_1423626, baseEnd_1423626] using wordTrace_append hprefix tailTrace_1423626
  have hstable : (prefixWord ++ tailWord_1423626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423626).length < 2 ^ (prefixWord ++ tailWord_1423626).sum := by decide
  have hdescent : baseEnd_1423626 < baseStart_1423626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423650 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1423650 : Nat := 118140960795 + 1423650 * 2 ^ 59
def prefixEnd_1423650 : Nat := 4983230072969 + 3 ^ 40 * 1423650 * 2
def baseEnd_1423650 : Nat := 731016733773460196527759

theorem tailTrace_1423650 : CollatzResearch.WordTrace tailWord_1423650 prefixEnd_1423650 731016733773460196527759 := by
  unfold tailWord_1423650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12981195323091666226935101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34616520861577776605160269 12981195323091666226935101)
  ·
    refine ⟨4867948246159374835100663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12981195323091666226935101 4867948246159374835100663)
    ·
      refine ⟨7301922369239062252650995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867948246159374835100663 7301922369239062252650995)
      ·
        refine ⟨10952883553858593378976493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7301922369239062252650995 10952883553858593378976493)
        ·
          refine ⟨4107331332696972517116185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10952883553858593378976493 4107331332696972517116185)
          ·
            refine ⟨3080498499522729387837139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4107331332696972517116185 3080498499522729387837139)
            ·
              refine ⟨4620747749284094081755709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080498499522729387837139 4620747749284094081755709)
              ·
                refine ⟨1732780405981535280658391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4620747749284094081755709 1732780405981535280658391)
                ·
                  refine ⟨2599170608972302920987587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732780405981535280658391 2599170608972302920987587)
                  ·
                    refine ⟨3898755913458454381481381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2599170608972302920987587 3898755913458454381481381)
                    ·
                      refine ⟨731016733773460196527759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3898755913458454381481381 731016733773460196527759)
                      ·
                        rfl

theorem cell23_1423650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1423650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423650 prefixEnd_1423650 := by exact prefixLift 1423650
  have htrace : WordTrace (prefixWord ++ tailWord_1423650) baseStart_1423650 baseEnd_1423650 := by
    simpa [prefixWord, tailWord_1423650, baseEnd_1423650] using wordTrace_append hprefix tailTrace_1423650
  have hstable : (prefixWord ++ tailWord_1423650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423650).length < 2 ^ (prefixWord ++ tailWord_1423650).sum := by decide
  have hdescent : baseEnd_1423650 < baseStart_1423650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423667 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 1, 2, 2]
def baseStart_1423667 : Nat := 118140960795 + 1423667 * 2 ^ 59
def prefixEnd_1423667 : Nat := 4983230072969 + 3 ^ 40 * 1423667 * 2
def baseEnd_1423667 : Nat := 731025462944586630015181

theorem tailTrace_1423667 : CollatzResearch.WordTrace tailWord_1423667 prefixEnd_1423667 731025462944586630015181 := by
  unfold tailWord_1423667
  simp only [CollatzResearch.WordTrace]
  refine ⟨51925401333305076811109255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34616934222203384540739503 51925401333305076811109255)
  ·
    refine ⟨77888101999957615216663883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51925401333305076811109255 77888101999957615216663883)
    ·
      refine ⟨116832152999936422824995825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77888101999957615216663883 116832152999936422824995825)
      ·
        refine ⟨87624114749952317118746869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116832152999936422824995825 87624114749952317118746869)
        ·
          refine ⟨8214760757808029729882519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87624114749952317118746869 8214760757808029729882519)
          ·
            refine ⟨12322141136712044594823779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8214760757808029729882519 12322141136712044594823779)
            ·
              refine ⟨18483211705068066892235669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12322141136712044594823779 18483211705068066892235669)
              ·
                refine ⟨866400548675065635573547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18483211705068066892235669 866400548675065635573547)
                ·
                  refine ⟨1299600823012598453360321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866400548675065635573547 1299600823012598453360321)
                  ·
                    refine ⟨974700617259448840020241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1299600823012598453360321 974700617259448840020241)
                    ·
                      refine ⟨731025462944586630015181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974700617259448840020241 731025462944586630015181)
                      ·
                        rfl

theorem cell23_1423667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 2, 2].length) (baseStart_1423667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423667 prefixEnd_1423667 := by exact prefixLift 1423667
  have htrace : WordTrace (prefixWord ++ tailWord_1423667) baseStart_1423667 baseEnd_1423667 := by
    simpa [prefixWord, tailWord_1423667, baseEnd_1423667] using wordTrace_append hprefix tailTrace_1423667
  have hstable : (prefixWord ++ tailWord_1423667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423667).length < 2 ^ (prefixWord ++ tailWord_1423667).sum := by decide
  have hdescent : baseEnd_1423667 < baseStart_1423667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423683 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 3]
def baseStart_1423683 : Nat := 118140960795 + 1423683 * 2 ^ 59
def prefixEnd_1423683 : Nat := 4983230072969 + 3 ^ 40 * 1423683 * 2
def baseEnd_1423683 : Nat := 731033678635058567415107

theorem tailTrace_1423683 : CollatzResearch.WordTrace tailWord_1423683 prefixEnd_1423683 731033678635058567415107 := by
  unfold tailWord_1423683
  simp only [CollatzResearch.WordTrace]
  refine ⟨51925984901247111543691703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34617323267498074362461135 51925984901247111543691703)
  ·
    refine ⟨77888977351870667315537555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51925984901247111543691703 77888977351870667315537555)
    ·
      refine ⟨116833466027806000973306333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77888977351870667315537555 116833466027806000973306333)
      ·
        refine ⟨43812549760427250364989875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116833466027806000973306333 43812549760427250364989875)
        ·
          refine ⟨65718824640640875547484813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43812549760427250364989875 65718824640640875547484813)
          ·
            refine ⟨24644559240240328330306805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65718824640640875547484813 24644559240240328330306805)
            ·
              refine ⟨2310427428772530780966263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24644559240240328330306805 2310427428772530780966263)
              ·
                refine ⟨3465641143158796171449395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310427428772530780966263 3465641143158796171449395)
                ·
                  refine ⟨5198461714738194257174093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465641143158796171449395 5198461714738194257174093)
                  ·
                    refine ⟨1949423143026822846440285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5198461714738194257174093 1949423143026822846440285)
                    ·
                      refine ⟨731033678635058567415107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1949423143026822846440285 731033678635058567415107)
                      ·
                        rfl

theorem cell23_1423683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_1423683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423683 prefixEnd_1423683 := by exact prefixLift 1423683
  have htrace : WordTrace (prefixWord ++ tailWord_1423683) baseStart_1423683 baseEnd_1423683 := by
    simpa [prefixWord, tailWord_1423683, baseEnd_1423683] using wordTrace_append hprefix tailTrace_1423683
  have hstable : (prefixWord ++ tailWord_1423683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423683).length < 2 ^ (prefixWord ++ tailWord_1423683).sum := by decide
  have hdescent : baseEnd_1423683 < baseStart_1423683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423696 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_1423696 : Nat := 118140960795 + 1423696 * 2 ^ 59
def prefixEnd_1423696 : Nat := 4983230072969 + 3 ^ 40 * 1423696 * 2
def baseEnd_1423696 : Nat := 731040353883567016552547

theorem tailTrace_1423696 : CollatzResearch.WordTrace tailWord_1423696 prefixEnd_1423696 731040353883567016552547 := by
  unfold tailWord_1423696
  simp only [CollatzResearch.WordTrace]
  refine ⟨25963229525100007381957471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34617639366800009842609961 25963229525100007381957471)
  ·
    refine ⟨38944844287650011072936207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25963229525100007381957471 38944844287650011072936207)
    ·
      refine ⟨58417266431475016609404311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38944844287650011072936207 58417266431475016609404311)
      ·
        refine ⟨87625899647212524914106467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58417266431475016609404311 87625899647212524914106467)
        ·
          refine ⟨131438849470818787371159701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87625899647212524914106467 131438849470818787371159701)
          ·
            refine ⟨6161196068944630658023111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131438849470818787371159701 6161196068944630658023111)
            ·
              refine ⟨9241794103416945987034667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161196068944630658023111 9241794103416945987034667)
              ·
                refine ⟨13862691155125418980552001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9241794103416945987034667 13862691155125418980552001)
                ·
                  refine ⟨10397018366344064235414001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13862691155125418980552001 10397018366344064235414001)
                  ·
                    refine ⟨7797763774758048176560501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10397018366344064235414001 7797763774758048176560501)
                    ·
                      refine ⟨731040353883567016552547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7797763774758048176560501 731040353883567016552547)
                      ·
                        rfl

theorem cell23_1423696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_1423696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423696 prefixEnd_1423696 := by exact prefixLift 1423696
  have htrace : WordTrace (prefixWord ++ tailWord_1423696) baseStart_1423696 baseEnd_1423696 := by
    simpa [prefixWord, tailWord_1423696, baseEnd_1423696] using wordTrace_append hprefix tailTrace_1423696
  have hstable : (prefixWord ++ tailWord_1423696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423696).length < 2 ^ (prefixWord ++ tailWord_1423696).sum := by decide
  have hdescent : baseEnd_1423696 < baseStart_1423696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423700 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1423700 : Nat := 118140960795 + 1423700 * 2 ^ 59
def prefixEnd_1423700 : Nat := 4983230072969 + 3 ^ 40 * 1423700 * 2
def baseEnd_1423700 : Nat := 731042407806185000902529

theorem tailTrace_1423700 : CollatzResearch.WordTrace tailWord_1423700 prefixEnd_1423700 731042407806185000902529 := by
  unfold tailWord_1423700
  simp only [CollatzResearch.WordTrace]
  refine ⟨25963302471092761723530277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34617736628123682298040369 25963302471092761723530277)
  ·
    refine ⟨4868119213329892823161927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25963302471092761723530277 4868119213329892823161927)
    ·
      refine ⟨7302178819994839234742891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868119213329892823161927 7302178819994839234742891)
      ·
        refine ⟨10953268229992258852114337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302178819994839234742891 10953268229992258852114337)
        ·
          refine ⟨8214951172494194139085753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10953268229992258852114337 8214951172494194139085753)
          ·
            refine ⟨6161213379370645604314315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8214951172494194139085753 6161213379370645604314315)
            ·
              refine ⟨9241820069055968406471473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161213379370645604314315 9241820069055968406471473)
              ·
                refine ⟨6931365051791976304853605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9241820069055968406471473 6931365051791976304853605)
                ·
                  refine ⟨1299630947210995557160051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6931365051791976304853605 1299630947210995557160051)
                  ·
                    refine ⟨1949446420816493335740077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1299630947210995557160051 1949446420816493335740077)
                    ·
                      refine ⟨731042407806185000902529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1949446420816493335740077 731042407806185000902529)
                      ·
                        rfl

theorem cell23_1423700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1423700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423700 prefixEnd_1423700 := by exact prefixLift 1423700
  have htrace : WordTrace (prefixWord ++ tailWord_1423700) baseStart_1423700 baseEnd_1423700 := by
    simpa [prefixWord, tailWord_1423700, baseEnd_1423700] using wordTrace_append hprefix tailTrace_1423700
  have hstable : (prefixWord ++ tailWord_1423700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423700).length < 2 ^ (prefixWord ++ tailWord_1423700).sum := by decide
  have hdescent : baseEnd_1423700 < baseStart_1423700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423701 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_1423701 : Nat := 118140960795 + 1423701 * 2 ^ 59
def prefixEnd_1423701 : Nat := 4983230072969 + 3 ^ 40 * 1423701 * 2
def baseEnd_1423701 : Nat := 731042921286839496990025

theorem tailTrace_1423701 : CollatzResearch.WordTrace tailWord_1423701 prefixEnd_1423701 731042921286839496990025 := by
  unfold tailWord_1423701
  simp only [CollatzResearch.WordTrace]
  refine ⟨51926641415181900617846957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34617760943454600411897971 51926641415181900617846957)
  ·
    refine ⟨19472490530693212731692609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51926641415181900617846957 19472490530693212731692609)
    ·
      refine ⟨14604367898019909548769457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19472490530693212731692609 14604367898019909548769457)
      ·
        refine ⟨10953275923514932161577093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14604367898019909548769457 10953275923514932161577093)
        ·
          refine ⟨2053739235659049780295705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10953275923514932161577093 2053739235659049780295705)
          ·
            refine ⟨1540304426744287335221779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053739235659049780295705 1540304426744287335221779)
            ·
              refine ⟨2310456640116431002832669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540304426744287335221779 2310456640116431002832669)
              ·
                refine ⟨866421240043661626062251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2310456640116431002832669 866421240043661626062251)
                ·
                  refine ⟨1299631860065492439093377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866421240043661626062251 1299631860065492439093377)
                  ·
                    refine ⟨974723895049119329320033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1299631860065492439093377 974723895049119329320033)
                    ·
                      refine ⟨731042921286839496990025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974723895049119329320033 731042921286839496990025)
                      ·
                        rfl

theorem cell23_1423701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_1423701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423701 prefixEnd_1423701 := by exact prefixLift 1423701
  have htrace : WordTrace (prefixWord ++ tailWord_1423701) baseStart_1423701 baseEnd_1423701 := by
    simpa [prefixWord, tailWord_1423701, baseEnd_1423701] using wordTrace_append hprefix tailTrace_1423701
  have hstable : (prefixWord ++ tailWord_1423701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423701).length < 2 ^ (prefixWord ++ tailWord_1423701).sum := by decide
  have hdescent : baseEnd_1423701 < baseStart_1423701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423706 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1423706 : Nat := 118140960795 + 1423706 * 2 ^ 59
def prefixEnd_1423706 : Nat := 4983230072969 + 3 ^ 40 * 1423706 * 2
def baseEnd_1423706 : Nat := 731045488690111977427501

theorem tailTrace_1423706 : CollatzResearch.WordTrace tailWord_1423706 prefixEnd_1423706 731045488690111977427501 := by
  unfold tailWord_1423706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12981705945040946617944743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34617882520109190981185981 12981705945040946617944743)
  ·
    refine ⟨19472558917561419926917115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12981705945040946617944743 19472558917561419926917115)
    ·
      refine ⟨29208838376342129890375673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19472558917561419926917115 29208838376342129890375673)
      ·
        refine ⟨21906628782256597417781755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29208838376342129890375673 21906628782256597417781755)
        ·
          refine ⟨32859943173384896126672633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21906628782256597417781755 32859943173384896126672633)
          ·
            refine ⟨24644957380038672095004475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32859943173384896126672633 24644957380038672095004475)
            ·
              refine ⟨36967436070058008142506713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24644957380038672095004475 36967436070058008142506713)
              ·
                refine ⟨27725577052543506106880035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36967436070058008142506713 27725577052543506106880035)
                ·
                  refine ⟨41588365578815259160320053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27725577052543506106880035 41588365578815259160320053)
                  ·
                    refine ⟨3898909273013930546280005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41588365578815259160320053 3898909273013930546280005)
                    ·
                      refine ⟨731045488690111977427501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3898909273013930546280005 731045488690111977427501)
                      ·
                        rfl

theorem cell23_1423706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1423706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423706 prefixEnd_1423706 := by exact prefixLift 1423706
  have htrace : WordTrace (prefixWord ++ tailWord_1423706) baseStart_1423706 baseEnd_1423706 := by
    simpa [prefixWord, tailWord_1423706, baseEnd_1423706] using wordTrace_append hprefix tailTrace_1423706
  have hstable : (prefixWord ++ tailWord_1423706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423706).length < 2 ^ (prefixWord ++ tailWord_1423706).sum := by decide
  have hdescent : baseEnd_1423706 < baseStart_1423706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423723 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 3, 4, 2]
def baseStart_1423723 : Nat := 118140960795 + 1423723 * 2 ^ 59
def prefixEnd_1423723 : Nat := 4983230072969 + 3 ^ 40 * 1423723 * 2
def baseEnd_1423723 : Nat := 731054217861238410914923

theorem tailTrace_1423723 : CollatzResearch.WordTrace tailWord_1423723 prefixEnd_1423723 731054217861238410914923 := by
  unfold tailWord_1423723
  simp only [CollatzResearch.WordTrace]
  refine ⟨51927443821102198375147823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34618295880734798916765215 51927443821102198375147823)
  ·
    refine ⟨77891165731653297562721735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51927443821102198375147823 77891165731653297562721735)
    ·
      refine ⟨116836748597479946344082603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77891165731653297562721735 116836748597479946344082603)
      ·
        refine ⟨175255122896219919516123905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116836748597479946344082603 175255122896219919516123905)
        ·
          refine ⟨131441342172164939637092929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175255122896219919516123905 131441342172164939637092929)
          ·
            refine ⟨98581006629123704727819697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131441342172164939637092929 98581006629123704727819697)
            ·
              refine ⟨73935754971842778545864773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98581006629123704727819697 73935754971842778545864773)
              ·
                refine ⟨13862954057220520977349645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73935754971842778545864773 13862954057220520977349645)
                ·
                  refine ⟨5198607771457695366506117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13862954057220520977349645 5198607771457695366506117)
                  ·
                    refine ⟨974738957148317881219897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5198607771457695366506117 974738957148317881219897)
                    ·
                      refine ⟨731054217861238410914923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974738957148317881219897 731054217861238410914923)
                      ·
                        rfl

theorem cell23_1423723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4, 2].length) (baseStart_1423723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423723 prefixEnd_1423723 := by exact prefixLift 1423723
  have htrace : WordTrace (prefixWord ++ tailWord_1423723) baseStart_1423723 baseEnd_1423723 := by
    simpa [prefixWord, tailWord_1423723, baseEnd_1423723] using wordTrace_append hprefix tailTrace_1423723
  have hstable : (prefixWord ++ tailWord_1423723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423723).length < 2 ^ (prefixWord ++ tailWord_1423723).sum := by decide
  have hdescent : baseEnd_1423723 < baseStart_1423723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423740 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_1423740 : Nat := 118140960795 + 1423740 * 2 ^ 59
def prefixEnd_1423740 : Nat := 4983230072969 + 3 ^ 40 * 1423740 * 2
def baseEnd_1423740 : Nat := 731062947032364844402345

theorem tailTrace_1423740 : CollatzResearch.WordTrace tailWord_1423740 prefixEnd_1423740 731062947032364844402345 := by
  unfold tailWord_1423740
  simp only [CollatzResearch.WordTrace]
  refine ⟨25964031931020305139258337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34618709241360406852344449 25964031931020305139258337)
  ·
    refine ⟨19473023948265228854443753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25964031931020305139258337 19473023948265228854443753)
    ·
      refine ⟨14604767961198921640832815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19473023948265228854443753 14604767961198921640832815)
      ·
        refine ⟨21907151941798382461249223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604767961198921640832815 21907151941798382461249223)
        ·
          refine ⟨32860727912697573691873835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907151941798382461249223 32860727912697573691873835)
          ·
            refine ⟨49291091869046360537810753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32860727912697573691873835 49291091869046360537810753)
            ·
              refine ⟨36968318901784770403358065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49291091869046360537810753 36968318901784770403358065)
              ·
                refine ⟨27726239176338577802518549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36968318901784770403358065 27726239176338577802518549)
                ·
                  refine ⟨1299667461390870834493057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27726239176338577802518549 1299667461390870834493057)
                  ·
                    refine ⟨974750596043153125869793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1299667461390870834493057 974750596043153125869793)
                    ·
                      refine ⟨731062947032364844402345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974750596043153125869793 731062947032364844402345)
                      ·
                        rfl

theorem cell23_1423740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_1423740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423740 prefixEnd_1423740 := by exact prefixLift 1423740
  have htrace : WordTrace (prefixWord ++ tailWord_1423740) baseStart_1423740 baseEnd_1423740 := by
    simpa [prefixWord, tailWord_1423740, baseEnd_1423740] using wordTrace_append hprefix tailTrace_1423740
  have hstable : (prefixWord ++ tailWord_1423740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423740).length < 2 ^ (prefixWord ++ tailWord_1423740).sum := by decide
  have hdescent : baseEnd_1423740 < baseStart_1423740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423823 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 7, 4]
def baseStart_1423823 : Nat := 118140960795 + 1423823 * 2 ^ 59
def prefixEnd_1423823 : Nat := 4983230072969 + 3 ^ 40 * 1423823 * 2
def baseEnd_1423823 : Nat := 243701855308896006554821

theorem tailTrace_1423823 : CollatzResearch.WordTrace tailWord_1423823 prefixEnd_1423823 243701855308896006554821 := by
  unfold tailWord_1423823
  simp only [CollatzResearch.WordTrace]
  refine ⟨51931091120739915453788123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34620727413826610302525415 51931091120739915453788123)
  ·
    refine ⟨77896636681109873180682185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51931091120739915453788123 77896636681109873180682185)
    ·
      refine ⟨58422477510832404885511639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77896636681109873180682185 58422477510832404885511639)
      ·
        refine ⟨87633716266248607328267459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58422477510832404885511639 87633716266248607328267459)
        ·
          refine ⟨131450574399372910992401189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87633716266248607328267459 131450574399372910992401189)
          ·
            refine ⟨24646982699882420811075223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131450574399372910992401189 24646982699882420811075223)
            ·
              refine ⟨36970474049823631216612835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24646982699882420811075223 36970474049823631216612835)
              ·
                refine ⟨55455711074735446824919253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36970474049823631216612835 55455711074735446824919253)
                ·
                  refine ⟨1299743228314112034959045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 55455711074735446824919253 1299743228314112034959045)
                  ·
                    refine ⟨243701855308896006554821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299743228314112034959045 243701855308896006554821)
                    ·
                      rfl

theorem cell23_1423823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_1423823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423823 prefixEnd_1423823 := by exact prefixLift 1423823
  have htrace : WordTrace (prefixWord ++ tailWord_1423823) baseStart_1423823 baseEnd_1423823 := by
    simpa [prefixWord, tailWord_1423823, baseEnd_1423823] using wordTrace_append hprefix tailTrace_1423823
  have hstable : (prefixWord ++ tailWord_1423823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423823).length < 2 ^ (prefixWord ++ tailWord_1423823).sum := by decide
  have hdescent : baseEnd_1423823 < baseStart_1423823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423840 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 3, 4]
def baseStart_1423840 : Nat := 118140960795 + 1423840 * 2 ^ 59
def prefixEnd_1423840 : Nat := 4983230072969 + 3 ^ 40 * 1423840 * 2
def baseEnd_1423840 : Nat := 243704765032604817717295

theorem tailTrace_1423840 : CollatzResearch.WordTrace tailWord_1423840 prefixEnd_1423840 243704765032604817717295 := by
  unfold tailWord_1423840
  simp only [CollatzResearch.WordTrace]
  refine ⟨25965855580839163678578487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34621140774452218238104649 25965855580839163678578487)
  ·
    refine ⟨38948783371258745517867731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25965855580839163678578487 38948783371258745517867731)
    ·
      refine ⟨58423175056888118276801597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38948783371258745517867731 58423175056888118276801597)
      ·
        refine ⟨21908690646333044353800599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58423175056888118276801597 21908690646333044353800599)
        ·
          refine ⟨32863035969499566530700899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21908690646333044353800599 32863035969499566530700899)
          ·
            refine ⟨49294553954249349796051349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32863035969499566530700899 49294553954249349796051349)
            ·
              refine ⟨2310682216605438271689907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49294553954249349796051349 2310682216605438271689907)
              ·
                refine ⟨3466023324908157407534861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310682216605438271689907 3466023324908157407534861)
                ·
                  refine ⟨1299758746840559027825573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3466023324908157407534861 1299758746840559027825573)
                  ·
                    refine ⟨243704765032604817717295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299758746840559027825573 243704765032604817717295)
                    ·
                      rfl

theorem cell23_1423840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_1423840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423840 prefixEnd_1423840 := by exact prefixLift 1423840
  have htrace : WordTrace (prefixWord ++ tailWord_1423840) baseStart_1423840 baseEnd_1423840 := by
    simpa [prefixWord, tailWord_1423840, baseEnd_1423840] using wordTrace_append hprefix tailTrace_1423840
  have hstable : (prefixWord ++ tailWord_1423840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423840).length < 2 ^ (prefixWord ++ tailWord_1423840).sum := by decide
  have hdescent : baseEnd_1423840 < baseStart_1423840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423850 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1423850 : Nat := 118140960795 + 1423850 * 2 ^ 59
def prefixEnd_1423850 : Nat := 4983230072969 + 3 ^ 40 * 1423850 * 2
def baseEnd_1423850 : Nat := 731119429904359414026839

theorem tailTrace_1423850 : CollatzResearch.WordTrace tailWord_1423850 prefixEnd_1423850 731119429904359414026839 := by
  unfold tailWord_1423850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983018972910524766255251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34621383927761399376680669 12983018972910524766255251)
  ·
    refine ⟨19474528459365787149382877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12983018972910524766255251 19474528459365787149382877)
    ·
      refine ⟨7302948172262170181018579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19474528459365787149382877 7302948172262170181018579)
      ·
        refine ⟨10954422258393255271527869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302948172262170181018579 10954422258393255271527869)
        ·
          refine ⟨4107908346897470726822951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10954422258393255271527869 4107908346897470726822951)
          ·
            refine ⟨6161862520346206090234427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107908346897470726822951 6161862520346206090234427)
            ·
              refine ⟨9242793780519309135351641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161862520346206090234427 9242793780519309135351641)
              ·
                refine ⟨6932095335389481851513731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9242793780519309135351641 6932095335389481851513731)
                ·
                  refine ⟨10398143003084222777270597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932095335389481851513731 10398143003084222777270597)
                  ·
                    refine ⟨1949651813078291770738237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10398143003084222777270597 1949651813078291770738237)
                    ·
                      refine ⟨731119429904359414026839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1949651813078291770738237 731119429904359414026839)
                      ·
                        rfl

theorem cell23_1423850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1423850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423850 prefixEnd_1423850 := by exact prefixLift 1423850
  have htrace : WordTrace (prefixWord ++ tailWord_1423850) baseStart_1423850 baseEnd_1423850 := by
    simpa [prefixWord, tailWord_1423850, baseEnd_1423850] using wordTrace_append hprefix tailTrace_1423850
  have hstable : (prefixWord ++ tailWord_1423850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423850).length < 2 ^ (prefixWord ++ tailWord_1423850).sum := by decide
  have hdescent : baseEnd_1423850 < baseStart_1423850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423903 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1423903 : Nat := 118140960795 + 1423903 * 2 ^ 59
def prefixEnd_1423903 : Nat := 4983230072969 + 3 ^ 40 * 1423903 * 2
def baseEnd_1423903 : Nat := 731146644379047706664095

theorem tailTrace_1423903 : CollatzResearch.WordTrace tailWord_1423903 prefixEnd_1423903 731146644379047706664095 := by
  unfold tailWord_1423903
  simp only [CollatzResearch.WordTrace]
  refine ⟨51934008960450089116700363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34622672640300059411133575 51934008960450089116700363)
  ·
    refine ⟨77901013440675133675050545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51934008960450089116700363 77901013440675133675050545)
    ·
      refine ⟨58425760080506350256287909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77901013440675133675050545 58425760080506350256287909)
      ·
        refine ⟨10954830015094940673053983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58425760080506350256287909 10954830015094940673053983)
        ·
          refine ⟨16432245022642411009580975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10954830015094940673053983 16432245022642411009580975)
          ·
            refine ⟨24648367533963616514371463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16432245022642411009580975 24648367533963616514371463)
            ·
              refine ⟨36972551300945424771557195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24648367533963616514371463 36972551300945424771557195)
              ·
                refine ⟨55458826951418137157335793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36972551300945424771557195 55458826951418137157335793)
                ·
                  refine ⟨41594120213563602868001845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55458826951418137157335793 41594120213563602868001845)
                  ·
                    refine ⟨3899448770021587768875173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41594120213563602868001845 3899448770021587768875173)
                    ·
                      refine ⟨731146644379047706664095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3899448770021587768875173 731146644379047706664095)
                      ·
                        rfl

theorem cell23_1423903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1423903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423903 prefixEnd_1423903 := by exact prefixLift 1423903
  have htrace : WordTrace (prefixWord ++ tailWord_1423903) baseStart_1423903 baseEnd_1423903 := by
    simpa [prefixWord, tailWord_1423903, baseEnd_1423903] using wordTrace_append hprefix tailTrace_1423903
  have hstable : (prefixWord ++ tailWord_1423903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423903).length < 2 ^ (prefixWord ++ tailWord_1423903).sum := by decide
  have hdescent : baseEnd_1423903 < baseStart_1423903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423904 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 6]
def baseStart_1423904 : Nat := 118140960795 + 1423904 * 2 ^ 59
def prefixEnd_1423904 : Nat := 4983230072969 + 3 ^ 40 * 1423904 * 2
def baseEnd_1423904 : Nat := 81238573095522466972399

theorem tailTrace_1423904 : CollatzResearch.WordTrace tailWord_1423904 prefixEnd_1423904 81238573095522466972399 := by
  unfold tailWord_1423904
  simp only [CollatzResearch.WordTrace]
  refine ⟨25967022716723233143743383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34622696955630977524991177 25967022716723233143743383)
  ·
    refine ⟨38950534075084849715615075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25967022716723233143743383 38950534075084849715615075)
    ·
      refine ⟨58425801112627274573422613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38950534075084849715615075 58425801112627274573422613)
      ·
        refine ⟨2738709427154403495629185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58425801112627274573422613 2738709427154403495629185)
        ·
          refine ⟨2054032070365802621721889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2738709427154403495629185 2054032070365802621721889)
          ·
            refine ⟨1540524052774351966291417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2054032070365802621721889 1540524052774351966291417)
            ·
              refine ⟨1155393039580763974718563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540524052774351966291417 1155393039580763974718563)
              ·
                refine ⟨1733089559371145962077845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155393039580763974718563 1733089559371145962077845)
                ·
                  refine ⟨81238573095522466972399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1733089559371145962077845 81238573095522466972399)
                  ·
                    rfl

theorem cell23_1423904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 6].length) (baseStart_1423904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423904 prefixEnd_1423904 := by exact prefixLift 1423904
  have htrace : WordTrace (prefixWord ++ tailWord_1423904) baseStart_1423904 baseEnd_1423904 := by
    simpa [prefixWord, tailWord_1423904, baseEnd_1423904] using wordTrace_append hprefix tailTrace_1423904
  have hstable : (prefixWord ++ tailWord_1423904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423904).length < 2 ^ (prefixWord ++ tailWord_1423904).sum := by decide
  have hdescent : baseEnd_1423904 < baseStart_1423904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423920 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 6, 2]
def baseStart_1423920 : Nat := 118140960795 + 1423920 * 2 ^ 59
def prefixEnd_1423920 : Nat := 4983230072969 + 3 ^ 40 * 1423920 * 2
def baseEnd_1423920 : Nat := 731155373550174140151517

theorem tailTrace_1423920 : CollatzResearch.WordTrace tailWord_1423920 prefixEnd_1423920 731155373550174140151517 := by
  unfold tailWord_1423920
  simp only [CollatzResearch.WordTrace]
  refine ⟨25967314500694250510034607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34623086000925667346712809 25967314500694250510034607)
  ·
    refine ⟨38950971751041375765051911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25967314500694250510034607 38950971751041375765051911)
    ·
      refine ⟨58426457626562063647577867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38950971751041375765051911 58426457626562063647577867)
      ·
        refine ⟨87639686439843095471366801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58426457626562063647577867 87639686439843095471366801)
        ·
          refine ⟨65729764829882321603525101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87639686439843095471366801 65729764829882321603525101)
          ·
            refine ⟨24648661811205870601321913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65729764829882321603525101 24648661811205870601321913)
            ·
              refine ⟨18486496358404402950991435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24648661811205870601321913 18486496358404402950991435)
              ·
                refine ⟨27729744537606604426487153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18486496358404402950991435 27729744537606604426487153)
                ·
                  refine ⟨20797308403204953319865365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27729744537606604426487153 20797308403204953319865365)
                  ·
                    refine ⟨974873831400232186868689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20797308403204953319865365 974873831400232186868689)
                    ·
                      refine ⟨731155373550174140151517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974873831400232186868689 731155373550174140151517)
                      ·
                        rfl

theorem cell23_1423920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 6, 2].length) (baseStart_1423920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423920 prefixEnd_1423920 := by exact prefixLift 1423920
  have htrace : WordTrace (prefixWord ++ tailWord_1423920) baseStart_1423920 baseEnd_1423920 := by
    simpa [prefixWord, tailWord_1423920, baseEnd_1423920] using wordTrace_append hprefix tailTrace_1423920
  have hstable : (prefixWord ++ tailWord_1423920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423920).length < 2 ^ (prefixWord ++ tailWord_1423920).sum := by decide
  have hdescent : baseEnd_1423920 < baseStart_1423920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423930 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_1423930 : Nat := 118140960795 + 1423930 * 2 ^ 59
def prefixEnd_1423930 : Nat := 4983230072969 + 3 ^ 40 * 1423930 * 2
def baseEnd_1423930 : Nat := 243720169452239700342157

theorem tailTrace_1423930 : CollatzResearch.WordTrace tailWord_1423930 prefixEnd_1423930 243720169452239700342157 := by
  unfold tailWord_1423930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983748432838068181983311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34623329154234848485288829 12983748432838068181983311)
  ·
    refine ⟨19475622649257102272974967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12983748432838068181983311 19475622649257102272974967)
    ·
      refine ⟨29213433973885653409462451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19475622649257102272974967 29213433973885653409462451)
      ·
        refine ⟨43820150960828480114193677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29213433973885653409462451 43820150960828480114193677)
        ·
          refine ⟨16432556610310680042822629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43820150960828480114193677 16432556610310680042822629)
          ·
            refine ⟨3081104364433252508029243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16432556610310680042822629 3081104364433252508029243)
            ·
              refine ⟨4621656546649878762043865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081104364433252508029243 4621656546649878762043865)
              ·
                refine ⟨3466242409987409071532899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621656546649878762043865 3466242409987409071532899)
                ·
                  refine ⟨5199363614981113607299349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466242409987409071532899 5199363614981113607299349)
                  ·
                    refine ⟨243720169452239700342157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5199363614981113607299349 243720169452239700342157)
                    ·
                      rfl

theorem cell23_1423930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_1423930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423930 prefixEnd_1423930 := by exact prefixLift 1423930
  have htrace : WordTrace (prefixWord ++ tailWord_1423930) baseStart_1423930 baseEnd_1423930 := by
    simpa [prefixWord, tailWord_1423930, baseEnd_1423930] using wordTrace_append hprefix tailTrace_1423930
  have hstable : (prefixWord ++ tailWord_1423930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423930).length < 2 ^ (prefixWord ++ tailWord_1423930).sum := by decide
  have hdescent : baseEnd_1423930 < baseStart_1423930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423943 : List Nat := [1, 1, 4, 1, 4, 12]
def baseStart_1423943 : Nat := 118140960795 + 1423943 * 2 ^ 59
def prefixEnd_1423943 : Nat := 4983230072969 + 3 ^ 40 * 1423943 * 2
def baseEnd_1423943 : Nat := 3008918451050319136477

theorem tailTrace_1423943 : CollatzResearch.WordTrace tailWord_1423943 prefixEnd_1423943 3008918451050319136477 := by
  unfold tailWord_1423943
  simp only [CollatzResearch.WordTrace]
  refine ⟨51935467880305175948156483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34623645253536783965437655 51935467880305175948156483)
  ·
    refine ⟨77903201820457763922234725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51935467880305175948156483 77903201820457763922234725)
    ·
      refine ⟨14606850341335830735419011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77903201820457763922234725 14606850341335830735419011)
      ·
        refine ⟨21910275512003746103128517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606850341335830735419011 21910275512003746103128517)
        ·
          refine ⟨4108176658500702394336597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21910275512003746103128517 4108176658500702394336597)
          ·
            refine ⟨3008918451050319136477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4108176658500702394336597 3008918451050319136477)
            ·
              rfl

theorem cell23_1423943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 12].length) (baseStart_1423943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423943 prefixEnd_1423943 := by exact prefixLift 1423943
  have htrace : WordTrace (prefixWord ++ tailWord_1423943) baseStart_1423943 baseEnd_1423943 := by
    simpa [prefixWord, tailWord_1423943, baseEnd_1423943] using wordTrace_append hprefix tailTrace_1423943
  have hstable : (prefixWord ++ tailWord_1423943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423943).length < 2 ^ (prefixWord ++ tailWord_1423943).sum := by decide
  have hdescent : baseEnd_1423943 < baseStart_1423943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423954 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_1423954 : Nat := 118140960795 + 1423954 * 2 ^ 59
def prefixEnd_1423954 : Nat := 4983230072969 + 3 ^ 40 * 1423954 * 2
def baseEnd_1423954 : Nat := 731172831892427007126361

theorem tailTrace_1423954 : CollatzResearch.WordTrace tailWord_1423954 prefixEnd_1423954 731172831892427007126361 := by
  unfold tailWord_1423954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983967270816331206701729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34623912722176883217871277 12983967270816331206701729)
  ·
    refine ⟨9737975453112248405026297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12983967270816331206701729 9737975453112248405026297)
    ·
      refine ⟨7303481589834186303769723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9737975453112248405026297 7303481589834186303769723)
      ·
        refine ⟨10955222384751279455654585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7303481589834186303769723 10955222384751279455654585)
        ·
          refine ⟨8216416788563459591740939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10955222384751279455654585 8216416788563459591740939)
          ·
            refine ⟨12324625182845189387611409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216416788563459591740939 12324625182845189387611409)
            ·
              refine ⟨9243468887133892040708557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12324625182845189387611409 9243468887133892040708557)
              ·
                refine ⟨3466300832675209515265709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9243468887133892040708557 3466300832675209515265709)
                ·
                  refine ⟨1299862812253203568224641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3466300832675209515265709 1299862812253203568224641)
                  ·
                    refine ⟨974897109189902676168481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1299862812253203568224641 974897109189902676168481)
                    ·
                      refine ⟨731172831892427007126361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974897109189902676168481 731172831892427007126361)
                      ·
                        rfl

theorem cell23_1423954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_1423954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1423954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1423954 prefixEnd_1423954 := by exact prefixLift 1423954
  have htrace : WordTrace (prefixWord ++ tailWord_1423954) baseStart_1423954 baseEnd_1423954 := by
    simpa [prefixWord, tailWord_1423954, baseEnd_1423954] using wordTrace_append hprefix tailTrace_1423954
  have hstable : (prefixWord ++ tailWord_1423954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423954).length < 2 ^ (prefixWord ++ tailWord_1423954).sum := by decide
  have hdescent : baseEnd_1423954 < baseStart_1423954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424004 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1424004 : Nat := 118140960795 + 1424004 * 2 ^ 59
def prefixEnd_1424004 : Nat := 4983230072969 + 3 ^ 40 * 1424004 * 2
def baseEnd_1424004 : Nat := 731198505925151811501131

theorem tailTrace_1424004 : CollatzResearch.WordTrace tailWord_1424004 prefixEnd_1424004 731198505925151811501131 := by
  unfold tailWord_1424004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25968846366542091683063533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34625128488722788910751377 25968846366542091683063533)
  ·
    refine ⟨9738317387453284381148825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25968846366542091683063533 9738317387453284381148825)
    ·
      refine ⟨7303738040589963285861619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9738317387453284381148825 7303738040589963285861619)
      ·
        refine ⟨10955607060884944928792429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7303738040589963285861619 10955607060884944928792429)
        ·
          refine ⟨4108352647831854348297161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10955607060884944928792429 4108352647831854348297161)
          ·
            refine ⟨3081264485873890761222871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108352647831854348297161 3081264485873890761222871)
            ·
              refine ⟨4621896728810836141834307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081264485873890761222871 4621896728810836141834307)
              ·
                refine ⟨6932845093216254212751461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621896728810836141834307 6932845093216254212751461)
                ·
                  refine ⟨1299908454978047664890899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6932845093216254212751461 1299908454978047664890899)
                  ·
                    refine ⟨1949862682467071497336349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1299908454978047664890899 1949862682467071497336349)
                    ·
                      refine ⟨731198505925151811501131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1949862682467071497336349 731198505925151811501131)
                      ·
                        rfl

theorem cell23_1424004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1424004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424004 prefixEnd_1424004 := by exact prefixLift 1424004
  have htrace : WordTrace (prefixWord ++ tailWord_1424004) baseStart_1424004 baseEnd_1424004 := by
    simpa [prefixWord, tailWord_1424004, baseEnd_1424004] using wordTrace_append hprefix tailTrace_1424004
  have hstable : (prefixWord ++ tailWord_1424004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424004).length < 2 ^ (prefixWord ++ tailWord_1424004).sum := by decide
  have hdescent : baseEnd_1424004 < baseStart_1424004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424060 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1424060 : Nat := 118140960795 + 1424060 * 2 ^ 59
def prefixEnd_1424060 : Nat := 4983230072969 + 3 ^ 40 * 1424060 * 2
def baseEnd_1424060 : Nat := 731227260841803592400873

theorem tailTrace_1424060 : CollatzResearch.WordTrace tailWord_1424060 prefixEnd_1424060 731227260841803592400873 := by
  unfold tailWord_1424060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969867610440652465082817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34626490147254203286777089 25969867610440652465082817)
  ·
    refine ⟨19477400707830489348812113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25969867610440652465082817 19477400707830489348812113)
    ·
      refine ⟨14608050530872867011609085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19477400707830489348812113 14608050530872867011609085)
      ·
        refine ⟨5478018949077325129353407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14608050530872867011609085 5478018949077325129353407)
        ·
          refine ⟨8217028423615987694030111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5478018949077325129353407 8217028423615987694030111)
          ·
            refine ⟨12325542635423981541045167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8217028423615987694030111 12325542635423981541045167)
            ·
              refine ⟨18488313953135972311567751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325542635423981541045167 18488313953135972311567751)
              ·
                refine ⟨27732470929703958467351627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18488313953135972311567751 27732470929703958467351627)
                ·
                  refine ⟨41598706394555937701027441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27732470929703958467351627 41598706394555937701027441)
                  ·
                    refine ⟨31199029795916953275770581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41598706394555937701027441 31199029795916953275770581)
                    ·
                      refine ⟨731227260841803592400873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31199029795916953275770581 731227260841803592400873)
                      ·
                        rfl

theorem cell23_1424060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1424060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424060 prefixEnd_1424060 := by exact prefixLift 1424060
  have htrace : WordTrace (prefixWord ++ tailWord_1424060) baseStart_1424060 baseEnd_1424060 := by
    simpa [prefixWord, tailWord_1424060, baseEnd_1424060] using wordTrace_append hprefix tailTrace_1424060
  have hstable : (prefixWord ++ tailWord_1424060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424060).length < 2 ^ (prefixWord ++ tailWord_1424060).sum := by decide
  have hdescent : baseEnd_1424060 < baseStart_1424060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424078 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_1424078 : Nat := 118140960795 + 1424078 * 2 ^ 59
def prefixEnd_1424078 : Nat := 4983230072969 + 3 ^ 40 * 1424078 * 2
def baseEnd_1424078 : Nat := 731236503493584521975791

theorem tailTrace_1424078 : CollatzResearch.WordTrace tailWord_1424078 prefixEnd_1424078 731236503493584521975791 := by
  unfold tailWord_1424078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492548966852011750540111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34626927823210729336213925 6492548966852011750540111)
  ·
    refine ⟨9738823450278017625810167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6492548966852011750540111 9738823450278017625810167)
    ·
      refine ⟨14608235175417026438715251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9738823450278017625810167 14608235175417026438715251)
      ·
        refine ⟨21912352763125539658072877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14608235175417026438715251 21912352763125539658072877)
        ·
          refine ⟨8217132286172077371777329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21912352763125539658072877 8217132286172077371777329)
          ·
            refine ⟨6162849214629058028832997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8217132286172077371777329 6162849214629058028832997)
            ·
              refine ⟨1155534227742948380406187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6162849214629058028832997 1155534227742948380406187)
              ·
                refine ⟨1733301341614422570609281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155534227742948380406187 1733301341614422570609281)
                ·
                  refine ⟨1299976006210816927956961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733301341614422570609281 1299976006210816927956961)
                  ·
                    refine ⟨974982004658112695967721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1299976006210816927956961 974982004658112695967721)
                    ·
                      refine ⟨731236503493584521975791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 974982004658112695967721 731236503493584521975791)
                      ·
                        rfl

theorem cell23_1424078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_1424078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424078 prefixEnd_1424078 := by exact prefixLift 1424078
  have htrace : WordTrace (prefixWord ++ tailWord_1424078) baseStart_1424078 baseEnd_1424078 := by
    simpa [prefixWord, tailWord_1424078, baseEnd_1424078] using wordTrace_append hprefix tailTrace_1424078
  have hstable : (prefixWord ++ tailWord_1424078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424078).length < 2 ^ (prefixWord ++ tailWord_1424078).sum := by decide
  have hdescent : baseEnd_1424078 < baseStart_1424078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424090 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1424090 : Nat := 118140960795 + 1424090 * 2 ^ 59
def prefixEnd_1424090 : Nat := 4983230072969 + 3 ^ 40 * 1424090 * 2
def baseEnd_1424090 : Nat := 731242665261438475025735

theorem tailTrace_1424090 : CollatzResearch.WordTrace tailWord_1424090 prefixEnd_1424090 731242665261438475025735 := by
  unfold tailWord_1424090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985207352693155013439431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34627219607181746702505149 12985207352693155013439431)
  ·
    refine ⟨19477811029039732520159147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985207352693155013439431 19477811029039732520159147)
    ·
      refine ⟨29216716543559598780238721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19477811029039732520159147 29216716543559598780238721)
      ·
        refine ⟨21912537407669699085179041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29216716543559598780238721 21912537407669699085179041)
        ·
          refine ⟨16434403055752274313884281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21912537407669699085179041 16434403055752274313884281)
          ·
            refine ⟨12325802291814205735413211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16434403055752274313884281 12325802291814205735413211)
            ·
              refine ⟨18488703437721308603119817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325802291814205735413211 18488703437721308603119817)
              ·
                refine ⟨13866527578290981452339863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18488703437721308603119817 13866527578290981452339863)
                ·
                  refine ⟨20799791367436472178509795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13866527578290981452339863 20799791367436472178509795)
                  ·
                    refine ⟨31199687051154708267764693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20799791367436472178509795 31199687051154708267764693)
                    ·
                      refine ⟨731242665261438475025735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31199687051154708267764693 731242665261438475025735)
                      ·
                        rfl

theorem cell23_1424090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1424090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424090 prefixEnd_1424090 := by exact prefixLift 1424090
  have htrace : WordTrace (prefixWord ++ tailWord_1424090) baseStart_1424090 baseEnd_1424090 := by
    simpa [prefixWord, tailWord_1424090, baseEnd_1424090] using wordTrace_append hprefix tailTrace_1424090
  have hstable : (prefixWord ++ tailWord_1424090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424090).length < 2 ^ (prefixWord ++ tailWord_1424090).sum := by decide
  have hdescent : baseEnd_1424090 < baseStart_1424090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424097 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1424097 : Nat := 118140960795 + 1424097 * 2 ^ 59
def prefixEnd_1424097 : Nat := 4983230072969 + 3 ^ 40 * 1424097 * 2
def baseEnd_1424097 : Nat := 243748753208673315879401

theorem tailTrace_1424097 : CollatzResearch.WordTrace tailWord_1424097 prefixEnd_1424097 243748753208673315879401 := by
  unfold tailWord_1424097
  simp only [CollatzResearch.WordTrace]
  refine ⟨51941084721747260249262545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34627389814498173499508363 51941084721747260249262545)
  ·
    refine ⟨38955813541310445186946909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51941084721747260249262545 38955813541310445186946909)
    ·
      refine ⟨14608430077991416945105091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38955813541310445186946909 14608430077991416945105091)
      ·
        refine ⟨21912645116987125417657637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14608430077991416945105091 21912645116987125417657637)
        ·
          refine ⟨4108620959435086015810807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21912645116987125417657637 4108620959435086015810807)
          ·
            refine ⟨6162931439152629023716211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4108620959435086015810807 6162931439152629023716211)
            ·
              refine ⟨9244397158728943535574317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162931439152629023716211 9244397158728943535574317)
              ·
                refine ⟨3466648934523353825840369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9244397158728943535574317 3466648934523353825840369)
                ·
                  refine ⟨2599986700892515369380277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3466648934523353825840369 2599986700892515369380277)
                  ·
                    refine ⟨243748753208673315879401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2599986700892515369380277 243748753208673315879401)
                    ·
                      rfl

theorem cell23_1424097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1424097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424097 prefixEnd_1424097 := by exact prefixLift 1424097
  have htrace : WordTrace (prefixWord ++ tailWord_1424097) baseStart_1424097 baseEnd_1424097 := by
    simpa [prefixWord, tailWord_1424097, baseEnd_1424097] using wordTrace_append hprefix tailTrace_1424097
  have hstable : (prefixWord ++ tailWord_1424097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424097).length < 2 ^ (prefixWord ++ tailWord_1424097).sum := by decide
  have hdescent : baseEnd_1424097 < baseStart_1424097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424120 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1424120 : Nat := 118140960795 + 1424120 * 2 ^ 59
def prefixEnd_1424120 : Nat := 4983230072969 + 3 ^ 40 * 1424120 * 2
def baseEnd_1424120 : Nat := 731258069681073357650597

theorem tailTrace_1424120 : CollatzResearch.WordTrace tailWord_1424120 prefixEnd_1424120 731258069681073357650597 := by
  unfold tailWord_1424120
  simp only [CollatzResearch.WordTrace]
  refine ⟨25970961800331967588674907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34627949067109290118233209 25970961800331967588674907)
  ·
    refine ⟨38956442700497951383012361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25970961800331967588674907 38956442700497951383012361)
    ·
      refine ⟨29217332025373463537259271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38956442700497951383012361 29217332025373463537259271)
      ·
        refine ⟨43825998038060195305888907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29217332025373463537259271 43825998038060195305888907)
        ·
          refine ⟨65738997057090292958833361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43825998038060195305888907 65738997057090292958833361)
          ·
            refine ⟨49304247792817719719125021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65738997057090292958833361 49304247792817719719125021)
            ·
              refine ⟨18489092922306644894671883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49304247792817719719125021 18489092922306644894671883)
              ·
                refine ⟨27733639383459967342007825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18489092922306644894671883 27733639383459967342007825)
                ·
                  refine ⟨20800229537594975506505869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27733639383459967342007825 20800229537594975506505869)
                  ·
                    refine ⟨7800086076598115814939701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20800229537594975506505869 7800086076598115814939701)
                    ·
                      refine ⟨731258069681073357650597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7800086076598115814939701 731258069681073357650597)
                      ·
                        rfl

theorem cell23_1424120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1424120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424120 prefixEnd_1424120 := by exact prefixLift 1424120
  have htrace : WordTrace (prefixWord ++ tailWord_1424120) baseStart_1424120 baseEnd_1424120 := by
    simpa [prefixWord, tailWord_1424120, baseEnd_1424120] using wordTrace_append hprefix tailTrace_1424120
  have hstable : (prefixWord ++ tailWord_1424120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424120).length < 2 ^ (prefixWord ++ tailWord_1424120).sum := by decide
  have hdescent : baseEnd_1424120 < baseStart_1424120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424127 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 3, 4]
def baseStart_1424127 : Nat := 118140960795 + 1424127 * 2 ^ 59
def prefixEnd_1424127 : Nat := 4983230072969 + 3 ^ 40 * 1424127 * 2
def baseEnd_1424127 : Nat := 243753888015218276754355

theorem tailTrace_1424127 : CollatzResearch.WordTrace tailWord_1424127 prefixEnd_1424127 243753888015218276754355 := by
  unfold tailWord_1424127
  simp only [CollatzResearch.WordTrace]
  refine ⟨51942178911638575372854635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34628119274425716915236423 51942178911638575372854635)
  ·
    refine ⟨77913268367457863059281953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51942178911638575372854635 77913268367457863059281953)
    ·
      refine ⟨58434951275593397294461465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77913268367457863059281953 58434951275593397294461465)
      ·
        refine ⟨43826213456695047970846099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58434951275593397294461465 43826213456695047970846099)
        ·
          refine ⟨65739320185042571956269149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43826213456695047970846099 65739320185042571956269149)
          ·
            refine ⟨24652245069390964483600931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65739320185042571956269149 24652245069390964483600931)
            ·
              refine ⟨36978367604086446725401397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24652245069390964483600931 36978367604086446725401397)
              ·
                refine ⟨3466721962883104380506381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36978367604086446725401397 3466721962883104380506381)
                ·
                  refine ⟨1300020736081164142689893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3466721962883104380506381 1300020736081164142689893)
                  ·
                    refine ⟨243753888015218276754355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300020736081164142689893 243753888015218276754355)
                    ·
                      rfl

theorem cell23_1424127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_1424127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424127 prefixEnd_1424127 := by exact prefixLift 1424127
  have htrace : WordTrace (prefixWord ++ tailWord_1424127) baseStart_1424127 baseEnd_1424127 := by
    simpa [prefixWord, tailWord_1424127, baseEnd_1424127] using wordTrace_append hprefix tailTrace_1424127
  have hstable : (prefixWord ++ tailWord_1424127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424127).length < 2 ^ (prefixWord ++ tailWord_1424127).sum := by decide
  have hdescent : baseEnd_1424127 < baseStart_1424127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424137 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_1424137 : Nat := 118140960795 + 1424137 * 2 ^ 59
def prefixEnd_1424137 : Nat := 4983230072969 + 3 ^ 40 * 1424137 * 2
def baseEnd_1424137 : Nat := 731266798852199791138019

theorem tailTrace_1424137 : CollatzResearch.WordTrace tailWord_1424137 prefixEnd_1424137 731266798852199791138019 := by
  unfold tailWord_1424137
  simp only [CollatzResearch.WordTrace]
  refine ⟨51942543641602347080718665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34628362427734898053812443 51942543641602347080718665)
  ·
    refine ⟨38956907731201760310538999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51942543641602347080718665 38956907731201760310538999)
    ·
      refine ⟨58435361596802640465808499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38956907731201760310538999 58435361596802640465808499)
      ·
        refine ⟨87653042395203960698712749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58435361596802640465808499 87653042395203960698712749)
        ·
          refine ⟨32869890898201485262017281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87653042395203960698712749 32869890898201485262017281)
          ·
            refine ⟨24652418173651113946512961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32869890898201485262017281 24652418173651113946512961)
            ·
              refine ⟨18489313630238335459884721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24652418173651113946512961 18489313630238335459884721)
              ·
                refine ⟨13866985222678751594913541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18489313630238335459884721 13866985222678751594913541)
                ·
                  refine ⟨2600059729252265924046289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13866985222678751594913541 2600059729252265924046289)
                  ·
                    refine ⟨1950044796939199443034717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600059729252265924046289 1950044796939199443034717)
                    ·
                      refine ⟨731266798852199791138019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950044796939199443034717 731266798852199791138019)
                      ·
                        rfl

theorem cell23_1424137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_1424137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424137 prefixEnd_1424137 := by exact prefixLift 1424137
  have htrace : WordTrace (prefixWord ++ tailWord_1424137) baseStart_1424137 baseEnd_1424137 := by
    simpa [prefixWord, tailWord_1424137, baseEnd_1424137] using wordTrace_append hprefix tailTrace_1424137
  have hstable : (prefixWord ++ tailWord_1424137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424137).length < 2 ^ (prefixWord ++ tailWord_1424137).sum := by decide
  have hdescent : baseEnd_1424137 < baseStart_1424137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424140 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 10]
def baseStart_1424140 : Nat := 118140960795 + 1424140 * 2 ^ 59
def prefixEnd_1424140 : Nat := 4983230072969 + 3 ^ 40 * 1424140 * 2
def baseEnd_1424140 : Nat := 81252037699351475488945

theorem tailTrace_1424140 : CollatzResearch.WordTrace tailWord_1424140 prefixEnd_1424140 81252037699351475488945 := by
  unfold tailWord_1424140
  simp only [CollatzResearch.WordTrace]
  refine ⟨25971326530295739296538937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34628435373727652395385249 25971326530295739296538937)
  ·
    refine ⟨19478494897721804472404203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25971326530295739296538937 19478494897721804472404203)
    ·
      refine ⟨29217742346582706708606305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19478494897721804472404203 29217742346582706708606305)
      ·
        refine ⟨21913306759937030031454729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29217742346582706708606305 21913306759937030031454729)
        ·
          refine ⟨16434980069952772523591047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21913306759937030031454729 16434980069952772523591047)
          ·
            refine ⟨24652470104929158785386571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16434980069952772523591047 24652470104929158785386571)
            ·
              refine ⟨36978705157393738178079857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24652470104929158785386571 36978705157393738178079857)
              ·
                refine ⟨27734028868045303633559893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36978705157393738178079857 27734028868045303633559893)
                ·
                  refine ⟨81252037699351475488945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27734028868045303633559893 81252037699351475488945)
                  ·
                    rfl

theorem cell23_1424140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_1424140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424140 prefixEnd_1424140 := by exact prefixLift 1424140
  have htrace : WordTrace (prefixWord ++ tailWord_1424140) baseStart_1424140 baseEnd_1424140 := by
    simpa [prefixWord, tailWord_1424140, baseEnd_1424140] using wordTrace_append hprefix tailTrace_1424140
  have hstable : (prefixWord ++ tailWord_1424140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424140).length < 2 ^ (prefixWord ++ tailWord_1424140).sum := by decide
  have hdescent : baseEnd_1424140 < baseStart_1424140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424151 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1424151 : Nat := 118140960795 + 1424151 * 2 ^ 59
def prefixEnd_1424151 : Nat := 4983230072969 + 3 ^ 40 * 1424151 * 2
def baseEnd_1424151 : Nat := 731273987581362736362955

theorem tailTrace_1424151 : CollatzResearch.WordTrace tailWord_1424151 prefixEnd_1424151 731273987581362736362955 := by
  unfold tailWord_1424151
  simp only [CollatzResearch.WordTrace]
  refine ⟨51943054263551627471728307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34628702842367751647818871 51943054263551627471728307)
  ·
    refine ⟨77914581395327441207592461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51943054263551627471728307 77914581395327441207592461)
    ·
      refine ⟨29217968023247790452847173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77914581395327441207592461 29217968023247790452847173)
      ·
        refine ⟨5478369004358960709908845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29217968023247790452847173 5478369004358960709908845)
        ·
          refine ⟨2054388376634610266215817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5478369004358960709908845 2054388376634610266215817)
          ·
            refine ⟨1540791282475957699661863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2054388376634610266215817 1540791282475957699661863)
            ·
              refine ⟨2311186923713936549492795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540791282475957699661863 2311186923713936549492795)
              ·
                refine ⟨3466780385570904824239193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311186923713936549492795 3466780385570904824239193)
                ·
                  refine ⟨2600085289178178618179395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3466780385570904824239193 2600085289178178618179395)
                  ·
                    refine ⟨3900127933767267927269093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2600085289178178618179395 3900127933767267927269093)
                    ·
                      refine ⟨731273987581362736362955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3900127933767267927269093 731273987581362736362955)
                      ·
                        rfl

theorem cell23_1424151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1424151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424151 prefixEnd_1424151 := by exact prefixLift 1424151
  have htrace : WordTrace (prefixWord ++ tailWord_1424151) baseStart_1424151 baseEnd_1424151 := by
    simpa [prefixWord, tailWord_1424151, baseEnd_1424151] using wordTrace_append hprefix tailTrace_1424151
  have hstable : (prefixWord ++ tailWord_1424151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424151).length < 2 ^ (prefixWord ++ tailWord_1424151).sum := by decide
  have hdescent : baseEnd_1424151 < baseStart_1424151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424161 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 1, 4]
def baseStart_1424161 : Nat := 118140960795 + 1424161 * 2 ^ 59
def prefixEnd_1424161 : Nat := 4983230072969 + 3 ^ 40 * 1424161 * 2
def baseEnd_1424161 : Nat := 243759707462635899079303

theorem tailTrace_1424161 : CollatzResearch.WordTrace tailWord_1424161 prefixEnd_1424161 243759707462635899079303 := by
  unfold tailWord_1424161
  simp only [CollatzResearch.WordTrace]
  refine ⟨51943418993515399179592337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34628945995676932786394891 51943418993515399179592337)
  ·
    refine ⟨38957564245136549384694253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51943418993515399179592337 38957564245136549384694253)
    ·
      refine ⟨14609086591926206019260345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38957564245136549384694253 14609086591926206019260345)
      ·
        refine ⟨10956814943944654514445259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14609086591926206019260345 10956814943944654514445259)
        ·
          refine ⟨16435222415916981771667889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10956814943944654514445259 16435222415916981771667889)
          ·
            refine ⟨12326416811937736328750917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16435222415916981771667889 12326416811937736328750917)
            ·
              refine ⟨2311203152238325561640797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12326416811937736328750917 2311203152238325561640797)
              ·
                refine ⟨866701182089372085615299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2311203152238325561640797 866701182089372085615299)
                ·
                  refine ⟨1300051773134058128422949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866701182089372085615299 1300051773134058128422949)
                  ·
                    refine ⟨243759707462635899079303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300051773134058128422949 243759707462635899079303)
                    ·
                      rfl

theorem cell23_1424161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_1424161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424161 prefixEnd_1424161 := by exact prefixLift 1424161
  have htrace : WordTrace (prefixWord ++ tailWord_1424161) baseStart_1424161 baseEnd_1424161 := by
    simpa [prefixWord, tailWord_1424161, baseEnd_1424161] using wordTrace_append hprefix tailTrace_1424161
  have hstable : (prefixWord ++ tailWord_1424161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424161).length < 2 ^ (prefixWord ++ tailWord_1424161).sum := by decide
  have hdescent : baseEnd_1424161 < baseStart_1424161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424174 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_1424174 : Nat := 118140960795 + 1424174 * 2 ^ 59
def prefixEnd_1424174 : Nat := 4983230072969 + 3 ^ 40 * 1424174 * 2
def baseEnd_1424174 : Nat := 81253977515157349597261

theorem tailTrace_1424174 : CollatzResearch.WordTrace tailWord_1424174 prefixEnd_1424174 81253977515157349597261 := by
  unfold tailWord_1424174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492986642808537799976947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34629262094978868266543717 6492986642808537799976947)
  ·
    refine ⟨9739479964212806699965421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6492986642808537799976947 9739479964212806699965421)
    ·
      refine ⟨3652304986579802512487033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9739479964212806699965421 3652304986579802512487033)
      ·
        refine ⟨2739228739934851884365275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3652304986579802512487033 2739228739934851884365275)
        ·
          refine ⟨4108843109902277826547913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739228739934851884365275 4108843109902277826547913)
          ·
            refine ⟨3081632332426708369910935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108843109902277826547913 3081632332426708369910935)
            ·
              refine ⟨4622448498640062554866403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081632332426708369910935 4622448498640062554866403)
              ·
                refine ⟨6933672747960093832299605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622448498640062554866403 6933672747960093832299605)
                ·
                  refine ⟨81253977515157349597261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6933672747960093832299605 81253977515157349597261)
                  ·
                    rfl

theorem cell23_1424174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_1424174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424174 prefixEnd_1424174 := by exact prefixLift 1424174
  have htrace : WordTrace (prefixWord ++ tailWord_1424174) baseStart_1424174 baseEnd_1424174 := by
    simpa [prefixWord, tailWord_1424174, baseEnd_1424174] using wordTrace_append hprefix tailTrace_1424174
  have hstable : (prefixWord ++ tailWord_1424174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424174).length < 2 ^ (prefixWord ++ tailWord_1424174).sum := by decide
  have hdescent : baseEnd_1424174 < baseStart_1424174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424204 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_1424204 : Nat := 118140960795 + 1424204 * 2 ^ 59
def prefixEnd_1424204 : Nat := 4983230072969 + 3 ^ 40 * 1424204 * 2
def baseEnd_1424204 : Nat := 243767067352017009666737

theorem tailTrace_1424204 : CollatzResearch.WordTrace tailWord_1424204 prefixEnd_1424204 243767067352017009666737 := by
  unfold tailWord_1424204
  simp only [CollatzResearch.WordTrace]
  refine ⟨25972493666179808761703833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34629991554906411682271777 25972493666179808761703833)
  ·
    refine ⟨19479370249634856571277875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25972493666179808761703833 19479370249634856571277875)
    ·
      refine ⟨29219055374452284856916813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19479370249634856571277875 29219055374452284856916813)
      ·
        refine ⟨10957145765419606821343805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29219055374452284856916813 10957145765419606821343805)
        ·
          refine ⟨4108929662032352558003927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10957145765419606821343805 4108929662032352558003927)
          ·
            refine ⟨6163394493048528837005891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4108929662032352558003927 6163394493048528837005891)
            ·
              refine ⟨9245091739572793255508837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163394493048528837005891 9245091739572793255508837)
              ·
                refine ⟨1733454701169898735407907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9245091739572793255508837 1733454701169898735407907)
                ·
                  refine ⟨2600182051754848103111861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733454701169898735407907 2600182051754848103111861)
                  ·
                    refine ⟨243767067352017009666737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2600182051754848103111861 243767067352017009666737)
                    ·
                      rfl

theorem cell23_1424204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_1424204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424204 prefixEnd_1424204 := by exact prefixLift 1424204
  have htrace : WordTrace (prefixWord ++ tailWord_1424204) baseStart_1424204 baseEnd_1424204 := by
    simpa [prefixWord, tailWord_1424204, baseEnd_1424204] using wordTrace_append hprefix tailTrace_1424204
  have hstable : (prefixWord ++ tailWord_1424204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424204).length < 2 ^ (prefixWord ++ tailWord_1424204).sum := by decide
  have hdescent : baseEnd_1424204 < baseStart_1424204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424218 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3]
def baseStart_1424218 : Nat := 118140960795 + 1424218 * 2 ^ 59
def prefixEnd_1424218 : Nat := 4983230072969 + 3 ^ 40 * 1424218 * 2
def baseEnd_1424218 : Nat := 731308390785213974225147

theorem tailTrace_1424218 : CollatzResearch.WordTrace tailWord_1424218 prefixEnd_1424218 731308390785213974225147 := by
  unfold tailWord_1424218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12986374488577224478604327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34630331969539265276278205 12986374488577224478604327)
  ·
    refine ⟨19479561732865836717906491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12986374488577224478604327 19479561732865836717906491)
    ·
      refine ⟨29219342599298755076859737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19479561732865836717906491 29219342599298755076859737)
      ·
        refine ⟨21914506949474066307644803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29219342599298755076859737 21914506949474066307644803)
        ·
          refine ⟨32871760424211099461467205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21914506949474066307644803 32871760424211099461467205)
          ·
            refine ⟨6163455079539581149025101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32871760424211099461467205 6163455079539581149025101)
            ·
              refine ⟨2311295654827342930884413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6163455079539581149025101 2311295654827342930884413)
              ·
                refine ⟨866735870560253599081655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2311295654827342930884413 866735870560253599081655)
                ·
                  refine ⟨1300103805840380398622483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866735870560253599081655 1300103805840380398622483)
                  ·
                    refine ⟨1950155708760570597933725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300103805840380398622483 1950155708760570597933725)
                    ·
                      refine ⟨731308390785213974225147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950155708760570597933725 731308390785213974225147)
                      ·
                        rfl

theorem cell23_1424218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_1424218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424218 prefixEnd_1424218 := by exact prefixLift 1424218
  have htrace : WordTrace (prefixWord ++ tailWord_1424218) baseStart_1424218 baseEnd_1424218 := by
    simpa [prefixWord, tailWord_1424218, baseEnd_1424218] using wordTrace_append hprefix tailTrace_1424218
  have hstable : (prefixWord ++ tailWord_1424218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424218).length < 2 ^ (prefixWord ++ tailWord_1424218).sum := by decide
  have hdescent : baseEnd_1424218 < baseStart_1424218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424224 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4]
def baseStart_1424224 : Nat := 118140960795 + 1424224 * 2 ^ 59
def prefixEnd_1424224 : Nat := 4983230072969 + 3 ^ 40 * 1424224 * 2
def baseEnd_1424224 : Nat := 731311471669140950750119

theorem tailTrace_1424224 : CollatzResearch.WordTrace tailWord_1424224 prefixEnd_1424224 731311471669140950750119 := by
  unfold tailWord_1424224
  simp only [CollatzResearch.WordTrace]
  refine ⟨25972858396143580469567863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34630477861524773959423817 25972858396143580469567863)
  ·
    refine ⟨38959287594215370704351795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25972858396143580469567863 38959287594215370704351795)
    ·
      refine ⟨58438931391323056056527693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38959287594215370704351795 58438931391323056056527693)
      ·
        refine ⟨21914599271746146021197885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58438931391323056056527693 21914599271746146021197885)
        ·
          refine ⟨8217974726904804757949207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21914599271746146021197885 8217974726904804757949207)
          ·
            refine ⟨12326962090357207136923811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8217974726904804757949207 12326962090357207136923811)
            ·
              refine ⟨18490443135535810705385717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12326962090357207136923811 18490443135535810705385717)
              ·
                refine ⟨1733479043956482253629911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18490443135535810705385717 1733479043956482253629911)
                ·
                  refine ⟨2600218565934723380444867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733479043956482253629911 2600218565934723380444867)
                  ·
                    refine ⟨3900327848902085070667301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2600218565934723380444867 3900327848902085070667301)
                    ·
                      refine ⟨731311471669140950750119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3900327848902085070667301 731311471669140950750119)
                      ·
                        rfl

theorem cell23_1424224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_1424224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424224 prefixEnd_1424224 := by exact prefixLift 1424224
  have htrace : WordTrace (prefixWord ++ tailWord_1424224) baseStart_1424224 baseEnd_1424224 := by
    simpa [prefixWord, tailWord_1424224, baseEnd_1424224] using wordTrace_append hprefix tailTrace_1424224
  have hstable : (prefixWord ++ tailWord_1424224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424224).length < 2 ^ (prefixWord ++ tailWord_1424224).sum := by decide
  have hdescent : baseEnd_1424224 < baseStart_1424224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424251 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 2, 4]
def baseStart_1424251 : Nat := 118140960795 + 1424251 * 2 ^ 59
def prefixEnd_1424251 : Nat := 4983230072969 + 3 ^ 40 * 1424251 * 2
def baseEnd_1424251 : Nat := 243775111882270781704165

theorem tailTrace_1424251 : CollatzResearch.WordTrace tailWord_1424251 prefixEnd_1424251 243775111882270781704165 := by
  unfold tailWord_1424251
  simp only [CollatzResearch.WordTrace]
  refine ⟨51946701563189344550368607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34631134375459563033579071 51946701563189344550368607)
  ·
    refine ⟨77920052344784016825552911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51946701563189344550368607 77920052344784016825552911)
    ·
      refine ⟨116880078517176025238329367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77920052344784016825552911 116880078517176025238329367)
      ·
        refine ⟨175320117775764037857494051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116880078517176025238329367 175320117775764037857494051)
        ·
          refine ⟨262980176663646056786241077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175320117775764037857494051 262980176663646056786241077)
          ·
            refine ⟨24654391562216817823710101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262980176663646056786241077 24654391562216817823710101)
            ·
              refine ⟨1155674604478913335486411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24654391562216817823710101 1155674604478913335486411)
              ·
                refine ⟨1733511906718370003229617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155674604478913335486411 1733511906718370003229617)
                ·
                  refine ⟨1300133930038777502422213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733511906718370003229617 1300133930038777502422213)
                  ·
                    refine ⟨243775111882270781704165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300133930038777502422213 243775111882270781704165)
                    ·
                      rfl

theorem cell23_1424251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 4].length) (baseStart_1424251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424251 prefixEnd_1424251 := by exact prefixLift 1424251
  have htrace : WordTrace (prefixWord ++ tailWord_1424251) baseStart_1424251 baseEnd_1424251 := by
    simpa [prefixWord, tailWord_1424251, baseEnd_1424251] using wordTrace_append hprefix tailTrace_1424251
  have hstable : (prefixWord ++ tailWord_1424251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424251).length < 2 ^ (prefixWord ++ tailWord_1424251).sum := by decide
  have hdescent : baseEnd_1424251 < baseStart_1424251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424261 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_1424261 : Nat := 118140960795 + 1424261 * 2 ^ 59
def prefixEnd_1424261 : Nat := 4983230072969 + 3 ^ 40 * 1424261 * 2
def baseEnd_1424261 : Nat := 731330470453357305987449

theorem tailTrace_1424261 : CollatzResearch.WordTrace tailWord_1424261 prefixEnd_1424261 731330470453357305987449 := by
  unfold tailWord_1424261
  simp only [CollatzResearch.WordTrace]
  refine ⟨51947066293153116258232637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34631377528768744172155091 51947066293153116258232637)
  ·
    refine ⟨19480149859932418596837239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51947066293153116258232637 19480149859932418596837239)
    ·
      refine ⟨29220224789898627895255859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19480149859932418596837239 29220224789898627895255859)
      ·
        refine ⟨43830337184847941842883789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29220224789898627895255859 43830337184847941842883789)
        ·
          refine ⟨16436376444317978191081421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43830337184847941842883789 16436376444317978191081421)
          ·
            refine ⟨6163641166619241821655533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16436376444317978191081421 6163641166619241821655533)
            ·
              refine ⟨2311365437482215683120825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6163641166619241821655533 2311365437482215683120825)
              ·
                refine ⟨1733524078111661762340619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311365437482215683120825 1733524078111661762340619)
                ·
                  refine ⟨2600286117167492643510929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733524078111661762340619 2600286117167492643510929)
                  ·
                    refine ⟨1950214587875619482633197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600286117167492643510929 1950214587875619482633197)
                    ·
                      refine ⟨731330470453357305987449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950214587875619482633197 731330470453357305987449)
                      ·
                        rfl

theorem cell23_1424261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_1424261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424261 prefixEnd_1424261 := by exact prefixLift 1424261
  have htrace : WordTrace (prefixWord ++ tailWord_1424261) baseStart_1424261 baseEnd_1424261 := by
    simpa [prefixWord, tailWord_1424261, baseEnd_1424261] using wordTrace_append hprefix tailTrace_1424261
  have hstable : (prefixWord ++ tailWord_1424261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424261).length < 2 ^ (prefixWord ++ tailWord_1424261).sum := by decide
  have hdescent : baseEnd_1424261 < baseStart_1424261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424291 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1424291 : Nat := 118140960795 + 1424291 * 2 ^ 59
def prefixEnd_1424291 : Nat := 4983230072969 + 3 ^ 40 * 1424291 * 2
def baseEnd_1424291 : Nat := 731345874872992188612311

theorem tailTrace_1424291 : CollatzResearch.WordTrace tailWord_1424291 prefixEnd_1424291 731345874872992188612311 := by
  unfold tailWord_1424291
  simp only [CollatzResearch.WordTrace]
  refine ⟨51948160483044431381824727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34632106988696287587883151 51948160483044431381824727)
  ·
    refine ⟨77922240724566647072737091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51948160483044431381824727 77922240724566647072737091)
    ·
      refine ⟨116883361086849970609105637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77922240724566647072737091 116883361086849970609105637)
      ·
        refine ⟨21915630203784369489207307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116883361086849970609105637 21915630203784369489207307)
        ·
          refine ⟨32873445305676554233810961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21915630203784369489207307 32873445305676554233810961)
          ·
            refine ⟨24655083979257415675358221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32873445305676554233810961 24655083979257415675358221)
            ·
              refine ⟨9245656492221530878259333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24655083979257415675358221 9245656492221530878259333)
              ·
                refine ⟨1733560592291537039673625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9245656492221530878259333 1733560592291537039673625)
                ·
                  refine ⟨1300170444218652779755219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733560592291537039673625 1300170444218652779755219)
                  ·
                    refine ⟨1950255666327979169632829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300170444218652779755219 1950255666327979169632829)
                    ·
                      refine ⟨731345874872992188612311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950255666327979169632829 731345874872992188612311)
                      ·
                        rfl

theorem cell23_1424291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1424291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424291 prefixEnd_1424291 := by exact prefixLift 1424291
  have htrace : WordTrace (prefixWord ++ tailWord_1424291) baseStart_1424291 baseEnd_1424291 := by
    simpa [prefixWord, tailWord_1424291, baseEnd_1424291] using wordTrace_append hprefix tailTrace_1424291
  have hstable : (prefixWord ++ tailWord_1424291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424291).length < 2 ^ (prefixWord ++ tailWord_1424291).sum := by decide
  have hdescent : baseEnd_1424291 < baseStart_1424291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424297 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_1424297 : Nat := 118140960795 + 1424297 * 2 ^ 59
def prefixEnd_1424297 : Nat := 4983230072969 + 3 ^ 40 * 1424297 * 2
def baseEnd_1424297 : Nat := 731348955756919165137283

theorem tailTrace_1424297 : CollatzResearch.WordTrace tailWord_1424297 prefixEnd_1424297 731348955756919165137283 := by
  unfold tailWord_1424297
  simp only [CollatzResearch.WordTrace]
  refine ⟨51948379321022694406543145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34632252880681796271028763 51948379321022694406543145)
  ·
    refine ⟨38961284490767020804907359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51948379321022694406543145 38961284490767020804907359)
    ·
      refine ⟨58441926736150531207361039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38961284490767020804907359 58441926736150531207361039)
      ·
        refine ⟨87662890104225796811041559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58441926736150531207361039 87662890104225796811041559)
        ·
          refine ⟨131494335156338695216562339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87662890104225796811041559 131494335156338695216562339)
          ·
            refine ⟨197241502734508042824843509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131494335156338695216562339 197241502734508042824843509)
            ·
              refine ⟨18491390881360129014829079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197241502734508042824843509 18491390881360129014829079)
              ·
                refine ⟨27737086322040193522243619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18491390881360129014829079 27737086322040193522243619)
                ·
                  refine ⟨41605629483060290283365429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27737086322040193522243619 41605629483060290283365429)
                  ·
                    refine ⟨3900527764036902214065509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41605629483060290283365429 3900527764036902214065509)
                    ·
                      refine ⟨731348955756919165137283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3900527764036902214065509 731348955756919165137283)
                      ·
                        rfl

theorem cell23_1424297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_1424297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424297 prefixEnd_1424297 := by exact prefixLift 1424297
  have htrace : WordTrace (prefixWord ++ tailWord_1424297) baseStart_1424297 baseEnd_1424297 := by
    simpa [prefixWord, tailWord_1424297, baseEnd_1424297] using wordTrace_append hprefix tailTrace_1424297
  have hstable : (prefixWord ++ tailWord_1424297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424297).length < 2 ^ (prefixWord ++ tailWord_1424297).sum := by decide
  have hdescent : baseEnd_1424297 < baseStart_1424297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424308 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1424308 : Nat := 118140960795 + 1424308 * 2 ^ 59
def prefixEnd_1424308 : Nat := 4983230072969 + 3 ^ 40 * 1424308 * 2
def baseEnd_1424308 : Nat := 731354604044118622099733

theorem tailTrace_1424308 : CollatzResearch.WordTrace tailWord_1424308 prefixEnd_1424308 731354604044118622099733 := by
  unfold tailWord_1424308
  simp only [CollatzResearch.WordTrace]
  refine ⟨25974390261991421642596789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34632520349321895523462385 25974390261991421642596789)
  ·
    refine ⟨2435099087061695778993449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25974390261991421642596789 2435099087061695778993449)
    ·
      refine ⟨1826324315296271834245087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2435099087061695778993449 1826324315296271834245087)
      ·
        refine ⟨2739486472944407751367631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826324315296271834245087 2739486472944407751367631)
        ·
          refine ⟨4109229709416611627051447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739486472944407751367631 4109229709416611627051447)
          ·
            refine ⟨6163844564124917440577171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109229709416611627051447 6163844564124917440577171)
            ·
              refine ⟨9245766846187376160865757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163844564124917440577171 9245766846187376160865757)
              ·
                refine ⟨3467162567320266060324659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9245766846187376160865757 3467162567320266060324659)
                ·
                  refine ⟨5200743850980399090486989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467162567320266060324659 5200743850980399090486989)
                  ·
                    refine ⟨1950278944117649658932621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5200743850980399090486989 1950278944117649658932621)
                    ·
                      refine ⟨731354604044118622099733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950278944117649658932621 731354604044118622099733)
                      ·
                        rfl

theorem cell23_1424308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1424308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424308 prefixEnd_1424308 := by exact prefixLift 1424308
  have htrace : WordTrace (prefixWord ++ tailWord_1424308) baseStart_1424308 baseEnd_1424308 := by
    simpa [prefixWord, tailWord_1424308, baseEnd_1424308] using wordTrace_append hprefix tailTrace_1424308
  have hstable : (prefixWord ++ tailWord_1424308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424308).length < 2 ^ (prefixWord ++ tailWord_1424308).sum := by decide
  have hdescent : baseEnd_1424308 < baseStart_1424308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424318 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_1424318 : Nat := 118140960795 + 1424318 * 2 ^ 59
def prefixEnd_1424318 : Nat := 4983230072969 + 3 ^ 40 * 1424318 * 2
def baseEnd_1424318 : Nat := 731359738850663582974687

theorem tailTrace_1424318 : CollatzResearch.WordTrace tailWord_1424318 prefixEnd_1424318 731359738850663582974687 := by
  unfold tailWord_1424318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6493643156743326874132201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34632763502631076662038405 6493643156743326874132201)
  ·
    refine ⟨4870232367557495155599151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6493643156743326874132201 4870232367557495155599151)
    ·
      refine ⟨7305348551336242733398727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4870232367557495155599151 7305348551336242733398727)
      ·
        refine ⟨10958022827004364100098091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7305348551336242733398727 10958022827004364100098091)
        ·
          refine ⟨16437034240506546150147137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10958022827004364100098091 16437034240506546150147137)
          ·
            refine ⟨12327775680379909612610353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16437034240506546150147137 12327775680379909612610353)
            ·
              refine ⟨9245831760284932209457765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12327775680379909612610353 9245831760284932209457765)
              ·
                refine ⟨1733593455053424789273331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9245831760284932209457765 1733593455053424789273331)
                ·
                  refine ⟨2600390182580137183909997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733593455053424789273331 2600390182580137183909997)
                  ·
                    refine ⟨975146318467551443966249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600390182580137183909997 975146318467551443966249)
                    ·
                      refine ⟨731359738850663582974687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975146318467551443966249 731359738850663582974687)
                      ·
                        rfl

theorem cell23_1424318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_1424318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424318 prefixEnd_1424318 := by exact prefixLift 1424318
  have htrace : WordTrace (prefixWord ++ tailWord_1424318) baseStart_1424318 baseEnd_1424318 := by
    simpa [prefixWord, tailWord_1424318, baseEnd_1424318] using wordTrace_append hprefix tailTrace_1424318
  have hstable : (prefixWord ++ tailWord_1424318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424318).length < 2 ^ (prefixWord ++ tailWord_1424318).sum := by decide
  have hdescent : baseEnd_1424318 < baseStart_1424318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424326 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1424326 : Nat := 118140960795 + 1424326 * 2 ^ 59
def prefixEnd_1424326 : Nat := 4983230072969 + 3 ^ 40 * 1424326 * 2
def baseEnd_1424326 : Nat := 731363846695899551674651

theorem tailTrace_1424326 : CollatzResearch.WordTrace tailWord_1424326 prefixEnd_1424326 731363846695899551674651 := by
  unfold tailWord_1424326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623419907434926011229651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34632958025278421572899221 1623419907434926011229651)
  ·
    refine ⟨2435129861152389016844477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1623419907434926011229651 2435129861152389016844477)
    ·
      refine ⟨913173697932145881316679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2435129861152389016844477 913173697932145881316679)
      ·
        refine ⟨1369760546898218821975019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913173697932145881316679 1369760546898218821975019)
        ·
          refine ⟨2054640820347328232962529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369760546898218821975019 2054640820347328232962529)
          ·
            refine ⟨1540980615260496174721897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2054640820347328232962529 1540980615260496174721897)
            ·
              refine ⟨1155735461445372131041423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540980615260496174721897 1155735461445372131041423)
              ·
                refine ⟨1733603192168058196562135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155735461445372131041423 1733603192168058196562135)
                ·
                  refine ⟨2600404788252087294843203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733603192168058196562135 2600404788252087294843203)
                  ·
                    refine ⟨3900607182378130942264805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2600404788252087294843203 3900607182378130942264805)
                    ·
                      refine ⟨731363846695899551674651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3900607182378130942264805 731363846695899551674651)
                      ·
                        rfl

theorem cell23_1424326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1424326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424326 prefixEnd_1424326 := by exact prefixLift 1424326
  have htrace : WordTrace (prefixWord ++ tailWord_1424326) baseStart_1424326 baseEnd_1424326 := by
    simpa [prefixWord, tailWord_1424326, baseEnd_1424326] using wordTrace_append hprefix tailTrace_1424326
  have hstable : (prefixWord ++ tailWord_1424326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424326).length < 2 ^ (prefixWord ++ tailWord_1424326).sum := by decide
  have hdescent : baseEnd_1424326 < baseStart_1424326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424331 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 1, 4, 2]
def baseStart_1424331 : Nat := 118140960795 + 1424331 * 2 ^ 59
def prefixEnd_1424331 : Nat := 4983230072969 + 3 ^ 40 * 1424331 * 2
def baseEnd_1424331 : Nat := 731366414099172032112127

theorem tailTrace_1424331 : CollatzResearch.WordTrace tailWord_1424331 prefixEnd_1424331 731366414099172032112127 := by
  unfold tailWord_1424331
  simp only [CollatzResearch.WordTrace]
  refine ⟨51949619402899518213280847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34633079601933012142187231 51949619402899518213280847)
  ·
    refine ⟨77924429104349277319921271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51949619402899518213280847 77924429104349277319921271)
    ·
      refine ⟨116886643656523915979881907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77924429104349277319921271 116886643656523915979881907)
      ·
        refine ⟨175329965484785873969822861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116886643656523915979881907 175329965484785873969822861)
        ·
          refine ⟨65748737056794702738683573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175329965484785873969822861 65748737056794702738683573)
          ·
            refine ⟨6163944099074503381751585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65748737056794702738683573 6163944099074503381751585)
            ·
              refine ⟨4622958074305877536313689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6163944099074503381751585 4622958074305877536313689)
              ·
                refine ⟨3467218555729408152235267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4622958074305877536313689 3467218555729408152235267)
                ·
                  refine ⟨5200827833594112228352901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467218555729408152235267 5200827833594112228352901)
                  ·
                    refine ⟨975155218798896042816169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200827833594112228352901 975155218798896042816169)
                    ·
                      refine ⟨731366414099172032112127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975155218798896042816169 731366414099172032112127)
                      ·
                        rfl

theorem cell23_1424331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4, 2].length) (baseStart_1424331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424331 prefixEnd_1424331 := by exact prefixLift 1424331
  have htrace : WordTrace (prefixWord ++ tailWord_1424331) baseStart_1424331 baseEnd_1424331 := by
    simpa [prefixWord, tailWord_1424331, baseEnd_1424331] using wordTrace_append hprefix tailTrace_1424331
  have hstable : (prefixWord ++ tailWord_1424331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424331).length < 2 ^ (prefixWord ++ tailWord_1424331).sum := by decide
  have hdescent : baseEnd_1424331 < baseStart_1424331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424335 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 1, 3, 2]
def baseStart_1424335 : Nat := 118140960795 + 1424335 * 2 ^ 59
def prefixEnd_1424335 : Nat := 4983230072969 + 3 ^ 40 * 1424335 * 2
def baseEnd_1424335 : Nat := 731368468021790016462109

theorem tailTrace_1424335 : CollatzResearch.WordTrace tailWord_1424335 prefixEnd_1424335 731368468021790016462109 := by
  unfold tailWord_1424335
  simp only [CollatzResearch.WordTrace]
  refine ⟨51949765294885026896426459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34633176863256684597617639 51949765294885026896426459)
  ·
    refine ⟨77924647942327540344639689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51949765294885026896426459 77924647942327540344639689)
    ·
      refine ⟨58443485956745655258479767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77924647942327540344639689 58443485956745655258479767)
      ·
        refine ⟨87665228935118482887719651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58443485956745655258479767 87665228935118482887719651)
        ·
          refine ⟨131497843402677724331579477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87665228935118482887719651 131497843402677724331579477)
          ·
            refine ⟨1540990352375129582010697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 131497843402677724331579477 1540990352375129582010697)
            ·
              refine ⟨1155742764281347186508023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540990352375129582010697 1155742764281347186508023)
              ·
                refine ⟨1733614146422020779762035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155742764281347186508023 1733614146422020779762035)
                ·
                  refine ⟨2600421219633031169643053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733614146422020779762035 2600421219633031169643053)
                  ·
                    refine ⟨975157957362386688616145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600421219633031169643053 975157957362386688616145)
                    ·
                      refine ⟨731368468021790016462109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975157957362386688616145 731368468021790016462109)
                      ·
                        rfl

theorem cell23_1424335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 3, 2].length) (baseStart_1424335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424335 prefixEnd_1424335 := by exact prefixLift 1424335
  have htrace : WordTrace (prefixWord ++ tailWord_1424335) baseStart_1424335 baseEnd_1424335 := by
    simpa [prefixWord, tailWord_1424335, baseEnd_1424335] using wordTrace_append hprefix tailTrace_1424335
  have hstable : (prefixWord ++ tailWord_1424335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424335).length < 2 ^ (prefixWord ++ tailWord_1424335).sum := by decide
  have hdescent : baseEnd_1424335 < baseStart_1424335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424337 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 9]
def baseStart_1424337 : Nat := 118140960795 + 1424337 * 2 ^ 59
def prefixEnd_1424337 : Nat := 4983230072969 + 3 ^ 40 * 1424337 * 2
def baseEnd_1424337 : Nat := 81263277220344334293011

theorem tailTrace_1424337 : CollatzResearch.WordTrace tailWord_1424337 prefixEnd_1424337 81263277220344334293011 := by
  unfold tailWord_1424337
  simp only [CollatzResearch.WordTrace]
  refine ⟨51949838240877781237999265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34633225493918520825332843 51949838240877781237999265)
  ·
    refine ⟨38962378680658335928499449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51949838240877781237999265 38962378680658335928499449)
    ·
      refine ⟨29221784010493751946374587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38962378680658335928499449 29221784010493751946374587)
      ·
        refine ⟨43832676015740627919561881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29221784010493751946374587 43832676015740627919561881)
        ·
          refine ⟨32874507011805470939671411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43832676015740627919561881 32874507011805470939671411)
          ·
            refine ⟨49311760517708206409507117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32874507011805470939671411 49311760517708206409507117)
            ·
              refine ⟨18491910194140577403565169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49311760517708206409507117 18491910194140577403565169)
              ·
                refine ⟨13868932645605433052673877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18491910194140577403565169 13868932645605433052673877)
                ·
                  refine ⟨81263277220344334293011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13868932645605433052673877 81263277220344334293011)
                  ·
                    rfl

theorem cell23_1424337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_1424337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424337 prefixEnd_1424337 := by exact prefixLift 1424337
  have htrace : WordTrace (prefixWord ++ tailWord_1424337) baseStart_1424337 baseEnd_1424337 := by
    simpa [prefixWord, tailWord_1424337, baseEnd_1424337] using wordTrace_append hprefix tailTrace_1424337
  have hstable : (prefixWord ++ tailWord_1424337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424337).length < 2 ^ (prefixWord ++ tailWord_1424337).sum := by decide
  have hdescent : baseEnd_1424337 < baseStart_1424337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424342 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1424342 : Nat := 118140960795 + 1424342 * 2 ^ 59
def prefixEnd_1424342 : Nat := 4983230072969 + 3 ^ 40 * 1424342 * 2
def baseEnd_1424342 : Nat := 731372062386371489074577

theorem tailTrace_1424342 : CollatzResearch.WordTrace tailWord_1424342 prefixEnd_1424342 731372062386371489074577 := by
  unfold tailWord_1424342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3246876287866229193245705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34633347070573111394620853 3246876287866229193245705)
  ·
    refine ⟨2435157215899671894934279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3246876287866229193245705 2435157215899671894934279)
    ·
      refine ⟨3652735823849507842401419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435157215899671894934279 3652735823849507842401419)
      ·
        refine ⟨5479103735774261763602129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652735823849507842401419 5479103735774261763602129)
        ·
          refine ⟨4109327801830696322701597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479103735774261763602129 4109327801830696322701597)
          ·
            refine ⟨1540997925686511121013099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4109327801830696322701597 1540997925686511121013099)
            ·
              refine ⟨2311496888529766681519649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540997925686511121013099 2311496888529766681519649)
              ·
                refine ⟨1733622666397325011139737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311496888529766681519649 1733622666397325011139737)
                ·
                  refine ⟨1300216999797993758354803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733622666397325011139737 1300216999797993758354803)
                  ·
                    refine ⟨1950325499696990637532205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300216999797993758354803 1950325499696990637532205)
                    ·
                      refine ⟨731372062386371489074577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950325499696990637532205 731372062386371489074577)
                      ·
                        rfl

theorem cell23_1424342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1424342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424342 prefixEnd_1424342 := by exact prefixLift 1424342
  have htrace : WordTrace (prefixWord ++ tailWord_1424342) baseStart_1424342 baseEnd_1424342 := by
    simpa [prefixWord, tailWord_1424342, baseEnd_1424342] using wordTrace_append hprefix tailTrace_1424342
  have hstable : (prefixWord ++ tailWord_1424342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424342).length < 2 ^ (prefixWord ++ tailWord_1424342).sum := by decide
  have hdescent : baseEnd_1424342 < baseStart_1424342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424344 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1424344 : Nat := 118140960795 + 1424344 * 2 ^ 59
def prefixEnd_1424344 : Nat := 4983230072969 + 3 ^ 40 * 1424344 * 2
def baseEnd_1424344 : Nat := 731373089347680481249567

theorem tailTrace_1424344 : CollatzResearch.WordTrace tailWord_1424344 prefixEnd_1424344 731373089347680481249567 := by
  unfold tailWord_1424344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25975046775926210716752043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34633395701234947622336057 25975046775926210716752043)
  ·
    refine ⟨38962570163889316075128065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25975046775926210716752043 38962570163889316075128065)
    ·
      refine ⟨29221927622916987056346049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38962570163889316075128065 29221927622916987056346049)
      ·
        refine ⟨21916445717187740292259537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29221927622916987056346049 21916445717187740292259537)
        ·
          refine ⟨16437334287890805219194653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21916445717187740292259537 16437334287890805219194653)
          ·
            refine ⟨6164000357959051957197995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16437334287890805219194653 6164000357959051957197995)
            ·
              refine ⟨9246000536938577935796993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164000357959051957197995 9246000536938577935796993)
              ·
                refine ⟨6934500402703933451847745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9246000536938577935796993 6934500402703933451847745)
                ·
                  refine ⟨5200875302027950088885809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6934500402703933451847745 5200875302027950088885809)
                  ·
                    refine ⟨3900656476520962566664357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200875302027950088885809 3900656476520962566664357)
                    ·
                      refine ⟨731373089347680481249567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3900656476520962566664357 731373089347680481249567)
                      ·
                        rfl

theorem cell23_1424344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1424344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424344 prefixEnd_1424344 := by exact prefixLift 1424344
  have htrace : WordTrace (prefixWord ++ tailWord_1424344) baseStart_1424344 baseEnd_1424344 := by
    simpa [prefixWord, tailWord_1424344, baseEnd_1424344] using wordTrace_append hprefix tailTrace_1424344
  have hstable : (prefixWord ++ tailWord_1424344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424344).length < 2 ^ (prefixWord ++ tailWord_1424344).sum := by decide
  have hdescent : baseEnd_1424344 < baseStart_1424344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424416 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1424416 : Nat := 118140960795 + 1424416 * 2 ^ 59
def prefixEnd_1424416 : Nat := 4983230072969 + 3 ^ 40 * 1424416 * 2
def baseEnd_1424416 : Nat := 731410059954804199549237

theorem tailTrace_1424416 : CollatzResearch.WordTrace tailWord_1424416 prefixEnd_1424416 731410059954804199549237 := by
  unfold tailWord_1424416
  simp only [CollatzResearch.WordTrace]
  refine ⟨25976359803795788865062551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34635146405061051820083401 25976359803795788865062551)
  ·
    refine ⟨38964539705693683297593827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25976359803795788865062551 38964539705693683297593827)
    ·
      refine ⟨58446809558540524946390741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38964539705693683297593827 58446809558540524946390741)
      ·
        refine ⟨1369847099028293553431033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58446809558540524946390741 1369847099028293553431033)
        ·
          refine ⟨1027385324271220165073275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1369847099028293553431033 1027385324271220165073275)
          ·
            refine ⟨1541077986406830247609913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027385324271220165073275 1541077986406830247609913)
            ·
              refine ⟨1155808489805122685707435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1541077986406830247609913 1155808489805122685707435)
              ·
                refine ⟨1733712734707684028561153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155808489805122685707435 1733712734707684028561153)
                ·
                  refine ⟨1300284551030763021420865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733712734707684028561153 1300284551030763021420865)
                  ·
                    refine ⟨975213413273072266065649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300284551030763021420865 975213413273072266065649)
                    ·
                      refine ⟨731410059954804199549237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975213413273072266065649 731410059954804199549237)
                      ·
                        rfl

theorem cell23_1424416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1424416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424416 prefixEnd_1424416 := by exact prefixLift 1424416
  have htrace : WordTrace (prefixWord ++ tailWord_1424416) baseStart_1424416 baseEnd_1424416 := by
    simpa [prefixWord, tailWord_1424416, baseEnd_1424416] using wordTrace_append hprefix tailTrace_1424416
  have hstable : (prefixWord ++ tailWord_1424416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424416).length < 2 ^ (prefixWord ++ tailWord_1424416).sum := by decide
  have hdescent : baseEnd_1424416 < baseStart_1424416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424421 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 6, 2]
def baseStart_1424421 : Nat := 118140960795 + 1424421 * 2 ^ 59
def prefixEnd_1424421 : Nat := 4983230072969 + 3 ^ 40 * 1424421 * 2
def baseEnd_1424421 : Nat := 731412627358076679986713

theorem tailTrace_1424421 : CollatzResearch.WordTrace tailWord_1424421 prefixEnd_1424421 731412627358076679986713 := by
  unfold tailWord_1424421
  simp only [CollatzResearch.WordTrace]
  refine ⟨51952901972573463584057117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34635267981715642389371411 51952901972573463584057117)
  ·
    refine ⟨19482338239715048844021419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51952901972573463584057117 19482338239715048844021419)
    ·
      refine ⟨29223507359572573266032129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19482338239715048844021419 29223507359572573266032129)
      ·
        refine ⟨21917630519679429949524097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29223507359572573266032129 21917630519679429949524097)
        ·
          refine ⟨16438222889759572462143073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21917630519679429949524097 16438222889759572462143073)
          ·
            refine ⟨12328667167319679346607305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16438222889759572462143073 12328667167319679346607305)
            ·
              refine ⟨9246500375489759509955479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12328667167319679346607305 9246500375489759509955479)
              ·
                refine ⟨13869750563234639264933219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246500375489759509955479 13869750563234639264933219)
                ·
                  refine ⟨20804625844851958897399829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13869750563234639264933219 20804625844851958897399829)
                  ·
                    refine ⟨975216836477435573315617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20804625844851958897399829 975216836477435573315617)
                    ·
                      refine ⟨731412627358076679986713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975216836477435573315617 731412627358076679986713)
                      ·
                        rfl

theorem cell23_1424421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_1424421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424421 prefixEnd_1424421 := by exact prefixLift 1424421
  have htrace : WordTrace (prefixWord ++ tailWord_1424421) baseStart_1424421 baseEnd_1424421 := by
    simpa [prefixWord, tailWord_1424421, baseEnd_1424421] using wordTrace_append hprefix tailTrace_1424421
  have hstable : (prefixWord ++ tailWord_1424421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424421).length < 2 ^ (prefixWord ++ tailWord_1424421).sum := by decide
  have hdescent : baseEnd_1424421 < baseStart_1424421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424438 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1424438 : Nat := 118140960795 + 1424438 * 2 ^ 59
def prefixEnd_1424438 : Nat := 4983230072969 + 3 ^ 40 * 1424438 * 2
def baseEnd_1424438 : Nat := 731421356529203113474135

theorem tailTrace_1424438 : CollatzResearch.WordTrace tailWord_1424438 prefixEnd_1424438 731421356529203113474135 := by
  unfold tailWord_1424438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247095125844492217964123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34635681342341250324950645 3247095125844492217964123)
  ·
    refine ⟨4870642688766738326946185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3247095125844492217964123 4870642688766738326946185)
    ·
      refine ⟨3652982016575053745209639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4870642688766738326946185 3652982016575053745209639)
      ·
        refine ⟨5479473024862580617814459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652982016575053745209639 5479473024862580617814459)
        ·
          refine ⟨8219209537293870926721689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479473024862580617814459 8219209537293870926721689)
          ·
            refine ⟨6164407152970403195041267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8219209537293870926721689 6164407152970403195041267)
            ·
              refine ⟨9246610729455604792561901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164407152970403195041267 9246610729455604792561901)
              ·
                refine ⟨3467479023545851797210713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9246610729455604792561901 3467479023545851797210713)
                ·
                  refine ⟨2600609267659388847908035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467479023545851797210713 2600609267659388847908035)
                  ·
                    refine ⟨3900913901489083271862053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2600609267659388847908035 3900913901489083271862053)
                    ·
                      refine ⟨731421356529203113474135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3900913901489083271862053 731421356529203113474135)
                      ·
                        rfl

theorem cell23_1424438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1424438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424438 prefixEnd_1424438 := by exact prefixLift 1424438
  have htrace : WordTrace (prefixWord ++ tailWord_1424438) baseStart_1424438 baseEnd_1424438 := by
    simpa [prefixWord, tailWord_1424438, baseEnd_1424438] using wordTrace_append hprefix tailTrace_1424438
  have hstable : (prefixWord ++ tailWord_1424438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424438).length < 2 ^ (prefixWord ++ tailWord_1424438).sum := by decide
  have hdescent : baseEnd_1424438 < baseStart_1424438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424448 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 1, 4]
def baseStart_1424448 : Nat := 118140960795 + 1424448 * 2 ^ 59
def prefixEnd_1424448 : Nat := 4983230072969 + 3 ^ 40 * 1424448 * 2
def baseEnd_1424448 : Nat := 243808830445249358116363

theorem tailTrace_1424448 : CollatzResearch.WordTrace tailWord_1424448 prefixEnd_1424448 243808830445249358116363 := by
  unfold tailWord_1424448
  simp only [CollatzResearch.WordTrace]
  refine ⟨25976943371737823597644999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34635924495650431463526665 25976943371737823597644999)
  ·
    refine ⟨38965415057606735396467499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25976943371737823597644999 38965415057606735396467499)
    ·
      refine ⟨58448122586410103094701249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38965415057606735396467499 58448122586410103094701249)
      ·
        refine ⟨43836091939807577321025937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58448122586410103094701249 43836091939807577321025937)
        ·
          refine ⟨32877068954855682990769453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43836091939807577321025937 32877068954855682990769453)
          ·
            refine ⟨12328900858070881121538545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32877068954855682990769453 12328900858070881121538545)
            ·
              refine ⟨9246675643553160841153909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12328900858070881121538545 9246675643553160841153909)
              ·
                refine ⟨866875841583108828858179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9246675643553160841153909 866875841583108828858179)
                ·
                  refine ⟨1300313762374663243287269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866875841583108828858179 1300313762374663243287269)
                  ·
                    refine ⟨243808830445249358116363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300313762374663243287269 243808830445249358116363)
                    ·
                      rfl

theorem cell23_1424448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 4].length) (baseStart_1424448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424448 prefixEnd_1424448 := by exact prefixLift 1424448
  have htrace : WordTrace (prefixWord ++ tailWord_1424448) baseStart_1424448 baseEnd_1424448 := by
    simpa [prefixWord, tailWord_1424448, baseEnd_1424448] using wordTrace_append hprefix tailTrace_1424448
  have hstable : (prefixWord ++ tailWord_1424448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424448).length < 2 ^ (prefixWord ++ tailWord_1424448).sum := by decide
  have hdescent : baseEnd_1424448 < baseStart_1424448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424465 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 1, 4]
def baseStart_1424465 : Nat := 118140960795 + 1424465 * 2 ^ 59
def prefixEnd_1424465 : Nat := 4983230072969 + 3 ^ 40 * 1424465 * 2
def baseEnd_1424465 : Nat := 243811740168958169278837

theorem tailTrace_1424465 : CollatzResearch.WordTrace tailWord_1424465 prefixEnd_1424465 243811740168958169278837 := by
  unfold tailWord_1424465
  simp only [CollatzResearch.WordTrace]
  refine ⟨51954506784414059098658849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34636337856276039399105899 51954506784414059098658849)
  ·
    refine ⟨38965880088310544323994137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51954506784414059098658849 38965880088310544323994137)
    ·
      refine ⟨29224410066232908242995603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38965880088310544323994137 29224410066232908242995603)
      ·
        refine ⟨43836615099349362364493405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29224410066232908242995603 43836615099349362364493405)
        ·
          refine ⟨16438730662256010886685027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43836615099349362364493405 16438730662256010886685027)
          ·
            refine ⟨24658095993384016330027541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16438730662256010886685027 24658095993384016330027541)
            ·
              refine ⟨1155848249689875765470041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24658095993384016330027541 1155848249689875765470041)
              ·
                refine ⟨866886187267406824102531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155848249689875765470041 866886187267406824102531)
                ·
                  refine ⟨1300329280901110236153797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866886187267406824102531 1300329280901110236153797)
                  ·
                    refine ⟨243811740168958169278837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300329280901110236153797 243811740168958169278837)
                    ·
                      rfl

theorem cell23_1424465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_1424465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424465 prefixEnd_1424465 := by exact prefixLift 1424465
  have htrace : WordTrace (prefixWord ++ tailWord_1424465) baseStart_1424465 baseEnd_1424465 := by
    simpa [prefixWord, tailWord_1424465, baseEnd_1424465] using wordTrace_append hprefix tailTrace_1424465
  have hstable : (prefixWord ++ tailWord_1424465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424465).length < 2 ^ (prefixWord ++ tailWord_1424465).sum := by decide
  have hdescent : baseEnd_1424465 < baseStart_1424465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424484 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_1424484 : Nat := 118140960795 + 1424484 * 2 ^ 59
def prefixEnd_1424484 : Nat := 4983230072969 + 3 ^ 40 * 1424484 * 2
def baseEnd_1424484 : Nat := 731444976639309933498923

theorem tailTrace_1424484 : CollatzResearch.WordTrace tailWord_1424484 prefixEnd_1424484 731444976639309933498923 := by
  unfold tailWord_1424484
  simp only [CollatzResearch.WordTrace]
  refine ⟨25977599885672612671800253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34636799847563483562400337 25977599885672612671800253)
  ·
    refine ⟨9741599957127229751925095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25977599885672612671800253 9741599957127229751925095)
    ·
      refine ⟨14612399935690844627887643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741599957127229751925095 14612399935690844627887643)
      ·
        refine ⟨21918599903536266941831465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14612399935690844627887643 21918599903536266941831465)
        ·
          refine ⟨16438949927652200206373599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21918599903536266941831465 16438949927652200206373599)
          ·
            refine ⟨24658424891478300309560399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16438949927652200206373599 24658424891478300309560399)
            ·
              refine ⟨36987637337217450464340599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24658424891478300309560399 36987637337217450464340599)
              ·
                refine ⟨55481456005826175696510899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36987637337217450464340599 55481456005826175696510899)
                ·
                  refine ⟨83222184008739263544766349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55481456005826175696510899 83222184008739263544766349)
                  ·
                    refine ⟨31208319003277223829287381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83222184008739263544766349 31208319003277223829287381)
                    ·
                      refine ⟨731444976639309933498923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31208319003277223829287381 731444976639309933498923)
                      ·
                        rfl

theorem cell23_1424484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_1424484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424484 prefixEnd_1424484 := by exact prefixLift 1424484
  have htrace : WordTrace (prefixWord ++ tailWord_1424484) baseStart_1424484 baseEnd_1424484 := by
    simpa [prefixWord, tailWord_1424484, baseEnd_1424484] using wordTrace_append hprefix tailTrace_1424484
  have hstable : (prefixWord ++ tailWord_1424484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424484).length < 2 ^ (prefixWord ++ tailWord_1424484).sum := by decide
  have hdescent : baseEnd_1424484 < baseStart_1424484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424498 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_1424498 : Nat := 118140960795 + 1424498 * 2 ^ 59
def prefixEnd_1424498 : Nat := 4983230072969 + 3 ^ 40 * 1424498 * 2
def baseEnd_1424498 : Nat := 731452165368472878723859

theorem tailTrace_1424498 : CollatzResearch.WordTrace tailWord_1424498 prefixEnd_1424498 731452165368472878723859 := by
  unfold tailWord_1424498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12988927598323626433652537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34637140262196337156406765 12988927598323626433652537)
  ·
    refine ⟨9741695698742719825239403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12988927598323626433652537 9741695698742719825239403)
    ·
      refine ⟨14612543548114079737859105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741695698742719825239403 14612543548114079737859105)
      ·
        refine ⟨10959407661085559803394329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14612543548114079737859105 10959407661085559803394329)
        ·
          refine ⟨8219555745814169852545747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10959407661085559803394329 8219555745814169852545747)
          ·
            refine ⟨12329333618721254778818621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219555745814169852545747 12329333618721254778818621)
            ·
              refine ⟨4623500107020470542056983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12329333618721254778818621 4623500107020470542056983)
              ·
                refine ⟨6935250160530705813085475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4623500107020470542056983 6935250160530705813085475)
                ·
                  refine ⟨10402875240796058719628213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935250160530705813085475 10402875240796058719628213)
                  ·
                    refine ⟨975269553824630504965145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10402875240796058719628213 975269553824630504965145)
                    ·
                      refine ⟨731452165368472878723859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975269553824630504965145 731452165368472878723859)
                      ·
                        rfl

theorem cell23_1424498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_1424498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424498 prefixEnd_1424498 := by exact prefixLift 1424498
  have htrace : WordTrace (prefixWord ++ tailWord_1424498) baseStart_1424498 baseEnd_1424498 := by
    simpa [prefixWord, tailWord_1424498, baseEnd_1424498] using wordTrace_append hprefix tailTrace_1424498
  have hstable : (prefixWord ++ tailWord_1424498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424498).length < 2 ^ (prefixWord ++ tailWord_1424498).sum := by decide
  have hdescent : baseEnd_1424498 < baseStart_1424498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424511 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 8, 2]
def baseStart_1424511 : Nat := 118140960795 + 1424511 * 2 ^ 59
def prefixEnd_1424511 : Nat := 4983230072969 + 3 ^ 40 * 1424511 * 2
def baseEnd_1424511 : Nat := 731458840616981327861299

theorem tailTrace_1424511 : CollatzResearch.WordTrace tailWord_1424511 prefixEnd_1424511 731458840616981327861299 := by
  unfold tailWord_1424511
  simp only [CollatzResearch.WordTrace]
  refine ⟨51956184542247408954833387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34637456361498272636555591 51956184542247408954833387)
  ·
    refine ⟨77934276813371113432250081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51956184542247408954833387 77934276813371113432250081)
    ·
      refine ⟨58450707610028335074187561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77934276813371113432250081 58450707610028335074187561)
      ·
        refine ⟨43838030707521251305640671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58450707610028335074187561 43838030707521251305640671)
        ·
          refine ⟨65757046061281876958461007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43838030707521251305640671 65757046061281876958461007)
          ·
            refine ⟨98635569091922815437691511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65757046061281876958461007 98635569091922815437691511)
            ·
              refine ⟨147953353637884223156537267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98635569091922815437691511 147953353637884223156537267)
              ·
                refine ⟨221930030456826334734805901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147953353637884223156537267 221930030456826334734805901)
                ·
                  refine ⟨83223761421309875525552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221930030456826334734805901 83223761421309875525552213)
                  ·
                    refine ⟨975278454155975103815065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83223761421309875525552213 975278454155975103815065)
                    ·
                      refine ⟨731458840616981327861299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975278454155975103815065 731458840616981327861299)
                      ·
                        rfl

theorem cell23_1424511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_1424511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424511 prefixEnd_1424511 := by exact prefixLift 1424511
  have htrace : WordTrace (prefixWord ++ tailWord_1424511) baseStart_1424511 baseEnd_1424511 := by
    simpa [prefixWord, tailWord_1424511, baseEnd_1424511] using wordTrace_append hprefix tailTrace_1424511
  have hstable : (prefixWord ++ tailWord_1424511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424511).length < 2 ^ (prefixWord ++ tailWord_1424511).sum := by decide
  have hdescent : baseEnd_1424511 < baseStart_1424511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424531 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 3]
def baseStart_1424531 : Nat := 118140960795 + 1424531 * 2 ^ 59
def prefixEnd_1424531 : Nat := 4983230072969 + 3 ^ 40 * 1424531 * 2
def baseEnd_1424531 : Nat := 731469110230071249611207

theorem tailTrace_1424531 : CollatzResearch.WordTrace tailWord_1424531 prefixEnd_1424531 731469110230071249611207 := by
  unfold tailWord_1424531
  simp only [CollatzResearch.WordTrace]
  refine ⟨51956914002174952370561447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34637942668116634913707631 51956914002174952370561447)
  ·
    refine ⟨77935371003262428555842171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51956914002174952370561447 77935371003262428555842171)
    ·
      refine ⟨116903056504893642833763257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77935371003262428555842171 116903056504893642833763257)
      ·
        refine ⟨87677292378670232125322443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116903056504893642833763257 87677292378670232125322443)
        ·
          refine ⟨131515938568005348187983665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87677292378670232125322443 131515938568005348187983665)
          ·
            refine ⟨98636953926004011140987749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131515938568005348187983665 98636953926004011140987749)
            ·
              refine ⟨18494428861125752088935203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98636953926004011140987749 18494428861125752088935203)
              ·
                refine ⟨27741643291688628133402805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18494428861125752088935203 27741643291688628133402805)
                ·
                  refine ⟨2600779058595808887506513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27741643291688628133402805 2600779058595808887506513)
                  ·
                    refine ⟨1950584293946856665629885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600779058595808887506513 1950584293946856665629885)
                    ·
                      refine ⟨731469110230071249611207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950584293946856665629885 731469110230071249611207)
                      ·
                        rfl

theorem cell23_1424531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_1424531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424531 prefixEnd_1424531 := by exact prefixLift 1424531
  have htrace : WordTrace (prefixWord ++ tailWord_1424531) baseStart_1424531 baseEnd_1424531 := by
    simpa [prefixWord, tailWord_1424531, baseEnd_1424531] using wordTrace_append hprefix tailTrace_1424531
  have hstable : (prefixWord ++ tailWord_1424531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424531).length < 2 ^ (prefixWord ++ tailWord_1424531).sum := by decide
  have hdescent : baseEnd_1424531 < baseStart_1424531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424538 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_1424538 : Nat := 118140960795 + 1424538 * 2 ^ 59
def prefixEnd_1424538 : Nat := 4983230072969 + 3 ^ 40 * 1424538 * 2
def baseEnd_1424538 : Nat := 243824234864884240741225

theorem tailTrace_1424538 : CollatzResearch.WordTrace tailWord_1424538 prefixEnd_1424538 243824234864884240741225 := by
  unfold tailWord_1424538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989292328287398141516567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34638112875433061710710845 12989292328287398141516567)
  ·
    refine ⟨19483938492431097212274851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12989292328287398141516567 19483938492431097212274851)
    ·
      refine ⟨29225907738646645818412277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19483938492431097212274851 29225907738646645818412277)
      ·
        refine ⟨2739928850498123045476151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29225907738646645818412277 2739928850498123045476151)
        ·
          refine ⟨4109893275747184568214227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739928850498123045476151 4109893275747184568214227)
          ·
            refine ⟨6164839913620776852321341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109893275747184568214227 6164839913620776852321341)
            ·
              refine ⟨2311814967607791319620503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6164839913620776852321341 2311814967607791319620503)
              ·
                refine ⟨3467722451411686979430755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311814967607791319620503 3467722451411686979430755)
                ·
                  refine ⟨5201583677117530469146133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467722451411686979430755 5201583677117530469146133)
                  ·
                    refine ⟨243824234864884240741225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5201583677117530469146133 243824234864884240741225)
                    ·
                      rfl

theorem cell23_1424538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_1424538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424538 prefixEnd_1424538 := by exact prefixLift 1424538
  have htrace : WordTrace (prefixWord ++ tailWord_1424538) baseStart_1424538 baseEnd_1424538 := by
    simpa [prefixWord, tailWord_1424538, baseEnd_1424538] using wordTrace_append hprefix tailTrace_1424538
  have hstable : (prefixWord ++ tailWord_1424538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424538).length < 2 ^ (prefixWord ++ tailWord_1424538).sum := by decide
  have hdescent : baseEnd_1424538 < baseStart_1424538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424541 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1424541 : Nat := 118140960795 + 1424541 * 2 ^ 59
def prefixEnd_1424541 : Nat := 4983230072969 + 3 ^ 40 * 1424541 * 2
def baseEnd_1424541 : Nat := 731474245036616210486161

theorem tailTrace_1424541 : CollatzResearch.WordTrace tailWord_1424541 prefixEnd_1424541 731474245036616210486161 := by
  unfold tailWord_1424541
  simp only [CollatzResearch.WordTrace]
  refine ⟨51957278732138724078425477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34638185821425816052283651 51957278732138724078425477)
  ·
    refine ⟨9741989762276010764704777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51957278732138724078425477 9741989762276010764704777)
    ·
      refine ⟨7306492321707008073528583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9741989762276010764704777 7306492321707008073528583)
      ·
        refine ⟨10959738482560512110292875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7306492321707008073528583 10959738482560512110292875)
        ·
          refine ⟨16439607723840768165439313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10959738482560512110292875 16439607723840768165439313)
          ·
            refine ⟨12329705792880576124079485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16439607723840768165439313 12329705792880576124079485)
            ·
              refine ⟨4623639672330216046529807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12329705792880576124079485 4623639672330216046529807)
              ·
                refine ⟨6935459508495324069794711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4623639672330216046529807 6935459508495324069794711)
                ·
                  refine ⟨10403189262742986104692067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935459508495324069794711 10403189262742986104692067)
                  ·
                    refine ⟨15604783894114479157038101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10403189262742986104692067 15604783894114479157038101)
                    ·
                      refine ⟨731474245036616210486161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15604783894114479157038101 731474245036616210486161)
                      ·
                        rfl

theorem cell23_1424541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1424541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424541 prefixEnd_1424541 := by exact prefixLift 1424541
  have htrace : WordTrace (prefixWord ++ tailWord_1424541) baseStart_1424541 baseEnd_1424541 := by
    simpa [prefixWord, tailWord_1424541, baseEnd_1424541] using wordTrace_append hprefix tailTrace_1424541
  have hstable : (prefixWord ++ tailWord_1424541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424541).length < 2 ^ (prefixWord ++ tailWord_1424541).sum := by decide
  have hdescent : baseEnd_1424541 < baseStart_1424541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424545 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_1424545 : Nat := 118140960795 + 1424545 * 2 ^ 59
def prefixEnd_1424545 : Nat := 4983230072969 + 3 ^ 40 * 1424545 * 2
def baseEnd_1424545 : Nat := 731476298959234194836143

theorem tailTrace_1424545 : CollatzResearch.WordTrace tailWord_1424545 prefixEnd_1424545 731476298959234194836143 := by
  unfold tailWord_1424545
  simp only [CollatzResearch.WordTrace]
  refine ⟨51957424624124232761571089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34638283082749488507714059 51957424624124232761571089)
  ·
    refine ⟨38968068468093174571178317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51957424624124232761571089 38968068468093174571178317)
    ·
      refine ⟨14613025675534940464191869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38968068468093174571178317 14613025675534940464191869)
      ·
        refine ⟨5479884628325602674071951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14613025675534940464191869 5479884628325602674071951)
        ·
          refine ⟨8219826942488404011107927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479884628325602674071951 8219826942488404011107927)
          ·
            refine ⟨12329740413732606016661891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219826942488404011107927 12329740413732606016661891)
            ·
              refine ⟨18494610620598909024992837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12329740413732606016661891 18494610620598909024992837)
              ·
                refine ⟨3467739491362295442186157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18494610620598909024992837 3467739491362295442186157)
                ·
                  refine ⟨1300402309260860790819809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3467739491362295442186157 1300402309260860790819809)
                  ·
                    refine ⟨975301731945645593114857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300402309260860790819809 975301731945645593114857)
                    ·
                      refine ⟨731476298959234194836143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975301731945645593114857 731476298959234194836143)
                      ·
                        rfl

theorem cell23_1424545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_1424545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424545 prefixEnd_1424545 := by exact prefixLift 1424545
  have htrace : WordTrace (prefixWord ++ tailWord_1424545) baseStart_1424545 baseEnd_1424545 := by
    simpa [prefixWord, tailWord_1424545, baseEnd_1424545] using wordTrace_append hprefix tailTrace_1424545
  have hstable : (prefixWord ++ tailWord_1424545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424545).length < 2 ^ (prefixWord ++ tailWord_1424545).sum := by decide
  have hdescent : baseEnd_1424545 < baseStart_1424545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424589 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1424589 : Nat := 118140960795 + 1424589 * 2 ^ 59
def prefixEnd_1424589 : Nat := 4983230072969 + 3 ^ 40 * 1424589 * 2
def baseEnd_1424589 : Nat := 243832964036010674228647

theorem tailTrace_1424589 : CollatzResearch.WordTrace tailWord_1424589 prefixEnd_1424589 243832964036010674228647 := by
  unfold tailWord_1424589
  simp only [CollatzResearch.WordTrace]
  refine ⟨51959029435964828276172821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34639352957309885517448547 51959029435964828276172821)
  ·
    refine ⟨2435579504810851325445601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51959029435964828276172821 2435579504810851325445601)
    ·
      refine ⟨1826684628608138494084201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2435579504810851325445601 1826684628608138494084201)
      ·
        refine ⟨1370013471456103870563151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1826684628608138494084201 1370013471456103870563151)
        ·
          refine ⟨2055020207184155805844727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370013471456103870563151 2055020207184155805844727)
          ·
            refine ⟨3082530310776233708767091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055020207184155805844727 3082530310776233708767091)
            ·
              refine ⟨4623795466164350563150637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082530310776233708767091 4623795466164350563150637)
              ·
                refine ⟨1733923299811631461181489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4623795466164350563150637 1733923299811631461181489)
                ·
                  refine ⟨1300442474858723595886117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733923299811631461181489 1300442474858723595886117)
                  ·
                    refine ⟨243832964036010674228647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300442474858723595886117 243832964036010674228647)
                    ·
                      rfl

theorem cell23_1424589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1424589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424589 prefixEnd_1424589 := by exact prefixLift 1424589
  have htrace : WordTrace (prefixWord ++ tailWord_1424589) baseStart_1424589 baseEnd_1424589 := by
    simpa [prefixWord, tailWord_1424589, baseEnd_1424589] using wordTrace_append hprefix tailTrace_1424589
  have hstable : (prefixWord ++ tailWord_1424589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424589).length < 2 ^ (prefixWord ++ tailWord_1424589).sum := by decide
  have hdescent : baseEnd_1424589 < baseStart_1424589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424631 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_1424631 : Nat := 118140960795 + 1424631 * 2 ^ 59
def prefixEnd_1424631 : Nat := 4983230072969 + 3 ^ 40 * 1424631 * 2
def baseEnd_1424631 : Nat := 731520458295520858360747

theorem tailTrace_1424631 : CollatzResearch.WordTrace tailWord_1424631 prefixEnd_1424631 731520458295520858360747 := by
  unfold tailWord_1424631
  simp only [CollatzResearch.WordTrace]
  refine ⟨51960561301812669449201747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34640374201208446299467831 51960561301812669449201747)
  ·
    refine ⟨77940841952719004173802621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51960561301812669449201747 77940841952719004173802621)
    ·
      refine ⟨29227815732269626565175983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77940841952719004173802621 29227815732269626565175983)
      ·
        refine ⟨43841723598404439847763975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29227815732269626565175983 43841723598404439847763975)
        ·
          refine ⟨65762585397606659771645963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43841723598404439847763975 65762585397606659771645963)
          ·
            refine ⟨98643878096409989657468945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65762585397606659771645963 98643878096409989657468945)
            ·
              refine ⟨73982908572307492243101709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98643878096409989657468945 73982908572307492243101709)
              ·
                refine ⟨27743590714615309591163141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73982908572307492243101709 27743590714615309591163141)
                ·
                  refine ⟨5201923258990370548343089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27743590714615309591163141 5201923258990370548343089)
                  ·
                    refine ⟨3901442444242777911257317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201923258990370548343089 3901442444242777911257317)
                    ·
                      refine ⟨731520458295520858360747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3901442444242777911257317 731520458295520858360747)
                      ·
                        rfl

theorem cell23_1424631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_1424631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424631 prefixEnd_1424631 := by exact prefixLift 1424631
  have htrace : WordTrace (prefixWord ++ tailWord_1424631) baseStart_1424631 baseEnd_1424631 := by
    simpa [prefixWord, tailWord_1424631, baseEnd_1424631] using wordTrace_append hprefix tailTrace_1424631
  have hstable : (prefixWord ++ tailWord_1424631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424631).length < 2 ^ (prefixWord ++ tailWord_1424631).sum := by decide
  have hdescent : baseEnd_1424631 < baseStart_1424631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424652 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 2, 2, 2]
def baseStart_1424652 : Nat := 118140960795 + 1424652 * 2 ^ 59
def prefixEnd_1424652 : Nat := 4983230072969 + 3 ^ 40 * 1424652 * 2
def baseEnd_1424652 : Nat := 731531241389265276198151

theorem tailTrace_1424652 : CollatzResearch.WordTrace tailWord_1424652 prefixEnd_1424652 731531241389265276198151 := by
  unfold tailWord_1424652
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980663617368295017858105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34640884823157726690477473 25980663617368295017858105)
  ·
    refine ⟨19485497713026221263393579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25980663617368295017858105 19485497713026221263393579)
    ·
      refine ⟨29228246569539331895090369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19485497713026221263393579 29228246569539331895090369)
      ·
        refine ⟨21921184927154498921317777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29228246569539331895090369 21921184927154498921317777)
        ·
          refine ⟨16440888695365874190988333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21921184927154498921317777 16440888695365874190988333)
          ·
            refine ⟨6165333260762202821620625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16440888695365874190988333 6165333260762202821620625)
            ·
              refine ⟨4623999945571652116215469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6165333260762202821620625 4623999945571652116215469)
              ·
                refine ⟨1733999979589369543580801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4623999945571652116215469 1733999979589369543580801)
                ·
                  refine ⟨1300499984692027157685601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733999979589369543580801 1300499984692027157685601)
                  ·
                    refine ⟨975374988519020368264201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300499984692027157685601 975374988519020368264201)
                    ·
                      refine ⟨731531241389265276198151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975374988519020368264201 731531241389265276198151)
                      ·
                        rfl

theorem cell23_1424652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_1424652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424652 prefixEnd_1424652 := by exact prefixLift 1424652
  have htrace : WordTrace (prefixWord ++ tailWord_1424652) baseStart_1424652 baseEnd_1424652 := by
    simpa [prefixWord, tailWord_1424652, baseEnd_1424652] using wordTrace_append hprefix tailTrace_1424652
  have hstable : (prefixWord ++ tailWord_1424652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424652).length < 2 ^ (prefixWord ++ tailWord_1424652).sum := by decide
  have hdescent : baseEnd_1424652 < baseStart_1424652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424675 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 5]
def baseStart_1424675 : Nat := 118140960795 + 1424675 * 2 ^ 59
def prefixEnd_1424675 : Nat := 4983230072969 + 3 ^ 40 * 1424675 * 2
def baseEnd_1424675 : Nat := 81282561271590965134505

theorem tailTrace_1424675 : CollatzResearch.WordTrace tailWord_1424675 prefixEnd_1424675 81282561271590965134505 := by
  unfold tailWord_1424675
  simp only [CollatzResearch.WordTrace]
  refine ⟨51962166113653264963803479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34641444075768843309202319 51962166113653264963803479)
  ·
    refine ⟨77943249170479897445705219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51962166113653264963803479 77943249170479897445705219)
    ·
      refine ⟨116914873755719846168557829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77943249170479897445705219 116914873755719846168557829)
      ·
        refine ⟨21921538829197471156604593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116914873755719846168557829 21921538829197471156604593)
        ·
          refine ⟨16441154121898103367453445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21921538829197471156604593 16441154121898103367453445)
          ·
            refine ⟨3082716397855894381397521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16441154121898103367453445 3082716397855894381397521)
            ·
              refine ⟨2312037298391920786048141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3082716397855894381397521 2312037298391920786048141)
              ·
                refine ⟨867013986896970294768053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2312037298391920786048141 867013986896970294768053)
                ·
                  refine ⟨81282561271590965134505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 867013986896970294768053 81282561271590965134505)
                  ·
                    rfl

theorem cell23_1424675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 5].length) (baseStart_1424675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424675 prefixEnd_1424675 := by exact prefixLift 1424675
  have htrace : WordTrace (prefixWord ++ tailWord_1424675) baseStart_1424675 baseEnd_1424675 := by
    simpa [prefixWord, tailWord_1424675, baseEnd_1424675] using wordTrace_append hprefix tailTrace_1424675
  have hstable : (prefixWord ++ tailWord_1424675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424675).length < 2 ^ (prefixWord ++ tailWord_1424675).sum := by decide
  have hdescent : baseEnd_1424675 < baseStart_1424675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424728 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1424728 : Nat := 118140960795 + 1424728 * 2 ^ 59
def prefixEnd_1424728 : Nat := 4983230072969 + 3 ^ 40 * 1424728 * 2
def baseEnd_1424728 : Nat := 731570265919006978847801

theorem tailTrace_1424728 : CollatzResearch.WordTrace tailWord_1424728 prefixEnd_1424728 731570265919006978847801 := by
  unfold tailWord_1424728
  simp only [CollatzResearch.WordTrace]
  refine ⟨25982049591230627507741419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34642732788307503343655225 25982049591230627507741419)
  ·
    refine ⟨38973074386845941261612129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25982049591230627507741419 38973074386845941261612129)
    ·
      refine ⟨29229805790134455946209097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38973074386845941261612129 29229805790134455946209097)
      ·
        refine ⟨21922354342600841959656823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29229805790134455946209097 21922354342600841959656823)
        ·
          refine ⟨32883531513901262939485235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21922354342600841959656823 32883531513901262939485235)
          ·
            refine ⟨49325297270851894409227853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32883531513901262939485235 49325297270851894409227853)
            ·
              refine ⟨18496986476569460403460445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49325297270851894409227853 18496986476569460403460445)
              ·
                refine ⟨6936369928713547651297667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18496986476569460403460445 6936369928713547651297667)
                ·
                  refine ⟨10404554893070321476946501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936369928713547651297667 10404554893070321476946501)
                  ·
                    refine ⟨1950854042450685276927469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10404554893070321476946501 1950854042450685276927469)
                    ·
                      refine ⟨731570265919006978847801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1950854042450685276927469 731570265919006978847801)
                      ·
                        rfl

theorem cell23_1424728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1424728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424728 prefixEnd_1424728 := by exact prefixLift 1424728
  have htrace : WordTrace (prefixWord ++ tailWord_1424728) baseStart_1424728 baseEnd_1424728 := by
    simpa [prefixWord, tailWord_1424728, baseEnd_1424728] using wordTrace_append hprefix tailTrace_1424728
  have hstable : (prefixWord ++ tailWord_1424728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424728).length < 2 ^ (prefixWord ++ tailWord_1424728).sum := by decide
  have hdescent : baseEnd_1424728 < baseStart_1424728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424748 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 8]
def baseStart_1424748 : Nat := 118140960795 + 1424748 * 2 ^ 59
def prefixEnd_1424748 : Nat := 4983230072969 + 3 ^ 40 * 1424748 * 2
def baseEnd_1424748 : Nat := 81286726170232988955301

theorem tailTrace_1424748 : CollatzResearch.WordTrace tailWord_1424748 prefixEnd_1424748 81286726170232988955301 := by
  unfold tailWord_1424748
  simp only [CollatzResearch.WordTrace]
  refine ⟨25982414321194399215605449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34643219094925865620807265 25982414321194399215605449)
  ·
    refine ⟨19486810740895799411704087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25982414321194399215605449 19486810740895799411704087)
    ·
      refine ⟨29230216111343699117556131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19486810740895799411704087 29230216111343699117556131)
      ·
        refine ⟨43845324167015548676334197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29230216111343699117556131 43845324167015548676334197)
        ·
          refine ⟨4110499140657707688406331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43845324167015548676334197 4110499140657707688406331)
          ·
            refine ⟨6165748710986561532609497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110499140657707688406331 6165748710986561532609497)
            ·
              refine ⟨4624311533239921149457123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6165748710986561532609497 4624311533239921149457123)
              ·
                refine ⟨6936467299859881724185685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624311533239921149457123 6936467299859881724185685)
                ·
                  refine ⟨81286726170232988955301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6936467299859881724185685 81286726170232988955301)
                  ·
                    rfl

theorem cell23_1424748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_1424748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424748 prefixEnd_1424748 := by exact prefixLift 1424748
  have htrace : WordTrace (prefixWord ++ tailWord_1424748) baseStart_1424748 baseEnd_1424748 := by
    simpa [prefixWord, tailWord_1424748, baseEnd_1424748] using wordTrace_append hprefix tailTrace_1424748
  have hstable : (prefixWord ++ tailWord_1424748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424748).length < 2 ^ (prefixWord ++ tailWord_1424748).sum := by decide
  have hdescent : baseEnd_1424748 < baseStart_1424748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424785 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 6, 3, 2]
def baseStart_1424785 : Nat := 118140960795 + 1424785 * 2 ^ 59
def prefixEnd_1424785 : Nat := 4983230072969 + 3 ^ 40 * 1424785 * 2
def baseEnd_1424785 : Nat := 731599534316313255835039

theorem tailTrace_1424785 : CollatzResearch.WordTrace tailWord_1424785 prefixEnd_1424785 731599534316313255835039 := by
  unfold tailWord_1424785
  simp only [CollatzResearch.WordTrace]
  refine ⟨51966178143254753750307809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34644118762169835833538539 51966178143254753750307809)
  ·
    refine ⟨38974633607441065312730857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51966178143254753750307809 38974633607441065312730857)
    ·
      refine ⟨29230975205580798984548143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38974633607441065312730857 29230975205580798984548143)
      ·
        refine ⟨43846462808371198476822215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29230975205580798984548143 43846462808371198476822215)
        ·
          refine ⟨65769694212556797715233323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43846462808371198476822215 65769694212556797715233323)
          ·
            refine ⟨98654541318835196572849985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65769694212556797715233323 98654541318835196572849985)
            ·
              refine ⟨73990905989126397429637489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98654541318835196572849985 73990905989126397429637489)
              ·
                refine ⟨55493179491844798072228117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73990905989126397429637489 55493179491844798072228117)
                ·
                  refine ⟨2601242788680224909635693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55493179491844798072228117 2601242788680224909635693)
                  ·
                    refine ⟨975466045755084341113385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601242788680224909635693 975466045755084341113385)
                    ·
                      refine ⟨731599534316313255835039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975466045755084341113385 731599534316313255835039)
                      ·
                        rfl

theorem cell23_1424785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_1424785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424785 prefixEnd_1424785 := by exact prefixLift 1424785
  have htrace : WordTrace (prefixWord ++ tailWord_1424785) baseStart_1424785 baseEnd_1424785 := by
    simpa [prefixWord, tailWord_1424785, baseEnd_1424785] using wordTrace_append hprefix tailTrace_1424785
  have hstable : (prefixWord ++ tailWord_1424785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424785).length < 2 ^ (prefixWord ++ tailWord_1424785).sum := by decide
  have hdescent : baseEnd_1424785 < baseStart_1424785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424832 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 5, 2, 2]
def baseStart_1424832 : Nat := 118140960795 + 1424832 * 2 ^ 59
def prefixEnd_1424832 : Nat := 4983230072969 + 3 ^ 40 * 1424832 * 2
def baseEnd_1424832 : Nat := 731623667907074571947323

theorem tailTrace_1424832 : CollatzResearch.WordTrace tailWord_1424832 prefixEnd_1424832 731623667907074571947323 := by
  unfold tailWord_1424832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25983946187042240388634375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34645261582722987184845833 25983946187042240388634375)
  ·
    refine ⟨38975919280563360582951563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25983946187042240388634375 38975919280563360582951563)
    ·
      refine ⟨58463878920845040874427345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38975919280563360582951563 58463878920845040874427345)
      ·
        refine ⟨43847909190633780655820509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58463878920845040874427345 43847909190633780655820509)
        ·
          refine ⟨16442965946487667745932691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43847909190633780655820509 16442965946487667745932691)
          ·
            refine ⟨24664448919731501618899037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16442965946487667745932691 24664448919731501618899037)
            ·
              refine ⟨9249168344899313107087139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24664448919731501618899037 9249168344899313107087139)
              ·
                refine ⟨13873752517348969660630709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9249168344899313107087139 13873752517348969660630709)
                ·
                  refine ⟨1300664298501465905684129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13873752517348969660630709 1300664298501465905684129)
                  ·
                    refine ⟨975498223876099429263097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300664298501465905684129 975498223876099429263097)
                    ·
                      refine ⟨731623667907074571947323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975498223876099429263097 731623667907074571947323)
                      ·
                        rfl

theorem cell23_1424832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_1424832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424832 prefixEnd_1424832 := by exact prefixLift 1424832
  have htrace : WordTrace (prefixWord ++ tailWord_1424832) baseStart_1424832 baseEnd_1424832 := by
    simpa [prefixWord, tailWord_1424832, baseEnd_1424832] using wordTrace_append hprefix tailTrace_1424832
  have hstable : (prefixWord ++ tailWord_1424832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424832).length < 2 ^ (prefixWord ++ tailWord_1424832).sum := by decide
  have hdescent : baseEnd_1424832 < baseStart_1424832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424835 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 3]
def baseStart_1424835 : Nat := 118140960795 + 1424835 * 2 ^ 59
def prefixEnd_1424835 : Nat := 4983230072969 + 3 ^ 40 * 1424835 * 2
def baseEnd_1424835 : Nat := 731625208349038060209809

theorem tailTrace_1424835 : CollatzResearch.WordTrace tailWord_1424835 prefixEnd_1424835 731625208349038060209809 := by
  unfold tailWord_1424835
  simp only [CollatzResearch.WordTrace]
  refine ⟨51968001793073612289627959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34645334528715741526418639 51968001793073612289627959)
  ·
    refine ⟨77952002689610418434441939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51968001793073612289627959 77952002689610418434441939)
    ·
      refine ⟨116928004034415627651662909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77952002689610418434441939 116928004034415627651662909)
      ·
        refine ⟨43848001512905860369373591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116928004034415627651662909 43848001512905860369373591)
        ·
          refine ⟨65772002269358790554060387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43848001512905860369373591 65772002269358790554060387)
          ·
            refine ⟨98658003404038185831090581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65772002269358790554060387 98658003404038185831090581)
            ·
              refine ⟨4624593909564289960832371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98658003404038185831090581 4624593909564289960832371)
              ·
                refine ⟨6936890864346434941248557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624593909564289960832371 6936890864346434941248557)
                ·
                  refine ⟨2601334074129913102968209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6936890864346434941248557 2601334074129913102968209)
                  ·
                    refine ⟨1951000555597434827226157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2601334074129913102968209 1951000555597434827226157)
                    ·
                      refine ⟨731625208349038060209809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1951000555597434827226157 731625208349038060209809)
                      ·
                        rfl

theorem cell23_1424835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_1424835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424835 prefixEnd_1424835 := by exact prefixLift 1424835
  have htrace : WordTrace (prefixWord ++ tailWord_1424835) baseStart_1424835 baseEnd_1424835 := by
    simpa [prefixWord, tailWord_1424835, baseEnd_1424835] using wordTrace_append hprefix tailTrace_1424835
  have hstable : (prefixWord ++ tailWord_1424835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424835).length < 2 ^ (prefixWord ++ tailWord_1424835).sum := by decide
  have hdescent : baseEnd_1424835 < baseStart_1424835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424836 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_1424836 : Nat := 118140960795 + 1424836 * 2 ^ 59
def prefixEnd_1424836 : Nat := 4983230072969 + 3 ^ 40 * 1424836 * 2
def baseEnd_1424836 : Nat := 731625721829692556297305

theorem tailTrace_1424836 : CollatzResearch.WordTrace tailWord_1424836 prefixEnd_1424836 731625721829692556297305 := by
  unfold tailWord_1424836
  simp only [CollatzResearch.WordTrace]
  refine ⟨25984019133034994730207181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34645358844046659640276241 25984019133034994730207181)
  ·
    refine ⟨9744007174888123023827693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25984019133034994730207181 9744007174888123023827693)
    ·
      refine ⟨3654002690583046133935385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9744007174888123023827693 3654002690583046133935385)
      ·
        refine ⟨2740502017937284600451539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3654002690583046133935385 2740502017937284600451539)
        ·
          refine ⟨4110753026905926900677309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740502017937284600451539 4110753026905926900677309)
          ·
            refine ⟨1541532385089722587753991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4110753026905926900677309 1541532385089722587753991)
            ·
              refine ⟨2312298577634583881630987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541532385089722587753991 2312298577634583881630987)
              ·
                refine ⟨3468447866451875822446481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312298577634583881630987 3468447866451875822446481)
                ·
                  refine ⟨2601335899838906866834861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468447866451875822446481 2601335899838906866834861)
                  ·
                    refine ⟨975500962439590075063073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601335899838906866834861 975500962439590075063073)
                    ·
                      refine ⟨731625721829692556297305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975500962439590075063073 731625721829692556297305)
                      ·
                        rfl

theorem cell23_1424836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_1424836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424836 prefixEnd_1424836 := by exact prefixLift 1424836
  have htrace : WordTrace (prefixWord ++ tailWord_1424836) baseStart_1424836 baseEnd_1424836 := by
    simpa [prefixWord, tailWord_1424836, baseEnd_1424836] using wordTrace_append hprefix tailTrace_1424836
  have hstable : (prefixWord ++ tailWord_1424836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424836).length < 2 ^ (prefixWord ++ tailWord_1424836).sum := by decide
  have hdescent : baseEnd_1424836 < baseStart_1424836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424868 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1424868 : Nat := 118140960795 + 1424868 * 2 ^ 59
def prefixEnd_1424868 : Nat := 4983230072969 + 3 ^ 40 * 1424868 * 2
def baseEnd_1424868 : Nat := 243880717736878810365719

theorem tailTrace_1424868 : CollatzResearch.WordTrace tailWord_1424868 prefixEnd_1424868 243880717736878810365719 := by
  unfold tailWord_1424868
  simp only [CollatzResearch.WordTrace]
  refine ⟨25984602700977029462789629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34646136934636039283719505 25984602700977029462789629)
  ·
    refine ⟨9744226012866386048546111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25984602700977029462789629 9744226012866386048546111)
    ·
      refine ⟨14616339019299579072819167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9744226012866386048546111 14616339019299579072819167)
      ·
        refine ⟨21924508528949368609228751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14616339019299579072819167 21924508528949368609228751)
        ·
          refine ⟨32886762793424052913843127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21924508528949368609228751 32886762793424052913843127)
          ·
            refine ⟨49330144190136079370764691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32886762793424052913843127 49330144190136079370764691)
            ·
              refine ⟨73995216285204119056147037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49330144190136079370764691 73995216285204119056147037)
              ·
                refine ⟨27748206106951544646055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73995216285204119056147037 27748206106951544646055139)
                ·
                  refine ⟨41622309160427316969082709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27748206106951544646055139 41622309160427316969082709)
                  ·
                    refine ⟨243880717736878810365719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 41622309160427316969082709 243880717736878810365719)
                    ·
                      rfl

theorem cell23_1424868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1424868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424868 prefixEnd_1424868 := by exact prefixLift 1424868
  have htrace : WordTrace (prefixWord ++ tailWord_1424868) baseStart_1424868 baseEnd_1424868 := by
    simpa [prefixWord, tailWord_1424868, baseEnd_1424868] using wordTrace_append hprefix tailTrace_1424868
  have hstable : (prefixWord ++ tailWord_1424868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424868).length < 2 ^ (prefixWord ++ tailWord_1424868).sum := by decide
  have hdescent : baseEnd_1424868 < baseStart_1424868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424875 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 7, 2]
def baseStart_1424875 : Nat := 118140960795 + 1424875 * 2 ^ 59
def prefixEnd_1424875 : Nat := 4983230072969 + 3 ^ 40 * 1424875 * 2
def baseEnd_1424875 : Nat := 731645747575217903709625

theorem tailTrace_1424875 : CollatzResearch.WordTrace tailWord_1424875 prefixEnd_1424875 731645747575217903709625 := by
  unfold tailWord_1424875
  simp only [CollatzResearch.WordTrace]
  refine ⟨51969460712928699121084079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34646307141952466080722719 51969460712928699121084079)
  ·
    refine ⟨77954191069393048681626119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51969460712928699121084079 77954191069393048681626119)
    ·
      refine ⟨116931286604089573022439179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77954191069393048681626119 116931286604089573022439179)
      ·
        refine ⟨175396929906134359533658769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116931286604089573022439179 175396929906134359533658769)
        ·
          refine ⟨131547697429600769650244077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175396929906134359533658769 131547697429600769650244077)
          ·
            refine ⟨49330386536100288618841529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131547697429600769650244077 49330386536100288618841529)
            ·
              refine ⟨36997789902075216464131147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49330386536100288618841529 36997789902075216464131147)
              ·
                refine ⟨55496684853112824696196721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36997789902075216464131147 55496684853112824696196721)
                ·
                  refine ⟨41622513639834618522147541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55496684853112824696196721 41622513639834618522147541)
                  ·
                    refine ⟨975527663433623871612833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41622513639834618522147541 975527663433623871612833)
                    ·
                      refine ⟨731645747575217903709625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975527663433623871612833 731645747575217903709625)
                      ·
                        rfl

theorem cell23_1424875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7, 2].length) (baseStart_1424875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424875 prefixEnd_1424875 := by exact prefixLift 1424875
  have htrace : WordTrace (prefixWord ++ tailWord_1424875) baseStart_1424875 baseEnd_1424875 := by
    simpa [prefixWord, tailWord_1424875, baseEnd_1424875] using wordTrace_append hprefix tailTrace_1424875
  have hstable : (prefixWord ++ tailWord_1424875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424875).length < 2 ^ (prefixWord ++ tailWord_1424875).sum := by decide
  have hdescent : baseEnd_1424875 < baseStart_1424875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424892 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_1424892 : Nat := 118140960795 + 1424892 * 2 ^ 59
def prefixEnd_1424892 : Nat := 4983230072969 + 3 ^ 40 * 1424892 * 2
def baseEnd_1424892 : Nat := 731654476746344337197047

theorem tailTrace_1424892 : CollatzResearch.WordTrace tailWord_1424892 prefixEnd_1424892 731654476746344337197047 := by
  unfold tailWord_1424892
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985040376933555512226465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34646720502578074016301953 25985040376933555512226465)
  ·
    refine ⟨19488780282700166634169849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25985040376933555512226465 19488780282700166634169849)
    ·
      refine ⟨14616585212025124975627387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19488780282700166634169849 14616585212025124975627387)
      ·
        refine ⟨21924877818037687463441081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14616585212025124975627387 21924877818037687463441081)
        ·
          refine ⟨16443658363528265597580811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21924877818037687463441081 16443658363528265597580811)
          ·
            refine ⟨24665487545292398396371217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16443658363528265597580811 24665487545292398396371217)
            ·
              refine ⟨18499115658969298797278413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24665487545292398396371217 18499115658969298797278413)
              ·
                refine ⟨6937168372113487048979405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18499115658969298797278413 6937168372113487048979405)
                ·
                  refine ⟨2601438139542557643367277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6937168372113487048979405 2601438139542557643367277)
                  ·
                    refine ⟨975539302328459116262729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601438139542557643367277 975539302328459116262729)
                    ·
                      refine ⟨731654476746344337197047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975539302328459116262729 731654476746344337197047)
                      ·
                        rfl

theorem cell23_1424892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_1424892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424892 prefixEnd_1424892 := by exact prefixLift 1424892
  have htrace : WordTrace (prefixWord ++ tailWord_1424892) baseStart_1424892 baseEnd_1424892 := by
    simpa [prefixWord, tailWord_1424892, baseEnd_1424892] using wordTrace_append hprefix tailTrace_1424892
  have hstable : (prefixWord ++ tailWord_1424892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424892).length < 2 ^ (prefixWord ++ tailWord_1424892).sum := by decide
  have hdescent : baseEnd_1424892 < baseStart_1424892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424900 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1424900 : Nat := 118140960795 + 1424900 * 2 ^ 59
def prefixEnd_1424900 : Nat := 4983230072969 + 3 ^ 40 * 1424900 * 2
def baseEnd_1424900 : Nat := 731658584591580305897011

theorem tailTrace_1424900 : CollatzResearch.WordTrace tailWord_1424900 prefixEnd_1424900 731658584591580305897011 := by
  unfold tailWord_1424900
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985186268919064195372077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34646915025225418927162769 25985186268919064195372077)
  ·
    refine ⟨9744444850844649073264529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25985186268919064195372077 9744444850844649073264529)
    ·
      refine ⟨7308333638133486804948397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9744444850844649073264529 7308333638133486804948397)
      ·
        refine ⟨2740625114300057551855649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7308333638133486804948397 2740625114300057551855649)
        ·
          refine ⟨2055468835725043163891737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740625114300057551855649 2055468835725043163891737)
          ·
            refine ⟨1541601626793782372918803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2055468835725043163891737 1541601626793782372918803)
            ·
              refine ⟨2312402440190673559378205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541601626793782372918803 2312402440190673559378205)
              ·
                refine ⟨867150915071502584766827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2312402440190673559378205 867150915071502584766827)
                ·
                  refine ⟨1300726372607253877150241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867150915071502584766827 1300726372607253877150241)
                  ·
                    refine ⟨975544779455440407862681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300726372607253877150241 975544779455440407862681)
                    ·
                      refine ⟨731658584591580305897011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975544779455440407862681 731658584591580305897011)
                      ·
                        rfl

theorem cell23_1424900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1424900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424900 prefixEnd_1424900 := by exact prefixLift 1424900
  have htrace : WordTrace (prefixWord ++ tailWord_1424900) baseStart_1424900 baseEnd_1424900 := by
    simpa [prefixWord, tailWord_1424900, baseEnd_1424900] using wordTrace_append hprefix tailTrace_1424900
  have hstable : (prefixWord ++ tailWord_1424900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424900).length < 2 ^ (prefixWord ++ tailWord_1424900).sum := by decide
  have hdescent : baseEnd_1424900 < baseStart_1424900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424925 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1424925 : Nat := 118140960795 + 1424925 * 2 ^ 59
def prefixEnd_1424925 : Nat := 4983230072969 + 3 ^ 40 * 1424925 * 2
def baseEnd_1424925 : Nat := 731671421607942708084395

theorem tailTrace_1424925 : CollatzResearch.WordTrace tailWord_1424925 prefixEnd_1424925 731671421607942708084395 := by
  unfold tailWord_1424925
  simp only [CollatzResearch.WordTrace]
  refine ⟨51971284362747557660404229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34647522908498371773602819 51971284362747557660404229)
  ·
    refine ⟨9744615818015167061325793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51971284362747557660404229 9744615818015167061325793)
    ·
      refine ⟨7308461863511375295994345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9744615818015167061325793 7308461863511375295994345)
      ·
        refine ⟨5481346397633531471995759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7308461863511375295994345 5481346397633531471995759)
        ·
          refine ⟨8222019596450297207993639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481346397633531471995759 8222019596450297207993639)
          ·
            refine ⟨12333029394675445811990459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8222019596450297207993639 12333029394675445811990459)
            ·
              refine ⟨18499544092013168717985689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12333029394675445811990459 18499544092013168717985689)
              ·
                refine ⟨13874658069009876538489267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18499544092013168717985689 13874658069009876538489267)
                ·
                  refine ⟨20811987103514814807733901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13874658069009876538489267 20811987103514814807733901)
                  ·
                    refine ⟨7804495163818055552900213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20811987103514814807733901 7804495163818055552900213)
                    ·
                      refine ⟨731671421607942708084395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7804495163818055552900213 731671421607942708084395)
                      ·
                        rfl

theorem cell23_1424925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1424925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424925 prefixEnd_1424925 := by exact prefixLift 1424925
  have htrace : WordTrace (prefixWord ++ tailWord_1424925) baseStart_1424925 baseEnd_1424925 := by
    simpa [prefixWord, tailWord_1424925, baseEnd_1424925] using wordTrace_append hprefix tailTrace_1424925
  have hstable : (prefixWord ++ tailWord_1424925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424925).length < 2 ^ (prefixWord ++ tailWord_1424925).sum := by decide
  have hdescent : baseEnd_1424925 < baseStart_1424925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424942 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1424942 : Nat := 118140960795 + 1424942 * 2 ^ 59
def prefixEnd_1424942 : Nat := 4983230072969 + 3 ^ 40 * 1424942 * 2
def baseEnd_1424942 : Nat := 731680150779069141571817

theorem tailTrace_1424942 : CollatzResearch.WordTrace tailWord_1424942 prefixEnd_1424942 731680150779069141571817 := by
  unfold tailWord_1424942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496488050460746195471635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34647936269123979709182053 6496488050460746195471635)
  ·
    refine ⟨9744732075691119293207453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6496488050460746195471635 9744732075691119293207453)
    ·
      refine ⟨3654274528384169734952795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9744732075691119293207453 3654274528384169734952795)
      ·
        refine ⟨5481411792576254602429193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654274528384169734952795 5481411792576254602429193)
        ·
          refine ⟨4111058844432190951821895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5481411792576254602429193 4111058844432190951821895)
          ·
            refine ⟨6166588266648286427732843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4111058844432190951821895 6166588266648286427732843)
            ·
              refine ⟨9249882399972429641599265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166588266648286427732843 9249882399972429641599265)
              ·
                refine ⟨6937411799979322231199449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9249882399972429641599265 6937411799979322231199449)
                ·
                  refine ⟨5203058849984491673399587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6937411799979322231199449 5203058849984491673399587)
                  ·
                    refine ⟨7804588274976737510099381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5203058849984491673399587 7804588274976737510099381)
                    ·
                      refine ⟨731680150779069141571817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7804588274976737510099381 731680150779069141571817)
                      ·
                        rfl

theorem cell23_1424942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1424942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1424942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1424942 prefixEnd_1424942 := by exact prefixLift 1424942
  have htrace : WordTrace (prefixWord ++ tailWord_1424942) baseStart_1424942 baseEnd_1424942 := by
    simpa [prefixWord, tailWord_1424942, baseEnd_1424942] using wordTrace_append hprefix tailTrace_1424942
  have hstable : (prefixWord ++ tailWord_1424942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424942).length < 2 ^ (prefixWord ++ tailWord_1424942).sum := by decide
  have hdescent : baseEnd_1424942 < baseStart_1424942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425035 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 8]
def baseStart_1425035 : Nat := 118140960795 + 1425035 * 2 ^ 59
def prefixEnd_1425035 : Nat := 4983230072969 + 3 ^ 40 * 1425035 * 2
def baseEnd_1425035 : Nat := 81303100497770808634321

theorem tailTrace_1425035 : CollatzResearch.WordTrace tailWord_1425035 prefixEnd_1425035 81303100497770808634321 := by
  unfold tailWord_1425035
  simp only [CollatzResearch.WordTrace]
  refine ⟨51975296392349046446908559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34650197594899364297939039 51975296392349046446908559)
  ·
    refine ⟨77962944588523569670362839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51975296392349046446908559 77962944588523569670362839)
    ·
      refine ⟨116944416882785354505544259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77962944588523569670362839 116944416882785354505544259)
      ·
        refine ⟨175416625324178031758316389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116944416882785354505544259 175416625324178031758316389)
        ·
          refine ⟨32890617248283380954684323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175416625324178031758316389 32890617248283380954684323)
          ·
            refine ⟨49335925872425071432026485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32890617248283380954684323 49335925872425071432026485)
            ·
              refine ⟨4625243050539850446752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49335925872425071432026485 4625243050539850446752483)
              ·
                refine ⟨6937864575809775670128725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625243050539850446752483 6937864575809775670128725)
                ·
                  refine ⟨81303100497770808634321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6937864575809775670128725 81303100497770808634321)
                  ·
                    rfl

theorem cell23_1425035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 8].length) (baseStart_1425035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425035 prefixEnd_1425035 := by exact prefixLift 1425035
  have htrace : WordTrace (prefixWord ++ tailWord_1425035) baseStart_1425035 baseEnd_1425035 := by
    simpa [prefixWord, tailWord_1425035, baseEnd_1425035] using wordTrace_append hprefix tailTrace_1425035
  have hstable : (prefixWord ++ tailWord_1425035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425035).length < 2 ^ (prefixWord ++ tailWord_1425035).sum := by decide
  have hdescent : baseEnd_1425035 < baseStart_1425035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425112 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_1425112 : Nat := 118140960795 + 1425112 * 2 ^ 59
def prefixEnd_1425112 : Nat := 4983230072969 + 3 ^ 40 * 1425112 * 2
def baseEnd_1425112 : Nat := 243922480830111158815345

theorem tailTrace_1425112 : CollatzResearch.WordTrace tailWord_1425112 prefixEnd_1425112 243922480830111158815345 := by
  unfold tailWord_1425112
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989052406535044298730795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34652069875380059064974393 25989052406535044298730795)
  ·
    refine ⟨38983578609802566448096193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25989052406535044298730795 38983578609802566448096193)
    ·
      refine ⟨29237683957351924836072145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38983578609802566448096193 29237683957351924836072145)
      ·
        refine ⟨21928262968013943627054109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29237683957351924836072145 21928262968013943627054109)
        ·
          refine ⟨8223098613005228860145291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21928262968013943627054109 8223098613005228860145291)
          ·
            refine ⟨12334647919507843290217937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223098613005228860145291 12334647919507843290217937)
            ·
              refine ⟨9250985939630882467663453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12334647919507843290217937 9250985939630882467663453)
              ·
                refine ⟨3469119727361580925373795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9250985939630882467663453 3469119727361580925373795)
                ·
                  refine ⟨5203679591042371388060693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469119727361580925373795 5203679591042371388060693)
                  ·
                    refine ⟨243922480830111158815345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5203679591042371388060693 243922480830111158815345)
                    ·
                      rfl

theorem cell23_1425112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_1425112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425112 prefixEnd_1425112 := by exact prefixLift 1425112
  have htrace : WordTrace (prefixWord ++ tailWord_1425112) baseStart_1425112 baseEnd_1425112 := by
    simpa [prefixWord, tailWord_1425112, baseEnd_1425112] using wordTrace_append hprefix tailTrace_1425112
  have hstable : (prefixWord ++ tailWord_1425112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425112).length < 2 ^ (prefixWord ++ tailWord_1425112).sum := by decide
  have hdescent : baseEnd_1425112 < baseStart_1425112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425116 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1425116 : Nat := 118140960795 + 1425116 * 2 ^ 59
def prefixEnd_1425116 : Nat := 4983230072969 + 3 ^ 40 * 1425116 * 2
def baseEnd_1425116 : Nat := 243923165470983820265339

theorem tailTrace_1425116 : CollatzResearch.WordTrace tailWord_1425116 prefixEnd_1425116 243923165470983820265339 := by
  unfold tailWord_1425116
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989125352527798640303601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34652167136703731520404801 25989125352527798640303601)
  ·
    refine ⟨19491844014395848980227701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25989125352527798640303601 19491844014395848980227701)
    ·
      refine ⟨1827360376349610841896347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19491844014395848980227701 1827360376349610841896347)
      ·
        refine ⟨2741040564524416262844521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827360376349610841896347 2741040564524416262844521)
        ·
          refine ⟨2055780423393312197133391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2741040564524416262844521 2055780423393312197133391)
          ·
            refine ⟨3083670635089968295700087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055780423393312197133391 3083670635089968295700087)
            ·
              refine ⟨4625505952634952443550131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083670635089968295700087 4625505952634952443550131)
              ·
                refine ⟨6938258928952428665325197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625505952634952443550131 6938258928952428665325197)
                ·
                  refine ⟨2601847098357160749496949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6938258928952428665325197 2601847098357160749496949)
                  ·
                    refine ⟨243923165470983820265339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2601847098357160749496949 243923165470983820265339)
                    ·
                      rfl

theorem cell23_1425116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1425116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425116 prefixEnd_1425116 := by exact prefixLift 1425116
  have htrace : WordTrace (prefixWord ++ tailWord_1425116) baseStart_1425116 baseEnd_1425116 := by
    simpa [prefixWord, tailWord_1425116, baseEnd_1425116] using wordTrace_append hprefix tailTrace_1425116
  have hstable : (prefixWord ++ tailWord_1425116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425116).length < 2 ^ (prefixWord ++ tailWord_1425116).sum := by decide
  have hdescent : baseEnd_1425116 < baseStart_1425116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425123 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1425123 : Nat := 118140960795 + 1425123 * 2 ^ 59
def prefixEnd_1425123 : Nat := 4983230072969 + 3 ^ 40 * 1425123 * 2
def baseEnd_1425123 : Nat := 731773090777532933408485

theorem tailTrace_1425123 : CollatzResearch.WordTrace tailWord_1425123 prefixEnd_1425123 731773090777532933408485 := by
  unfold tailWord_1425123
  simp only [CollatzResearch.WordTrace]
  refine ⟨51978506016030237476112023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34652337344020158317408015 51978506016030237476112023)
  ·
    refine ⟨77967759024045356214168035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51978506016030237476112023 77967759024045356214168035)
    ·
      refine ⟨116951638536068034321252053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77967759024045356214168035 116951638536068034321252053)
      ·
        refine ⟨2741054028189094554404345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 116951638536068034321252053 2741054028189094554404345)
        ·
          refine ⟨2055790521141820915803259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2741054028189094554404345 2055790521141820915803259)
          ·
            refine ⟨3083685781712731373704889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055790521141820915803259 3083685781712731373704889)
            ·
              refine ⟨2312764336284548530278667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083685781712731373704889 2312764336284548530278667)
              ·
                refine ⟨3469146504426822795418001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312764336284548530278667 3469146504426822795418001)
                ·
                  refine ⟨2601859878320117096563501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469146504426822795418001 2601859878320117096563501)
                  ·
                    refine ⟨975697454370043911211313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601859878320117096563501 975697454370043911211313)
                    ·
                      refine ⟨731773090777532933408485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975697454370043911211313 731773090777532933408485)
                      ·
                        rfl

theorem cell23_1425123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1425123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425123 prefixEnd_1425123 := by exact prefixLift 1425123
  have htrace : WordTrace (prefixWord ++ tailWord_1425123) baseStart_1425123 baseEnd_1425123 := by
    simpa [prefixWord, tailWord_1425123, baseEnd_1425123] using wordTrace_append hprefix tailTrace_1425123
  have hstable : (prefixWord ++ tailWord_1425123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425123).length < 2 ^ (prefixWord ++ tailWord_1425123).sum := by decide
  have hdescent : baseEnd_1425123 < baseStart_1425123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425132 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_1425132 : Nat := 118140960795 + 1425132 * 2 ^ 59
def prefixEnd_1425132 : Nat := 4983230072969 + 3 ^ 40 * 1425132 * 2
def baseEnd_1425132 : Nat := 731777712103423398195943

theorem tailTrace_1425132 : CollatzResearch.WordTrace tailWord_1425132 prefixEnd_1425132 731777712103423398195943 := by
  unfold tailWord_1425132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989417136498816006594825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34652556181998421342126433 25989417136498816006594825)
  ·
    refine ⟨19492062852374112004946119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25989417136498816006594825 19492062852374112004946119)
    ·
      refine ⟨29238094278561168007419179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19492062852374112004946119 29238094278561168007419179)
      ·
        refine ⟨43857141417841752011128769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29238094278561168007419179 43857141417841752011128769)
        ·
          refine ⟨32892856063381314008346577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43857141417841752011128769 32892856063381314008346577)
          ·
            refine ⟨24669642047535985506259933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32892856063381314008346577 24669642047535985506259933)
            ·
              refine ⟨9251115767825994564847475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24669642047535985506259933 9251115767825994564847475)
              ·
                refine ⟨13876673651738991847271213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9251115767825994564847475 13876673651738991847271213)
                ·
                  refine ⟨5203752619402121942726705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13876673651738991847271213 5203752619402121942726705)
                  ·
                    refine ⟨3902814464551591457045029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5203752619402121942726705 3902814464551591457045029)
                    ·
                      refine ⟨731777712103423398195943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3902814464551591457045029 731777712103423398195943)
                      ·
                        rfl

theorem cell23_1425132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_1425132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425132 prefixEnd_1425132 := by exact prefixLift 1425132
  have htrace : WordTrace (prefixWord ++ tailWord_1425132) baseStart_1425132 baseEnd_1425132 := by
    simpa [prefixWord, tailWord_1425132, baseEnd_1425132] using wordTrace_append hprefix tailTrace_1425132
  have hstable : (prefixWord ++ tailWord_1425132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425132).length < 2 ^ (prefixWord ++ tailWord_1425132).sum := by decide
  have hdescent : baseEnd_1425132 < baseStart_1425132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425139 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 3]
def baseStart_1425139 : Nat := 118140960795 + 1425139 * 2 ^ 59
def prefixEnd_1425139 : Nat := 4983230072969 + 3 ^ 40 * 1425139 * 2
def baseEnd_1425139 : Nat := 731781306468004870808411

theorem tailTrace_1425139 : CollatzResearch.WordTrace tailWord_1425139 prefixEnd_1425139 731781306468004870808411 := by
  unfold tailWord_1425139
  simp only [CollatzResearch.WordTrace]
  refine ⟨51979089583972272208694471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34652726389314848139129647 51979089583972272208694471)
  ·
    refine ⟨77968634375958408313041707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51979089583972272208694471 77968634375958408313041707)
    ·
      refine ⟨116952951563937612469562561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77968634375958408313041707 116952951563937612469562561)
      ·
        refine ⟨87714713672953209352171921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116952951563937612469562561 87714713672953209352171921)
        ·
          refine ⟨65786035254714907014128941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87714713672953209352171921 65786035254714907014128941)
          ·
            refine ⟨24669763220518090130298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65786035254714907014128941 24669763220518090130298353)
            ·
              refine ⟨18502322415388567597723765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24669763220518090130298353 18502322415388567597723765)
              ·
                refine ⟨1734592726442678212286603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18502322415388567597723765 1734592726442678212286603)
                ·
                  refine ⟨2601889089664017318429905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734592726442678212286603 2601889089664017318429905)
                  ·
                    refine ⟨1951416817248012988822429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2601889089664017318429905 1951416817248012988822429)
                    ·
                      refine ⟨731781306468004870808411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1951416817248012988822429 731781306468004870808411)
                      ·
                        rfl

theorem cell23_1425139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_1425139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425139 prefixEnd_1425139 := by exact prefixLift 1425139
  have htrace : WordTrace (prefixWord ++ tailWord_1425139) baseStart_1425139 baseEnd_1425139 := by
    simpa [prefixWord, tailWord_1425139, baseEnd_1425139] using wordTrace_append hprefix tailTrace_1425139
  have hstable : (prefixWord ++ tailWord_1425139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425139).length < 2 ^ (prefixWord ++ tailWord_1425139).sum := by decide
  have hdescent : baseEnd_1425139 < baseStart_1425139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425140 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1425140 : Nat := 118140960795 + 1425140 * 2 ^ 59
def prefixEnd_1425140 : Nat := 4983230072969 + 3 ^ 40 * 1425140 * 2
def baseEnd_1425140 : Nat := 731781819948659366895907

theorem tailTrace_1425140 : CollatzResearch.WordTrace tailWord_1425140 prefixEnd_1425140 731781819948659366895907 := by
  unfold tailWord_1425140
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989563028484324689740437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34652750704645766252987249 25989563028484324689740437)
  ·
    refine ⟨1218260766960202719831583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25989563028484324689740437 1218260766960202719831583)
    ·
      refine ⟨1827391150440304079747375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218260766960202719831583 1827391150440304079747375)
      ·
        refine ⟨2741086725660456119621063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827391150440304079747375 2741086725660456119621063)
        ·
          refine ⟨4111630088490684179431595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741086725660456119621063 4111630088490684179431595)
          ·
            refine ⟨6167445132736026269147393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4111630088490684179431595 6167445132736026269147393)
            ·
              refine ⟨4625583849552019701860545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6167445132736026269147393 4625583849552019701860545)
              ·
                refine ⟨3469187887164014776395409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4625583849552019701860545 3469187887164014776395409)
                ·
                  refine ⟨2601890915373011082296557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469187887164014776395409 2601890915373011082296557)
                  ·
                    refine ⟨975709093264879155861209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601890915373011082296557 975709093264879155861209)
                    ·
                      refine ⟨731781819948659366895907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975709093264879155861209 731781819948659366895907)
                      ·
                        rfl

theorem cell23_1425140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1425140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425140 prefixEnd_1425140 := by exact prefixLift 1425140
  have htrace : WordTrace (prefixWord ++ tailWord_1425140) baseStart_1425140 baseEnd_1425140 := by
    simpa [prefixWord, tailWord_1425140, baseEnd_1425140] using wordTrace_append hprefix tailTrace_1425140
  have hstable : (prefixWord ++ tailWord_1425140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425140).length < 2 ^ (prefixWord ++ tailWord_1425140).sum := by decide
  have hdescent : baseEnd_1425140 < baseStart_1425140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425142 : List Nat := [5, 1, 1, 1, 1, 14]
def baseStart_1425142 : Nat := 118140960795 + 1425142 * 2 ^ 59
def prefixEnd_1425142 : Nat := 4983230072969 + 3 ^ 40 * 1425142 * 2
def baseEnd_1425142 : Nat := 3011452044896989131979

theorem tailTrace_1425142 : CollatzResearch.WordTrace tailWord_1425142 prefixEnd_1425142 3011452044896989131979 := by
  unfold tailWord_1425142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248699937685087732565855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34652799335307602480702453 3248699937685087732565855)
  ·
    refine ⟨4873049906527631598848783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3248699937685087732565855 4873049906527631598848783)
    ·
      refine ⟨7309574859791447398273175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4873049906527631598848783 7309574859791447398273175)
      ·
        refine ⟨10964362289687171097409763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7309574859791447398273175 10964362289687171097409763)
        ·
          refine ⟨16446543434530756646114645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10964362289687171097409763 16446543434530756646114645)
          ·
            refine ⟨3011452044896989131979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 16446543434530756646114645 3011452044896989131979)
            ·
              rfl

theorem cell23_1425142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 14].length) (baseStart_1425142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425142 prefixEnd_1425142 := by exact prefixLift 1425142
  have htrace : WordTrace (prefixWord ++ tailWord_1425142) baseStart_1425142 baseEnd_1425142 := by
    simpa [prefixWord, tailWord_1425142, baseEnd_1425142] using wordTrace_append hprefix tailTrace_1425142
  have hstable : (prefixWord ++ tailWord_1425142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425142).length < 2 ^ (prefixWord ++ tailWord_1425142).sum := by decide
  have hdescent : baseEnd_1425142 < baseStart_1425142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425169 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_1425169 : Nat := 118140960795 + 1425169 * 2 ^ 59
def prefixEnd_1425169 : Nat := 4983230072969 + 3 ^ 40 * 1425169 * 2
def baseEnd_1425169 : Nat := 731796710887639753433273

theorem tailTrace_1425169 : CollatzResearch.WordTrace tailWord_1425169 prefixEnd_1425169 731796710887639753433273 := by
  unfold tailWord_1425169
  simp only [CollatzResearch.WordTrace]
  refine ⟨51980183773863587332286561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34653455849242391554857707 51980183773863587332286561)
  ·
    refine ⟨38985137830397690499214921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51980183773863587332286561 38985137830397690499214921)
    ·
      refine ⟨29238853372798267874411191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38985137830397690499214921 29238853372798267874411191)
      ·
        refine ⟨43858280059197401811616787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29238853372798267874411191 43858280059197401811616787)
        ·
          refine ⟨65787420088796102717425181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43858280059197401811616787 65787420088796102717425181)
          ·
            refine ⟨24670282533298538519034443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65787420088796102717425181 24670282533298538519034443)
            ·
              refine ⟨37005423799947807778551665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24670282533298538519034443 37005423799947807778551665)
              ·
                refine ⟨27754067849960855833913749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37005423799947807778551665 27754067849960855833913749)
                ·
                  refine ⟨1300971930466915117214707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27754067849960855833913749 1300971930466915117214707)
                  ·
                    refine ⟨1951457895700372675822061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300971930466915117214707 1951457895700372675822061)
                    ·
                      refine ⟨731796710887639753433273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1951457895700372675822061 731796710887639753433273)
                      ·
                        rfl

theorem cell23_1425169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_1425169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425169 prefixEnd_1425169 := by exact prefixLift 1425169
  have htrace : WordTrace (prefixWord ++ tailWord_1425169) baseStart_1425169 baseEnd_1425169 := by
    simpa [prefixWord, tailWord_1425169, baseEnd_1425169] using wordTrace_append hprefix tailTrace_1425169
  have hstable : (prefixWord ++ tailWord_1425169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425169).length < 2 ^ (prefixWord ++ tailWord_1425169).sum := by decide
  have hdescent : baseEnd_1425169 < baseStart_1425169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425170 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1425170 : Nat := 118140960795 + 1425170 * 2 ^ 59
def prefixEnd_1425170 : Nat := 4983230072969 + 3 ^ 40 * 1425170 * 2
def baseEnd_1425170 : Nat := 731797224368294249520769

theorem tailTrace_1425170 : CollatzResearch.WordTrace tailWord_1425170 prefixEnd_1425170 731797224368294249520769 := by
  unfold tailWord_1425170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995055061714991125768241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34653480164573309668715309 12995055061714991125768241)
  ·
    refine ⟨9746291296286243344326181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12995055061714991125768241 9746291296286243344326181)
    ·
      refine ⟨1827429618053670627061159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9746291296286243344326181 1827429618053670627061159)
      ·
        refine ⟨2741144427080505940591739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827429618053670627061159 2741144427080505940591739)
        ·
          refine ⟨4111716640620758910887609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741144427080505940591739 4111716640620758910887609)
          ·
            refine ⟨3083787480465569183165707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111716640620758910887609 3083787480465569183165707)
            ·
              refine ⟨4625681220698353774748561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083787480465569183165707 4625681220698353774748561)
              ·
                refine ⟨3469260915523765331061421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4625681220698353774748561 3469260915523765331061421)
                ·
                  refine ⟨1300972843321411999148033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3469260915523765331061421 1300972843321411999148033)
                  ·
                    refine ⟨975729632491058999361025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300972843321411999148033 975729632491058999361025)
                    ·
                      refine ⟨731797224368294249520769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975729632491058999361025 731797224368294249520769)
                      ·
                        rfl

theorem cell23_1425170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1425170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425170 prefixEnd_1425170 := by exact prefixLift 1425170
  have htrace : WordTrace (prefixWord ++ tailWord_1425170) baseStart_1425170 baseEnd_1425170 := by
    simpa [prefixWord, tailWord_1425170, baseEnd_1425170] using wordTrace_append hprefix tailTrace_1425170
  have hstable : (prefixWord ++ tailWord_1425170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425170).length < 2 ^ (prefixWord ++ tailWord_1425170).sum := by decide
  have hdescent : baseEnd_1425170 < baseStart_1425170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425186 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1425186 : Nat := 118140960795 + 1425186 * 2 ^ 59
def prefixEnd_1425186 : Nat := 4983230072969 + 3 ^ 40 * 1425186 * 2
def baseEnd_1425186 : Nat := 731805440058766186920695

theorem tailTrace_1425186 : CollatzResearch.WordTrace tailWord_1425186 prefixEnd_1425186 731805440058766186920695 := by
  unfold tailWord_1425186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995200953700499808913853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34653869209867999490436941 12995200953700499808913853)
  ·
    refine ⟨4873200357637687428342695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12995200953700499808913853 4873200357637687428342695)
    ·
      refine ⟨7309800536456531142514043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4873200357637687428342695 7309800536456531142514043)
      ·
        refine ⟨10964700804684796713771065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7309800536456531142514043 10964700804684796713771065)
        ·
          refine ⟨8223525603513597535328299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10964700804684796713771065 8223525603513597535328299)
          ·
            refine ⟨12335288405270396302992449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223525603513597535328299 12335288405270396302992449)
            ·
              refine ⟨9251466303952797227244337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12335288405270396302992449 9251466303952797227244337)
              ·
                refine ⟨6938599727964597920433253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9251466303952797227244337 6938599727964597920433253)
                ·
                  refine ⟨1300987448993362110081235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6938599727964597920433253 1300987448993362110081235)
                  ·
                    refine ⟨1951481173490043165121853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300987448993362110081235 1951481173490043165121853)
                    ·
                      refine ⟨731805440058766186920695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1951481173490043165121853 731805440058766186920695)
                      ·
                        rfl

theorem cell23_1425186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1425186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425186 prefixEnd_1425186 := by exact prefixLift 1425186
  have htrace : WordTrace (prefixWord ++ tailWord_1425186) baseStart_1425186 baseEnd_1425186 := by
    simpa [prefixWord, tailWord_1425186, baseEnd_1425186] using wordTrace_append hprefix tailTrace_1425186
  have hstable : (prefixWord ++ tailWord_1425186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425186).length < 2 ^ (prefixWord ++ tailWord_1425186).sum := by decide
  have hdescent : baseEnd_1425186 < baseStart_1425186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425316 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_1425316 : Nat := 118140960795 + 1425316 * 2 ^ 59
def prefixEnd_1425316 : Nat := 4983230072969 + 3 ^ 40 * 1425316 * 2
def baseEnd_1425316 : Nat := 731872192543850678295097

theorem tailTrace_1425316 : CollatzResearch.WordTrace tailWord_1425316 prefixEnd_1425316 731872192543850678295097 := by
  unfold tailWord_1425316
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992772652165515718943901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34657030202887354291925201 25992772652165515718943901)
  ·
    refine ⟨9747289744562068394603963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25992772652165515718943901 9747289744562068394603963)
    ·
      refine ⟨14620934616843102591905945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9747289744562068394603963 14620934616843102591905945)
      ·
        refine ⟨10965700962632326943929459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14620934616843102591905945 10965700962632326943929459)
        ·
          refine ⟨16448551443948490415894189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10965700962632326943929459 16448551443948490415894189)
          ·
            refine ⟨6168206791480683905960321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16448551443948490415894189 6168206791480683905960321)
            ·
              refine ⟨4626155093610512929470241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6168206791480683905960321 4626155093610512929470241)
              ·
                refine ⟨3469616320207884697102681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626155093610512929470241 3469616320207884697102681)
                ·
                  refine ⟨2602212240155913522827011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469616320207884697102681 2602212240155913522827011)
                  ·
                    refine ⟨3903318360233870284240517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2602212240155913522827011 3903318360233870284240517)
                    ·
                      refine ⟨731872192543850678295097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3903318360233870284240517 731872192543850678295097)
                      ·
                        rfl

theorem cell23_1425316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_1425316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425316 prefixEnd_1425316 := by exact prefixLift 1425316
  have htrace : WordTrace (prefixWord ++ tailWord_1425316) baseStart_1425316 baseEnd_1425316 := by
    simpa [prefixWord, tailWord_1425316, baseEnd_1425316] using wordTrace_append hprefix tailTrace_1425316
  have hstable : (prefixWord ++ tailWord_1425316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425316).length < 2 ^ (prefixWord ++ tailWord_1425316).sum := by decide
  have hdescent : baseEnd_1425316 < baseStart_1425316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425333 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_1425333 : Nat := 118140960795 + 1425333 * 2 ^ 59
def prefixEnd_1425333 : Nat := 4983230072969 + 3 ^ 40 * 1425333 * 2
def baseEnd_1425333 : Nat := 731880921714977111782519

theorem tailTrace_1425333 : CollatzResearch.WordTrace tailWord_1425333 prefixEnd_1425333 731880921714977111782519 := by
  unfold tailWord_1425333
  simp only [CollatzResearch.WordTrace]
  refine ⟨51986165345269443341256653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34657443563512962227504435 51986165345269443341256653)
  ·
    refine ⟨19494812004476041252971245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51986165345269443341256653 19494812004476041252971245)
    ·
      refine ⟨7310554501678515469864217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19494812004476041252971245 7310554501678515469864217)
      ·
        refine ⟨5482915876258886602398163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7310554501678515469864217 5482915876258886602398163)
        ·
          refine ⟨8224373814388329903597245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482915876258886602398163 8224373814388329903597245)
          ·
            refine ⟨3084140180395623713848967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8224373814388329903597245 3084140180395623713848967)
            ·
              refine ⟨4626210270593435570773451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084140180395623713848967 4626210270593435570773451)
              ·
                refine ⟨6939315405890153356160177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626210270593435570773451 6939315405890153356160177)
                ·
                  refine ⟨5204486554417615017120133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6939315405890153356160177 5204486554417615017120133)
                  ·
                    refine ⟨975841228953302815710025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204486554417615017120133 975841228953302815710025)
                    ·
                      refine ⟨731880921714977111782519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 975841228953302815710025 731880921714977111782519)
                      ·
                        rfl

theorem cell23_1425333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_1425333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1425333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1425333 prefixEnd_1425333 := by exact prefixLift 1425333
  have htrace : WordTrace (prefixWord ++ tailWord_1425333) baseStart_1425333 baseEnd_1425333 := by
    simpa [prefixWord, tailWord_1425333, baseEnd_1425333] using wordTrace_append hprefix tailTrace_1425333
  have hstable : (prefixWord ++ tailWord_1425333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425333).length < 2 ^ (prefixWord ++ tailWord_1425333).sum := by decide
  have hdescent : baseEnd_1425333 < baseStart_1425333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
