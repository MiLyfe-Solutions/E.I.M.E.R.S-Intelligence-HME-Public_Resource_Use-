import V185TrunkScan23Chunk1191

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7062327 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_7062327 : Nat := 118140960795 + 7062327 * 2 ^ 59
def prefixEnd_7062327 : Nat := 4983230072969 + 3 ^ 40 * 7062327 * 2
def baseEnd_7062327 : Nat := 3626368290225495346833455

theorem tailTrace_7062327 : CollatzResearch.WordTrace tailWord_7062327 prefixEnd_7062327 3626368290225495346833455 := by
  unfold tailWord_7062327
  simp only [CollatzResearch.WordTrace]
  refine ⟨257584227085402903270249235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171722818056935268846832823 257584227085402903270249235)
  ·
    refine ⟨386376340628104354905373853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257584227085402903270249235 386376340628104354905373853)
    ·
      refine ⟨144891127735539133089515195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386376340628104354905373853 144891127735539133089515195)
      ·
        refine ⟨217336691603308699634272793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144891127735539133089515195 217336691603308699634272793)
        ·
          refine ⟨163002518702481524725704595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217336691603308699634272793 163002518702481524725704595)
          ·
            refine ⟨244503778053722287088556893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163002518702481524725704595 244503778053722287088556893)
            ·
              refine ⟨91688916770145857658208835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244503778053722287088556893 91688916770145857658208835)
              ·
                refine ⟨137533375155218786487313253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91688916770145857658208835 137533375155218786487313253)
                ·
                  refine ⟨25787507841603522466371235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137533375155218786487313253 25787507841603522466371235)
                  ·
                    refine ⟨38681261762405283699556853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25787507841603522466371235 38681261762405283699556853)
                    ·
                      refine ⟨3626368290225495346833455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38681261762405283699556853 3626368290225495346833455)
                      ·
                        rfl

theorem cell23_7062327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_7062327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062327 prefixEnd_7062327 := by exact prefixLift 7062327
  have htrace : WordTrace (prefixWord ++ tailWord_7062327) baseStart_7062327 baseEnd_7062327 := by
    simpa [prefixWord, tailWord_7062327, baseEnd_7062327] using wordTrace_append hprefix tailTrace_7062327
  have hstable : (prefixWord ++ tailWord_7062327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062327).length < 2 ^ (prefixWord ++ tailWord_7062327).sum := by decide
  have hdescent : baseEnd_7062327 < baseStart_7062327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062341 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 4, 2, 2]
def baseStart_7062341 : Nat := 118140960795 + 7062341 * 2 ^ 59
def prefixEnd_7062341 : Nat := 4983230072969 + 3 ^ 40 * 7062341 * 2
def baseEnd_7062341 : Nat := 3626375478954658292058391

theorem tailTrace_7062341 : CollatzResearch.WordTrace tailWord_7062341 prefixEnd_7062341 3626375478954658292058391 := by
  unfold tailWord_7062341
  simp only [CollatzResearch.WordTrace]
  refine ⟨257584737707352183661258877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171723158471568122440839251 257584737707352183661258877)
  ·
    refine ⟨96594276640257068872972079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257584737707352183661258877 96594276640257068872972079)
    ·
      refine ⟨144891414960385603309458119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96594276640257068872972079 144891414960385603309458119)
      ·
        refine ⟨217337122440578404964187179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144891414960385603309458119 217337122440578404964187179)
        ·
          refine ⟨326005683660867607446280769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217337122440578404964187179 326005683660867607446280769)
          ·
            refine ⟨244504262745650705584710577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326005683660867607446280769 244504262745650705584710577)
            ·
              refine ⟨183378197059238029188532933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244504262745650705584710577 183378197059238029188532933)
              ·
                refine ⟨34383411948607130472849925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183378197059238029188532933 34383411948607130472849925)
                ·
                  refine ⟨6446889740363836963659361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34383411948607130472849925 6446889740363836963659361)
                  ·
                    refine ⟨4835167305272877722744521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6446889740363836963659361 4835167305272877722744521)
                    ·
                      refine ⟨3626375478954658292058391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835167305272877722744521 3626375478954658292058391)
                      ·
                        rfl

theorem cell23_7062341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_7062341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062341 prefixEnd_7062341 := by exact prefixLift 7062341
  have htrace : WordTrace (prefixWord ++ tailWord_7062341) baseStart_7062341 baseEnd_7062341 := by
    simpa [prefixWord, tailWord_7062341, baseEnd_7062341] using wordTrace_append hprefix tailTrace_7062341
  have hstable : (prefixWord ++ tailWord_7062341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062341).length < 2 ^ (prefixWord ++ tailWord_7062341).sum := by decide
  have hdescent : baseEnd_7062341 < baseStart_7062341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062354 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7062354 : Nat := 118140960795 + 7062354 * 2 ^ 59
def prefixEnd_7062354 : Nat := 4983230072969 + 3 ^ 40 * 7062354 * 2
def baseEnd_7062354 : Nat := 3626382154203166741195831

theorem tailTrace_7062354 : CollatzResearch.WordTrace tailWord_7062354 prefixEnd_7062354 3626382154203166741195831 := by
  unfold tailWord_7062354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64396302964076271720370529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171723474570870057920988077 64396302964076271720370529)
  ·
    refine ⟨48297227223057203790277897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64396302964076271720370529 48297227223057203790277897)
    ·
      refine ⟨36222920417292902842708423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48297227223057203790277897 36222920417292902842708423)
      ·
        refine ⟨54334380625939354264062635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36222920417292902842708423 54334380625939354264062635)
        ·
          refine ⟨81501570938909031396093953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54334380625939354264062635 81501570938909031396093953)
          ·
            refine ⟨61126178204181773547070465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81501570938909031396093953 61126178204181773547070465)
            ·
              refine ⟨45844633653136330160302849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61126178204181773547070465 45844633653136330160302849)
              ·
                refine ⟨34383475239852247620227137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45844633653136330160302849 34383475239852247620227137)
                ·
                  refine ⟨25787606429889185715170353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34383475239852247620227137 25787606429889185715170353)
                  ·
                    refine ⟨19340704822416889286377765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25787606429889185715170353 19340704822416889286377765)
                    ·
                      refine ⟨3626382154203166741195831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19340704822416889286377765 3626382154203166741195831)
                      ·
                        rfl

theorem cell23_7062354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7062354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062354 prefixEnd_7062354 := by exact prefixLift 7062354
  have htrace : WordTrace (prefixWord ++ tailWord_7062354) baseStart_7062354 baseEnd_7062354 := by
    simpa [prefixWord, tailWord_7062354, baseEnd_7062354] using wordTrace_append hprefix tailTrace_7062354
  have hstable : (prefixWord ++ tailWord_7062354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062354).length < 2 ^ (prefixWord ++ tailWord_7062354).sum := by decide
  have hdescent : baseEnd_7062354 < baseStart_7062354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062387 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_7062387 : Nat := 118140960795 + 7062387 * 2 ^ 59
def prefixEnd_7062387 : Nat := 4983230072969 + 3 ^ 40 * 7062387 * 2
def baseEnd_7062387 : Nat := 3626399099064765112083179

theorem tailTrace_7062387 : CollatzResearch.WordTrace tailWord_7062387 prefixEnd_7062387 3626399099064765112083179 := by
  unfold tailWord_7062387
  simp only [CollatzResearch.WordTrace]
  refine ⟨257586415465185533517433415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171724276976790355678288943 257586415465185533517433415)
  ·
    refine ⟨386379623197778300276150123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257586415465185533517433415 386379623197778300276150123)
    ·
      refine ⟨579569434796667450414225185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386379623197778300276150123 579569434796667450414225185)
      ·
        refine ⟨434677076097500587810668889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579569434796667450414225185 434677076097500587810668889)
        ·
          refine ⟨326007807073125440858001667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434677076097500587810668889 326007807073125440858001667)
          ·
            refine ⟨489011710609688161287002501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326007807073125440858001667 489011710609688161287002501)
            ·
              refine ⟨91689695739316530241312969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489011710609688161287002501 91689695739316530241312969)
              ·
                refine ⟨68767271804487397680984727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91689695739316530241312969 68767271804487397680984727)
                ·
                  refine ⟨103150907706731096521477091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68767271804487397680984727 103150907706731096521477091)
                  ·
                    refine ⟨154726361560096644782215637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103150907706731096521477091 154726361560096644782215637)
                    ·
                      refine ⟨3626399099064765112083179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154726361560096644782215637 3626399099064765112083179)
                      ·
                        rfl

theorem cell23_7062387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_7062387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062387 prefixEnd_7062387 := by exact prefixLift 7062387
  have htrace : WordTrace (prefixWord ++ tailWord_7062387) baseStart_7062387 baseEnd_7062387 := by
    simpa [prefixWord, tailWord_7062387, baseEnd_7062387] using wordTrace_append hprefix tailTrace_7062387
  have hstable : (prefixWord ++ tailWord_7062387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062387).length < 2 ^ (prefixWord ++ tailWord_7062387).sum := by decide
  have hdescent : baseEnd_7062387 < baseStart_7062387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062475 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 1, 4]
def baseStart_7062475 : Nat := 118140960795 + 7062475 * 2 ^ 59
def prefixEnd_7062475 : Nat := 4983230072969 + 3 ^ 40 * 7062475 * 2
def baseEnd_7062475 : Nat := 1208814761787453589260925

theorem tailTrace_7062475 : CollatzResearch.WordTrace tailWord_7062475 prefixEnd_7062475 1208814761787453589260925 := by
  unfold tailWord_7062475
  simp only [CollatzResearch.WordTrace]
  refine ⟨257589625088866724546636879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171726416725911149697757919 257589625088866724546636879)
  ·
    refine ⟨386384437633300086819955319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257589625088866724546636879 386384437633300086819955319)
    ·
      refine ⟨579576656449950130229932979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386384437633300086819955319 579576656449950130229932979)
      ·
        refine ⟨869364984674925195344899469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579576656449950130229932979 869364984674925195344899469)
        ·
          refine ⟨326011869253096948254337301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 869364984674925195344899469 326011869253096948254337301)
          ·
            refine ⟨15281806371238919449422061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326011869253096948254337301 15281806371238919449422061)
            ·
              refine ⟨5730677389214594793533273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15281806371238919449422061 5730677389214594793533273)
              ·
                refine ⟨4298008041910946095149955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5730677389214594793533273 4298008041910946095149955)
                ·
                  refine ⟨6447012062866419142724933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298008041910946095149955 6447012062866419142724933)
                  ·
                    refine ⟨1208814761787453589260925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447012062866419142724933 1208814761787453589260925)
                    ·
                      rfl

theorem cell23_7062475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 4].length) (baseStart_7062475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062475 prefixEnd_7062475 := by exact prefixLift 7062475
  have htrace : WordTrace (prefixWord ++ tailWord_7062475) baseStart_7062475 baseEnd_7062475 := by
    simpa [prefixWord, tailWord_7062475, baseEnd_7062475] using wordTrace_append hprefix tailTrace_7062475
  have hstable : (prefixWord ++ tailWord_7062475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062475).length < 2 ^ (prefixWord ++ tailWord_7062475).sum := by decide
  have hdescent : baseEnd_7062475 < baseStart_7062475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062488 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 6]
def baseStart_7062488 : Nat := 118140960795 + 7062488 * 2 ^ 59
def prefixEnd_7062488 : Nat := 4983230072969 + 3 ^ 40 * 7062488 * 2
def baseEnd_7062488 : Nat := 402938995623429912991135

theorem tailTrace_7062488 : CollatzResearch.WordTrace tailWord_7062488 prefixEnd_7062488 402938995623429912991135 := by
  unfold tailWord_7062488
  simp only [CollatzResearch.WordTrace]
  refine ⟨128795049618909813883430059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171726732825213085177906745 128795049618909813883430059)
  ·
    refine ⟨193192574428364720825145089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128795049618909813883430059 193192574428364720825145089)
    ·
      refine ⟨144894430821273540618858817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193192574428364720825145089 144894430821273540618858817)
      ·
        refine ⟨108670823115955155464144113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144894430821273540618858817 108670823115955155464144113)
        ·
          refine ⟨81503117336966366598108085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108670823115955155464144113 81503117336966366598108085)
          ·
            refine ⟨7640917250340596868572633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81503117336966366598108085 7640917250340596868572633)
            ·
              refine ⟨5730687937755447651429475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7640917250340596868572633 5730687937755447651429475)
              ·
                refine ⟨8596031906633171477144213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730687937755447651429475 8596031906633171477144213)
                ·
                  refine ⟨402938995623429912991135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8596031906633171477144213 402938995623429912991135)
                  ·
                    rfl

theorem cell23_7062488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 6].length) (baseStart_7062488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062488 prefixEnd_7062488 := by exact prefixLift 7062488
  have htrace : WordTrace (prefixWord ++ tailWord_7062488) baseStart_7062488 baseEnd_7062488 := by
    simpa [prefixWord, tailWord_7062488, baseEnd_7062488] using wordTrace_append hprefix tailTrace_7062488
  have hstable : (prefixWord ++ tailWord_7062488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062488).length < 2 ^ (prefixWord ++ tailWord_7062488).sum := by decide
  have hdescent : baseEnd_7062488 < baseStart_7062488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062526 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_7062526 : Nat := 118140960795 + 7062526 * 2 ^ 59
def prefixEnd_7062526 : Nat := 4983230072969 + 3 ^ 40 * 7062526 * 2
def baseEnd_7062526 : Nat := 1208823490958580022748347

theorem tailTrace_7062526 : CollatzResearch.WordTrace tailWord_7062526 prefixEnd_7062526 1208823490958580022748347 := by
  unfold tailWord_7062526
  simp only [CollatzResearch.WordTrace]
  refine ⟨32198935651460245032092929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171727656807787973504495621 32198935651460245032092929)
  ·
    refine ⟨24149201738595183774069697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32198935651460245032092929 24149201738595183774069697)
    ·
      refine ⟨18111901303946387830552273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24149201738595183774069697 18111901303946387830552273)
      ·
        refine ⟨13583925977959790872914205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18111901303946387830552273 13583925977959790872914205)
        ·
          refine ⟨5093972241734921577342827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13583925977959790872914205 5093972241734921577342827)
          ·
            refine ⟨7640958362602382366014241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093972241734921577342827 7640958362602382366014241)
            ·
              refine ⟨5730718771951786774510681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7640958362602382366014241 5730718771951786774510681)
              ·
                refine ⟨4298039078963840080883011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5730718771951786774510681 4298039078963840080883011)
                ·
                  refine ⟨6447058618445760121324517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298039078963840080883011 6447058618445760121324517)
                  ·
                    refine ⟨1208823490958580022748347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447058618445760121324517 1208823490958580022748347)
                    ·
                      rfl

theorem cell23_7062526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_7062526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062526 prefixEnd_7062526 := by exact prefixLift 7062526
  have htrace : WordTrace (prefixWord ++ tailWord_7062526) baseStart_7062526 baseEnd_7062526 := by
    simpa [prefixWord, tailWord_7062526, baseEnd_7062526] using wordTrace_append hprefix tailTrace_7062526
  have hstable : (prefixWord ++ tailWord_7062526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062526).length < 2 ^ (prefixWord ++ tailWord_7062526).sum := by decide
  have hdescent : baseEnd_7062526 < baseStart_7062526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062571 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 3]
def baseStart_7062571 : Nat := 118140960795 + 7062571 * 2 ^ 59
def prefixEnd_7062571 : Nat := 4983230072969 + 3 ^ 40 * 7062571 * 2
def baseEnd_7062571 : Nat := 3626493579505192392182333

theorem tailTrace_7062571 : CollatzResearch.WordTrace tailWord_7062571 prefixEnd_7062571 3626493579505192392182333 := by
  unfold tailWord_7062571
  simp only [CollatzResearch.WordTrace]
  refine ⟨257593126496518932942131567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171728750997679288628087711 257593126496518932942131567)
  ·
    refine ⟨386389689744778399413197351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257593126496518932942131567 386389689744778399413197351)
    ·
      refine ⟨579584534617167599119796027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386389689744778399413197351 579584534617167599119796027)
      ·
        refine ⟨869376801925751398679694041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579584534617167599119796027 869376801925751398679694041)
        ·
          refine ⟨652032601444313549009770531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869376801925751398679694041 652032601444313549009770531)
          ·
            refine ⟨978048902166470323514655797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652032601444313549009770531 978048902166470323514655797)
            ·
              refine ⟨91692084578106592829498981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 978048902166470323514655797 91692084578106592829498981)
              ·
                refine ⟨17192265858394986155531059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91692084578106592829498981 17192265858394986155531059)
                ·
                  refine ⟨25788398787592479233296589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17192265858394986155531059 25788398787592479233296589)
                  ·
                    refine ⟨9670649545347179712486221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25788398787592479233296589 9670649545347179712486221)
                    ·
                      refine ⟨3626493579505192392182333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9670649545347179712486221 3626493579505192392182333)
                      ·
                        rfl

theorem cell23_7062571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 3].length) (baseStart_7062571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062571 prefixEnd_7062571 := by exact prefixLift 7062571
  have htrace : WordTrace (prefixWord ++ tailWord_7062571) baseStart_7062571 baseEnd_7062571 := by
    simpa [prefixWord, tailWord_7062571, baseEnd_7062571] using wordTrace_append hprefix tailTrace_7062571
  have hstable : (prefixWord ++ tailWord_7062571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062571).length < 2 ^ (prefixWord ++ tailWord_7062571).sum := by decide
  have hdescent : baseEnd_7062571 < baseStart_7062571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062572 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 1, 2, 2]
def baseStart_7062572 : Nat := 118140960795 + 7062572 * 2 ^ 59
def prefixEnd_7062572 : Nat := 4983230072969 + 3 ^ 40 * 7062572 * 2
def baseEnd_7062572 : Nat := 3626494092985846888269829

theorem tailTrace_7062572 : CollatzResearch.WordTrace tailWord_7062572 prefixEnd_7062572 3626494092985846888269829 := by
  unfold tailWord_7062572
  simp only [CollatzResearch.WordTrace]
  refine ⟨128796581484757655056458985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171728775313010206741945313 128796581484757655056458985)
  ·
    refine ⟨96597436113568241292344239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128796581484757655056458985 96597436113568241292344239)
    ·
      refine ⟨144896154170352361938516359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96597436113568241292344239 144896154170352361938516359)
      ·
        refine ⟨217344231255528542907774539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144896154170352361938516359 217344231255528542907774539)
        ·
          refine ⟨326016346883292814361661809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217344231255528542907774539 326016346883292814361661809)
          ·
            refine ⟨244512260162469610771246357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326016346883292814361661809 244512260162469610771246357)
            ·
              refine ⟨11461512195115763004902173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244512260162469610771246357 11461512195115763004902173)
              ·
                refine ⟨4298067073168411126838315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11461512195115763004902173 4298067073168411126838315)
                ·
                  refine ⟨6447100609752616690257473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298067073168411126838315 6447100609752616690257473)
                  ·
                    refine ⟨4835325457314462517693105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6447100609752616690257473 4835325457314462517693105)
                    ·
                      refine ⟨3626494092985846888269829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835325457314462517693105 3626494092985846888269829)
                      ·
                        rfl

theorem cell23_7062572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_7062572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062572 prefixEnd_7062572 := by exact prefixLift 7062572
  have htrace : WordTrace (prefixWord ++ tailWord_7062572) baseStart_7062572 baseEnd_7062572 := by
    simpa [prefixWord, tailWord_7062572, baseEnd_7062572] using wordTrace_append hprefix tailTrace_7062572
  have hstable : (prefixWord ++ tailWord_7062572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062572).length < 2 ^ (prefixWord ++ tailWord_7062572).sum := by decide
  have hdescent : baseEnd_7062572 < baseStart_7062572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062582 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7062582 : Nat := 118140960795 + 7062582 * 2 ^ 59
def prefixEnd_7062582 : Nat := 4983230072969 + 3 ^ 40 * 7062582 * 2
def baseEnd_7062582 : Nat := 1208833075930797283048261

theorem tailTrace_7062582 : CollatzResearch.WordTrace tailWord_7062582 prefixEnd_7062582 1208833075930797283048261 := by
  unfold tailWord_7062582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16099595481217442613798875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171729018466319387880521333 16099595481217442613798875)
  ·
    refine ⟨24149393221826163920698313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16099595481217442613798875 24149393221826163920698313)
    ·
      refine ⟨18112044916369622940523735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24149393221826163920698313 18112044916369622940523735)
      ·
        refine ⟨27168067374554434410785603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18112044916369622940523735 27168067374554434410785603)
        ·
          refine ⟨40752101061831651616178405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27168067374554434410785603 40752101061831651616178405)
          ·
            refine ⟨7641018949093434678033451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40752101061831651616178405 7641018949093434678033451)
            ·
              refine ⟨11461528423640152017050177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641018949093434678033451 11461528423640152017050177)
              ·
                refine ⟨8596146317730114012787633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11461528423640152017050177 8596146317730114012787633)
                ·
                  refine ⟨6447109738297585509590725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8596146317730114012787633 6447109738297585509590725)
                  ·
                    refine ⟨1208833075930797283048261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447109738297585509590725 1208833075930797283048261)
                    ·
                      rfl

theorem cell23_7062582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7062582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062582 prefixEnd_7062582 := by exact prefixLift 7062582
  have htrace : WordTrace (prefixWord ++ tailWord_7062582) baseStart_7062582 baseEnd_7062582 := by
    simpa [prefixWord, tailWord_7062582, baseEnd_7062582] using wordTrace_append hprefix tailTrace_7062582
  have hstable : (prefixWord ++ tailWord_7062582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062582).length < 2 ^ (prefixWord ++ tailWord_7062582).sum := by decide
  have hdescent : baseEnd_7062582 < baseStart_7062582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062605 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7062605 : Nat := 118140960795 + 7062605 * 2 ^ 59
def prefixEnd_7062605 : Nat := 4983230072969 + 3 ^ 40 * 7062605 * 2
def baseEnd_7062605 : Nat := 3626511037847445259157177

theorem tailTrace_7062605 : CollatzResearch.WordTrace tailWord_7062605 prefixEnd_7062605 3626511037847445259157177 := by
  unfold tailWord_7062605
  simp only [CollatzResearch.WordTrace]
  refine ⟨257594366578395756748869269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171729577718930504499246179 257594366578395756748869269)
  ·
    refine ⟨12074735933362301097603247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 257594366578395756748869269 12074735933362301097603247)
    ·
      refine ⟨18112103900043451646404871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074735933362301097603247 18112103900043451646404871)
      ·
        refine ⟨27168155850065177469607307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18112103900043451646404871 27168155850065177469607307)
        ·
          refine ⟨40752233775097766204410961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27168155850065177469607307 40752233775097766204410961)
          ·
            refine ⟨30564175331323324653308221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40752233775097766204410961 30564175331323324653308221)
            ·
              refine ⟨11461565749246246744990583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30564175331323324653308221 11461565749246246744990583)
              ·
                refine ⟨17192348623869370117485875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11461565749246246744990583 17192348623869370117485875)
                ·
                  refine ⟨25788522935804055176228813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17192348623869370117485875 25788522935804055176228813)
                  ·
                    refine ⟨9670696100926520691085805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25788522935804055176228813 9670696100926520691085805)
                    ·
                      refine ⟨3626511037847445259157177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9670696100926520691085805 3626511037847445259157177)
                      ·
                        rfl

theorem cell23_7062605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7062605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062605 prefixEnd_7062605 := by exact prefixLift 7062605
  have htrace : WordTrace (prefixWord ++ tailWord_7062605) baseStart_7062605 baseEnd_7062605 := by
    simpa [prefixWord, tailWord_7062605, baseEnd_7062605] using wordTrace_append hprefix tailTrace_7062605
  have hstable : (prefixWord ++ tailWord_7062605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062605).length < 2 ^ (prefixWord ++ tailWord_7062605).sum := by decide
  have hdescent : baseEnd_7062605 < baseStart_7062605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062628 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_7062628 : Nat := 118140960795 + 7062628 * 2 ^ 59
def prefixEnd_7062628 : Nat := 4983230072969 + 3 ^ 40 * 7062628 * 2
def baseEnd_7062628 : Nat := 3626522847902498669169571

theorem tailTrace_7062628 : CollatzResearch.WordTrace tailWord_7062628 prefixEnd_7062628 3626522847902498669169571 := by
  unfold tailWord_7062628
  simp only [CollatzResearch.WordTrace]
  refine ⟨128797602728656215838478269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171730136971541621117971025 128797602728656215838478269)
  ·
    refine ⟨48299101023246080939429351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128797602728656215838478269 48299101023246080939429351)
    ·
      refine ⟨72448651534869121409144027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48299101023246080939429351 72448651534869121409144027)
      ·
        refine ⟨108672977302303682113716041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72448651534869121409144027 108672977302303682113716041)
        ·
          refine ⟨81504732976727761585287031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108672977302303682113716041 81504732976727761585287031)
          ·
            refine ⟨122257099465091642377930547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81504732976727761585287031 122257099465091642377930547)
            ·
              refine ⟨183385649197637463566895821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122257099465091642377930547 183385649197637463566895821)
              ·
                refine ⟨68769618449114048837585933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183385649197637463566895821 68769618449114048837585933)
                ·
                  refine ⟨25788606918417768314094725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68769618449114048837585933 25788606918417768314094725)
                  ·
                    refine ⟨4835363797203331558892761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25788606918417768314094725 4835363797203331558892761)
                    ·
                      refine ⟨3626522847902498669169571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835363797203331558892761 3626522847902498669169571)
                      ·
                        rfl

theorem cell23_7062628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_7062628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062628 prefixEnd_7062628 := by exact prefixLift 7062628
  have htrace : WordTrace (prefixWord ++ tailWord_7062628) baseStart_7062628 baseEnd_7062628 := by
    simpa [prefixWord, tailWord_7062628, baseEnd_7062628] using wordTrace_append hprefix tailTrace_7062628
  have hstable : (prefixWord ++ tailWord_7062628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062628).length < 2 ^ (prefixWord ++ tailWord_7062628).sum := by decide
  have hdescent : baseEnd_7062628 < baseStart_7062628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062631 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_7062631 : Nat := 118140960795 + 7062631 * 2 ^ 59
def prefixEnd_7062631 : Nat := 4983230072969 + 3 ^ 40 * 7062631 * 2
def baseEnd_7062631 : Nat := 3626524388344462157432057

theorem tailTrace_7062631 : CollatzResearch.WordTrace tailWord_7062631 prefixEnd_7062631 3626524388344462157432057 := by
  unfold tailWord_7062631
  simp only [CollatzResearch.WordTrace]
  refine ⟨257595314876301563189315747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171730209917534375459543831 257595314876301563189315747)
  ·
    refine ⟨386392972314452344783973621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257595314876301563189315747 386392972314452344783973621)
    ·
      refine ⟨36224341154479907323497527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 386392972314452344783973621 36224341154479907323497527)
      ·
        refine ⟨54336511731719860985246291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36224341154479907323497527 54336511731719860985246291)
        ·
          refine ⟨81504767597579791477869437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54336511731719860985246291 81504767597579791477869437)
          ·
            refine ⟨30564287849092421804201039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81504767597579791477869437 30564287849092421804201039)
            ·
              refine ⟨45846431773638632706301559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30564287849092421804201039 45846431773638632706301559)
              ·
                refine ⟨68769647660457949059452339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45846431773638632706301559 68769647660457949059452339)
                ·
                  refine ⟨103154471490686923589178509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68769647660457949059452339 103154471490686923589178509)
                  ·
                    refine ⟨38682926809007596345941941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103154471490686923589178509 38682926809007596345941941)
                    ·
                      refine ⟨3626524388344462157432057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38682926809007596345941941 3626524388344462157432057)
                      ·
                        rfl

theorem cell23_7062631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_7062631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062631 prefixEnd_7062631 := by exact prefixLift 7062631
  have htrace : WordTrace (prefixWord ++ tailWord_7062631) baseStart_7062631 baseEnd_7062631 := by
    simpa [prefixWord, tailWord_7062631, baseEnd_7062631] using wordTrace_append hprefix tailTrace_7062631
  have hstable : (prefixWord ++ tailWord_7062631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062631).length < 2 ^ (prefixWord ++ tailWord_7062631).sum := by decide
  have hdescent : baseEnd_7062631 < baseStart_7062631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062641 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_7062641 : Nat := 118140960795 + 7062641 * 2 ^ 59
def prefixEnd_7062641 : Nat := 4983230072969 + 3 ^ 40 * 7062641 * 2
def baseEnd_7062641 : Nat := 3626529523151007118307011

theorem tailTrace_7062641 : CollatzResearch.WordTrace tailWord_7062641 prefixEnd_7062641 3626529523151007118307011 := by
  unfold tailWord_7062641
  simp only [CollatzResearch.WordTrace]
  refine ⟨257595679606265334897179777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171730453070843556598119851 257595679606265334897179777)
  ·
    refine ⟨193196759704699001172884833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257595679606265334897179777 193196759704699001172884833)
    ·
      refine ⟨144897569778524250879663625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193196759704699001172884833 144897569778524250879663625)
      ·
        refine ⟨108673177333893188159747719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144897569778524250879663625 108673177333893188159747719)
        ·
          refine ⟨163009766000839782239621579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108673177333893188159747719 163009766000839782239621579)
          ·
            refine ⟨244514649001259673359432369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163009766000839782239621579 244514649001259673359432369)
            ·
              refine ⟨183385986750944755019574277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244514649001259673359432369 183385986750944755019574277)
              ·
                refine ⟨34384872515802141566170177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183385986750944755019574277 34384872515802141566170177)
                ·
                  refine ⟨25788654386851606174627633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34384872515802141566170177 25788654386851606174627633)
                  ·
                    refine ⟨19341490790138704630970725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25788654386851606174627633 19341490790138704630970725)
                    ·
                      refine ⟨3626529523151007118307011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19341490790138704630970725 3626529523151007118307011)
                      ·
                        rfl

theorem cell23_7062641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_7062641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062641 prefixEnd_7062641 := by exact prefixLift 7062641
  have htrace : WordTrace (prefixWord ++ tailWord_7062641) baseStart_7062641 baseEnd_7062641 := by
    simpa [prefixWord, tailWord_7062641, baseEnd_7062641] using wordTrace_append hprefix tailTrace_7062641
  have hstable : (prefixWord ++ tailWord_7062641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062641).length < 2 ^ (prefixWord ++ tailWord_7062641).sum := by decide
  have hdescent : baseEnd_7062641 < baseStart_7062641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062705 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7062705 : Nat := 118140960795 + 7062705 * 2 ^ 59
def prefixEnd_7062705 : Nat := 4983230072969 + 3 ^ 40 * 7062705 * 2
def baseEnd_7062705 : Nat := 3626562385912894867906717

theorem tailTrace_7062705 : CollatzResearch.WordTrace tailWord_7062705 prefixEnd_7062705 3626562385912894867906717 := by
  unfold tailWord_7062705
  simp only [CollatzResearch.WordTrace]
  refine ⟨257598013878033473827509569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171732009252022315885006379 257598013878033473827509569)
  ·
    refine ⟨193198510408525105370632177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257598013878033473827509569 193198510408525105370632177)
    ·
      refine ⟨144898882806393829027974133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193198510408525105370632177 144898882806393829027974133)
      ·
        refine ⟨13584270263099421471372575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144898882806393829027974133 13584270263099421471372575)
        ·
          refine ⟨20376405394649132207058863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584270263099421471372575 20376405394649132207058863)
          ·
            refine ⟨30564608091973698310588295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20376405394649132207058863 30564608091973698310588295)
            ·
              refine ⟨45846912137960547465882443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30564608091973698310588295 45846912137960547465882443)
              ·
                refine ⟨68770368206940821198823665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45846912137960547465882443 68770368206940821198823665)
                ·
                  refine ⟨51577776155205615899117749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68770368206940821198823665 51577776155205615899117749)
                  ·
                    refine ⟨4835416514550526490542289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51577776155205615899117749 4835416514550526490542289)
                    ·
                      refine ⟨3626562385912894867906717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835416514550526490542289 3626562385912894867906717)
                      ·
                        rfl

theorem cell23_7062705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7062705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062705 prefixEnd_7062705 := by exact prefixLift 7062705
  have htrace : WordTrace (prefixWord ++ tailWord_7062705) baseStart_7062705 baseEnd_7062705 := by
    simpa [prefixWord, tailWord_7062705, baseEnd_7062705] using wordTrace_append hprefix tailTrace_7062705
  have hstable : (prefixWord ++ tailWord_7062705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062705).length < 2 ^ (prefixWord ++ tailWord_7062705).sum := by decide
  have hdescent : baseEnd_7062705 < baseStart_7062705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062728 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 5, 4]
def baseStart_7062728 : Nat := 118140960795 + 7062728 * 2 ^ 59
def prefixEnd_7062728 : Nat := 4983230072969 + 3 ^ 40 * 7062728 * 2
def baseEnd_7062728 : Nat := 1208858065322649425973037

theorem tailTrace_7062728 : CollatzResearch.WordTrace tailWord_7062728 prefixEnd_7062728 1208858065322649425973037 := by
  unfold tailWord_7062728
  simp only [CollatzResearch.WordTrace]
  refine ⟨128799426378475074377798419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171732568504633432503731225 128799426378475074377798419)
  ·
    refine ⟨193199139567712611566697629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128799426378475074377798419 193199139567712611566697629)
    ·
      refine ⟨72449677337892229337511611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193199139567712611566697629 72449677337892229337511611)
      ·
        refine ⟨108674516006838344006267417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72449677337892229337511611 108674516006838344006267417)
        ·
          refine ⟨81505887005128758004700563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108674516006838344006267417 81505887005128758004700563)
          ·
            refine ⟨122258830507693137007050845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81505887005128758004700563 122258830507693137007050845)
            ·
              refine ⟨45847061440384926377644067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122258830507693137007050845 45847061440384926377644067)
              ·
                refine ⟨68770592160577389566466101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45847061440384926377644067 68770592160577389566466101)
                ·
                  refine ⟨6447243015054130271856197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68770592160577389566466101 6447243015054130271856197)
                  ·
                    refine ⟨1208858065322649425973037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447243015054130271856197 1208858065322649425973037)
                    ·
                      rfl

theorem cell23_7062728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_7062728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062728 prefixEnd_7062728 := by exact prefixLift 7062728
  have htrace : WordTrace (prefixWord ++ tailWord_7062728) baseStart_7062728 baseEnd_7062728 := by
    simpa [prefixWord, tailWord_7062728, baseEnd_7062728] using wordTrace_append hprefix tailTrace_7062728
  have hstable : (prefixWord ++ tailWord_7062728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062728).length < 2 ^ (prefixWord ++ tailWord_7062728).sum := by decide
  have hdescent : baseEnd_7062728 < baseStart_7062728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062731 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4]
def baseStart_7062731 : Nat := 118140960795 + 7062731 * 2 ^ 59
def prefixEnd_7062731 : Nat := 4983230072969 + 3 ^ 40 * 7062731 * 2
def baseEnd_7062731 : Nat := 3626575736409911766181597

theorem tailTrace_7062731 : CollatzResearch.WordTrace tailWord_7062731 prefixEnd_7062731 3626575736409911766181597 := by
  unfold tailWord_7062731
  simp only [CollatzResearch.WordTrace]
  refine ⟨257598962175939280267956047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171732641450626186845304031 257598962175939280267956047)
  ·
    refine ⟨386398443263908920401934071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257598962175939280267956047 386398443263908920401934071)
    ·
      refine ⟨579597664895863380602901107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386398443263908920401934071 579597664895863380602901107)
      ·
        refine ⟨869396497343795070904351661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579597664895863380602901107 869396497343795070904351661)
        ·
          refine ⟨326023686503923151589131873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 869396497343795070904351661 326023686503923151589131873)
          ·
            refine ⟨244517764877942363691848905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326023686503923151589131873 244517764877942363691848905)
            ·
              refine ⟨183388323658456772768886679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244517764877942363691848905 183388323658456772768886679)
              ·
                refine ⟨275082485487685159153330019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183388323658456772768886679 275082485487685159153330019)
                ·
                  refine ⟨412623728231527738729995029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275082485487685159153330019 412623728231527738729995029)
                  ·
                    refine ⟨19341737260852862752968517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 412623728231527738729995029 19341737260852862752968517)
                    ·
                      refine ⟨3626575736409911766181597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19341737260852862752968517 3626575736409911766181597)
                      ·
                        rfl

theorem cell23_7062731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_7062731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062731 prefixEnd_7062731 := by exact prefixLift 7062731
  have htrace : WordTrace (prefixWord ++ tailWord_7062731) baseStart_7062731 baseEnd_7062731 := by
    simpa [prefixWord, tailWord_7062731, baseEnd_7062731] using wordTrace_append hprefix tailTrace_7062731
  have hstable : (prefixWord ++ tailWord_7062731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062731).length < 2 ^ (prefixWord ++ tailWord_7062731).sum := by decide
  have hdescent : baseEnd_7062731 < baseStart_7062731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062762 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_7062762 : Nat := 118140960795 + 7062762 * 2 ^ 59
def prefixEnd_7062762 : Nat := 4983230072969 + 3 ^ 40 * 7062762 * 2
def baseEnd_7062762 : Nat := 1208863884770067048297985

theorem tailTrace_7062762 : CollatzResearch.WordTrace tailWord_7062762 prefixEnd_7062762 1208863884770067048297985 := by
  unfold tailWord_7062762
  simp only [CollatzResearch.WordTrace]
  refine ⟨64400023209706743140583635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171733395225884648374889693 64400023209706743140583635)
  ·
    refine ⟨96600034814560114710875453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64400023209706743140583635 96600034814560114710875453)
    ·
      refine ⟨36225013055460043016578295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96600034814560114710875453 36225013055460043016578295)
      ·
        refine ⟨54337519583190064524867443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36225013055460043016578295 54337519583190064524867443)
        ·
          refine ⟨81506279374785096787301165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54337519583190064524867443 81506279374785096787301165)
          ·
            refine ⟨30564854765544411295237937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81506279374785096787301165 30564854765544411295237937)
            ·
              refine ⟨22923641074158308471428453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30564854765544411295237937 22923641074158308471428453)
              ·
                refine ⟨4298182701404682838392835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22923641074158308471428453 4298182701404682838392835)
                ·
                  refine ⟨6447274052107024257589253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298182701404682838392835 6447274052107024257589253)
                  ·
                    refine ⟨1208863884770067048297985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447274052107024257589253 1208863884770067048297985)
                    ·
                      rfl

theorem cell23_7062762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_7062762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062762 prefixEnd_7062762 := by exact prefixLift 7062762
  have htrace : WordTrace (prefixWord ++ tailWord_7062762) baseStart_7062762 baseEnd_7062762 := by
    simpa [prefixWord, tailWord_7062762, baseEnd_7062762] using wordTrace_append hprefix tailTrace_7062762
  have hstable : (prefixWord ++ tailWord_7062762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062762).length < 2 ^ (prefixWord ++ tailWord_7062762).sum := by decide
  have hdescent : baseEnd_7062762 < baseStart_7062762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062795 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 1, 5, 2]
def baseStart_7062795 : Nat := 118140960795 + 7062795 * 2 ^ 59
def prefixEnd_7062795 : Nat := 4983230072969 + 3 ^ 40 * 7062795 * 2
def baseEnd_7062795 : Nat := 3626608599171799515781303

theorem tailTrace_7062795 : CollatzResearch.WordTrace tailWord_7062795 prefixEnd_7062795 3626608599171799515781303 := by
  unfold tailWord_7062795
  simp only [CollatzResearch.WordTrace]
  refine ⟨257601296447707419198285839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171734197631804946132190559 257601296447707419198285839)
  ·
    refine ⟨386401944671561128797428759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257601296447707419198285839 386401944671561128797428759)
    ·
      refine ⟨579602917007341693196143139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386401944671561128797428759 579602917007341693196143139)
      ·
        refine ⟨869404375511012539794214709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579602917007341693196143139 869404375511012539794214709)
        ·
          refine ⟨81506660204157425605707629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 869404375511012539794214709 81506660204157425605707629)
          ·
            refine ⟨30564997576559034602140361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81506660204157425605707629 30564997576559034602140361)
            ·
              refine ⟨22923748182419275951605271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30564997576559034602140361 22923748182419275951605271)
              ·
                refine ⟨34385622273628913927407907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22923748182419275951605271 34385622273628913927407907)
                ·
                  refine ⟨51578433410443370891111861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34385622273628913927407907 51578433410443370891111861)
                  ·
                    refine ⟨4835478132229066021041737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51578433410443370891111861 4835478132229066021041737)
                    ·
                      refine ⟨3626608599171799515781303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835478132229066021041737 3626608599171799515781303)
                      ·
                        rfl

theorem cell23_7062795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5, 2].length) (baseStart_7062795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062795 prefixEnd_7062795 := by exact prefixLift 7062795
  have htrace : WordTrace (prefixWord ++ tailWord_7062795) baseStart_7062795 baseEnd_7062795 := by
    simpa [prefixWord, tailWord_7062795, baseEnd_7062795] using wordTrace_append hprefix tailTrace_7062795
  have hstable : (prefixWord ++ tailWord_7062795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062795).length < 2 ^ (prefixWord ++ tailWord_7062795).sum := by decide
  have hdescent : baseEnd_7062795 < baseStart_7062795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062828 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_7062828 : Nat := 118140960795 + 7062828 * 2 ^ 59
def prefixEnd_7062828 : Nat := 4983230072969 + 3 ^ 40 * 7062828 * 2
def baseEnd_7062828 : Nat := 3626625544033397886668651

theorem tailTrace_7062828 : CollatzResearch.WordTrace tailWord_7062828 prefixEnd_7062828 3626625544033397886668651 := by
  unfold tailWord_7062828
  simp only [CollatzResearch.WordTrace]
  refine ⟨128801250028293932917118569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171735000037725243889491425 128801250028293932917118569)
  ·
    refine ⟨96600937521220449687838927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128801250028293932917118569 96600937521220449687838927)
    ·
      refine ⟨144901406281830674531758391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96600937521220449687838927 144901406281830674531758391)
      ·
        refine ⟨217352109422746011797637587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144901406281830674531758391 217352109422746011797637587)
        ·
          refine ⟨326028164134119017696456381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217352109422746011797637587 326028164134119017696456381)
          ·
            refine ⟨122260561550294631636171143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326028164134119017696456381 122260561550294631636171143)
            ·
              refine ⟨183390842325441947454256715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122260561550294631636171143 183390842325441947454256715)
              ·
                refine ⟨275086263488162921181385073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183390842325441947454256715 275086263488162921181385073)
                ·
                  refine ⟨206314697616122190886038805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275086263488162921181385073 206314697616122190886038805)
                  ·
                    refine ⟨9671001450755727697783069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 206314697616122190886038805 9671001450755727697783069)
                    ·
                      refine ⟨3626625544033397886668651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671001450755727697783069 3626625544033397886668651)
                      ·
                        rfl

theorem cell23_7062828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_7062828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062828 prefixEnd_7062828 := by exact prefixLift 7062828
  have htrace : WordTrace (prefixWord ++ tailWord_7062828) baseStart_7062828 baseEnd_7062828 := by
    simpa [prefixWord, tailWord_7062828, baseEnd_7062828] using wordTrace_append hprefix tailTrace_7062828
  have hstable : (prefixWord ++ tailWord_7062828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062828).length < 2 ^ (prefixWord ++ tailWord_7062828).sum := by decide
  have hdescent : baseEnd_7062828 < baseStart_7062828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062842 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2]
def baseStart_7062842 : Nat := 118140960795 + 7062842 * 2 ^ 59
def prefixEnd_7062842 : Nat := 4983230072969 + 3 ^ 40 * 7062842 * 2
def baseEnd_7062842 : Nat := 3626632732762560831893587

theorem tailTrace_7062842 : CollatzResearch.WordTrace tailWord_7062842 prefixEnd_7062842 3626632732762560831893587 := by
  unfold tailWord_7062842
  simp only [CollatzResearch.WordTrace]
  refine ⟨64400752669634286556311695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171735340452358097483497853 64400752669634286556311695)
  ·
    refine ⟨96601129004451429834467543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64400752669634286556311695 96601129004451429834467543)
    ·
      refine ⟨144901693506677144751701315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96601129004451429834467543 144901693506677144751701315)
      ·
        refine ⟨217352540260015717127551973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144901693506677144751701315 217352540260015717127551973)
        ·
          refine ⟨40753601298752946961415995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217352540260015717127551973 40753601298752946961415995)
          ·
            refine ⟨61130401948129420442123993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40753601298752946961415995 61130401948129420442123993)
            ·
              refine ⟨45847801461097065331592995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61130401948129420442123993 45847801461097065331592995)
              ·
                refine ⟨68771702191645597997389493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45847801461097065331592995 68771702191645597997389493)
                ·
                  refine ⟨6447347080466774812255265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68771702191645597997389493 6447347080466774812255265)
                  ·
                    refine ⟨4835510310350081109191449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6447347080466774812255265 4835510310350081109191449)
                    ·
                      refine ⟨3626632732762560831893587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835510310350081109191449 3626632732762560831893587)
                      ·
                        rfl

theorem cell23_7062842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_7062842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062842 prefixEnd_7062842 := by exact prefixLift 7062842
  have htrace : WordTrace (prefixWord ++ tailWord_7062842) baseStart_7062842 baseEnd_7062842 := by
    simpa [prefixWord, tailWord_7062842, baseEnd_7062842] using wordTrace_append hprefix tailTrace_7062842
  have hstable : (prefixWord ++ tailWord_7062842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062842).length < 2 ^ (prefixWord ++ tailWord_7062842).sum := by decide
  have hdescent : baseEnd_7062842 < baseStart_7062842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062852 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7062852 : Nat := 118140960795 + 7062852 * 2 ^ 59
def prefixEnd_7062852 : Nat := 4983230072969 + 3 ^ 40 * 7062852 * 2
def baseEnd_7062852 : Nat := 1208879289189701930922847

theorem tailTrace_7062852 : CollatzResearch.WordTrace tailWord_7062852 prefixEnd_7062852 1208879289189701930922847 := by
  unfold tailWord_7062852
  simp only [CollatzResearch.WordTrace]
  refine ⟨128801687704250458966555405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171735583605667278622073873 128801687704250458966555405)
  ·
    refine ⟨48300632889093922112458277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128801687704250458966555405 48300632889093922112458277)
    ·
      refine ⟨9056368666705110396085927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48300632889093922112458277 9056368666705110396085927)
      ·
        refine ⟨13584553000057665594128891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056368666705110396085927 13584553000057665594128891)
        ·
          refine ⟨20376829500086498391193337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584553000057665594128891 20376829500086498391193337)
          ·
            refine ⟨15282622125064873793395003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20376829500086498391193337 15282622125064873793395003)
            ·
              refine ⟨22923933187597310690092505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15282622125064873793395003 22923933187597310690092505)
              ·
                refine ⟨17192949890697983017569379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22923933187597310690092505 17192949890697983017569379)
                ·
                  refine ⟨25789424836046974526354069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17192949890697983017569379 25789424836046974526354069)
                  ·
                    refine ⟨1208879289189701930922847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25789424836046974526354069 1208879289189701930922847)
                    ·
                      rfl

theorem cell23_7062852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7062852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062852 prefixEnd_7062852 := by exact prefixLift 7062852
  have htrace : WordTrace (prefixWord ++ tailWord_7062852) baseStart_7062852 baseEnd_7062852 := by
    simpa [prefixWord, tailWord_7062852, baseEnd_7062852] using wordTrace_append hprefix tailTrace_7062852
  have hstable : (prefixWord ++ tailWord_7062852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062852).length < 2 ^ (prefixWord ++ tailWord_7062852).sum := by decide
  have hdescent : baseEnd_7062852 < baseStart_7062852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062855 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_7062855 : Nat := 118140960795 + 7062855 * 2 ^ 59
def prefixEnd_7062855 : Nat := 4983230072969 + 3 ^ 40 * 7062855 * 2
def baseEnd_7062855 : Nat := 3626639408011069281031027

theorem tailTrace_7062855 : CollatzResearch.WordTrace tailWord_7062855 prefixEnd_7062855 3626639408011069281031027 := by
  unfold tailWord_7062855
  simp only [CollatzResearch.WordTrace]
  refine ⟨257603484827490049445470019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171735656551660032963646679 257603484827490049445470019)
  ·
    refine ⟨386405227241235074168205029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257603484827490049445470019 386405227241235074168205029)
    ·
      refine ⟨72450980107731576406538443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386405227241235074168205029 72450980107731576406538443)
      ·
        refine ⟨108676470161597364609807665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72450980107731576406538443 108676470161597364609807665)
        ·
          refine ⟨81507352621198023457355749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108676470161597364609807665 81507352621198023457355749)
          ·
            refine ⟨15282628616474629398254203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81507352621198023457355749 15282628616474629398254203)
            ·
              refine ⟨22923942924711944097381305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15282628616474629398254203 22923942924711944097381305)
              ·
                refine ⟨17192957193533958073035979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22923942924711944097381305 17192957193533958073035979)
                ·
                  refine ⟨25789435790300937109553969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17192957193533958073035979 25789435790300937109553969)
                  ·
                    refine ⟨19342076842725702832165477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25789435790300937109553969 19342076842725702832165477)
                    ·
                      refine ⟨3626639408011069281031027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19342076842725702832165477 3626639408011069281031027)
                      ·
                        rfl

theorem cell23_7062855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_7062855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062855 prefixEnd_7062855 := by exact prefixLift 7062855
  have htrace : WordTrace (prefixWord ++ tailWord_7062855) baseStart_7062855 baseEnd_7062855 := by
    simpa [prefixWord, tailWord_7062855, baseEnd_7062855] using wordTrace_append hprefix tailTrace_7062855
  have hstable : (prefixWord ++ tailWord_7062855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062855).length < 2 ^ (prefixWord ++ tailWord_7062855).sum := by decide
  have hdescent : baseEnd_7062855 < baseStart_7062855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062892 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_7062892 : Nat := 118140960795 + 7062892 * 2 ^ 59
def prefixEnd_7062892 : Nat := 4983230072969 + 3 ^ 40 * 7062892 * 2
def baseEnd_7062892 : Nat := 3626658406795285636268357

theorem tailTrace_7062892 : CollatzResearch.WordTrace tailWord_7062892 prefixEnd_7062892 3626658406795285636268357 := by
  unfold tailWord_7062892
  simp only [CollatzResearch.WordTrace]
  refine ⟨128802417164178002382283465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171736556218904003176377953 128802417164178002382283465)
  ·
    refine ⟨96601812873133501786712599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128802417164178002382283465 96601812873133501786712599)
    ·
      refine ⟨144902719309700252680068899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96601812873133501786712599 144902719309700252680068899)
      ·
        refine ⟨217354078964550379020103349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144902719309700252680068899 217354078964550379020103349)
        ·
          refine ⟨20376944902926598033134689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217354078964550379020103349 20376944902926598033134689)
          ·
            refine ⟨15282708677194948524851017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20376944902926598033134689 15282708677194948524851017)
            ·
              refine ⟨11462031507896211393638263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15282708677194948524851017 11462031507896211393638263)
              ·
                refine ⟨17193047261844317090457395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462031507896211393638263 17193047261844317090457395)
                ·
                  refine ⟨25789570892766475635686093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17193047261844317090457395 25789570892766475635686093)
                  ·
                    refine ⟨9671089084787428363382285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25789570892766475635686093 9671089084787428363382285)
                    ·
                      refine ⟨3626658406795285636268357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671089084787428363382285 3626658406795285636268357)
                      ·
                        rfl

theorem cell23_7062892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_7062892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062892 prefixEnd_7062892 := by exact prefixLift 7062892
  have htrace : WordTrace (prefixWord ++ tailWord_7062892) baseStart_7062892 baseEnd_7062892 := by
    simpa [prefixWord, tailWord_7062892, baseEnd_7062892] using wordTrace_append hprefix tailTrace_7062892
  have hstable : (prefixWord ++ tailWord_7062892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062892).length < 2 ^ (prefixWord ++ tailWord_7062892).sum := by decide
  have hdescent : baseEnd_7062892 < baseStart_7062892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062908 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_7062908 : Nat := 118140960795 + 7062908 * 2 ^ 59
def prefixEnd_7062908 : Nat := 4983230072969 + 3 ^ 40 * 7062908 * 2
def baseEnd_7062908 : Nat := 1208888874161919191222761

theorem tailTrace_7062908 : CollatzResearch.WordTrace tailWord_7062908 prefixEnd_7062908 1208888874161919191222761 := by
  unfold tailWord_7062908
  simp only [CollatzResearch.WordTrace]
  refine ⟨128802708948149019748574689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171736945264198692998099585 128802708948149019748574689)
  ·
    refine ⟨96602031711111764811431017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128802708948149019748574689 96602031711111764811431017)
    ·
      refine ⟨72451523783333823608573263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96602031711111764811431017 72451523783333823608573263)
      ·
        refine ⟨108677285675000735412859895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72451523783333823608573263 108677285675000735412859895)
        ·
          refine ⟨163015928512501103119289843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108677285675000735412859895 163015928512501103119289843)
          ·
            refine ⟨244523892768751654678934765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163015928512501103119289843 244523892768751654678934765)
            ·
              refine ⟨91696459788281870504600537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244523892768751654678934765 91696459788281870504600537)
              ·
                refine ⟨68772344841211402878450403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91696459788281870504600537 68772344841211402878450403)
                ·
                  refine ⟨103158517261817104317675605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68772344841211402878450403 103158517261817104317675605)
                  ·
                    refine ⟨1208888874161919191222761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103158517261817104317675605 1208888874161919191222761)
                    ·
                      rfl

theorem cell23_7062908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_7062908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062908 prefixEnd_7062908 := by exact prefixLift 7062908
  have htrace : WordTrace (prefixWord ++ tailWord_7062908) baseStart_7062908 baseEnd_7062908 := by
    simpa [prefixWord, tailWord_7062908, baseEnd_7062908] using wordTrace_append hprefix tailTrace_7062908
  have hstable : (prefixWord ++ tailWord_7062908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062908).length < 2 ^ (prefixWord ++ tailWord_7062908).sum := by decide
  have hdescent : baseEnd_7062908 < baseStart_7062908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062910 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7062910 : Nat := 118140960795 + 7062910 * 2 ^ 59
def prefixEnd_7062910 : Nat := 4983230072969 + 3 ^ 40 * 7062910 * 2
def baseEnd_7062910 : Nat := 3626667649447066565843275

theorem tailTrace_7062910 : CollatzResearch.WordTrace tailWord_7062910 prefixEnd_7062910 3626667649447066565843275 := by
  unfold tailWord_7062910
  simp only [CollatzResearch.WordTrace]
  refine ⟨32200686355286349229840273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171736993894860529225814789 32200686355286349229840273)
  ·
    refine ⟨24150514766464761922380205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32200686355286349229840273 24150514766464761922380205)
    ·
      refine ⟨9056443037424285720892577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24150514766464761922380205 9056443037424285720892577)
      ·
        refine ⟨6792332278068214290669433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9056443037424285720892577 6792332278068214290669433)
        ·
          refine ⟨5094249208551160718002075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6792332278068214290669433 5094249208551160718002075)
          ·
            refine ⟨7641373812826741077003113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094249208551160718002075 7641373812826741077003113)
            ·
              refine ⟨5731030359620055807752335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7641373812826741077003113 5731030359620055807752335)
              ·
                refine ⟨8596545539430083711628503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731030359620055807752335 8596545539430083711628503)
                ·
                  refine ⟨12894818309145125567442755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8596545539430083711628503 12894818309145125567442755)
                  ·
                    refine ⟨19342227463717688351164133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12894818309145125567442755 19342227463717688351164133)
                    ·
                      refine ⟨3626667649447066565843275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19342227463717688351164133 3626667649447066565843275)
                      ·
                        rfl

theorem cell23_7062910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7062910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062910 prefixEnd_7062910 := by exact prefixLift 7062910
  have htrace : WordTrace (prefixWord ++ tailWord_7062910) baseStart_7062910 baseEnd_7062910 := by
    simpa [prefixWord, tailWord_7062910, baseEnd_7062910] using wordTrace_append hprefix tailTrace_7062910
  have hstable : (prefixWord ++ tailWord_7062910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062910).length < 2 ^ (prefixWord ++ tailWord_7062910).sum := by decide
  have hdescent : baseEnd_7062910 < baseStart_7062910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062913 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7062913 : Nat := 118140960795 + 7062913 * 2 ^ 59
def prefixEnd_7062913 : Nat := 4983230072969 + 3 ^ 40 * 7062913 * 2
def baseEnd_7062913 : Nat := 3626669189889030054105761

theorem tailTrace_7062913 : CollatzResearch.WordTrace tailWord_7062913 prefixEnd_7062913 3626669189889030054105761 := by
  unfold tailWord_7062913
  simp only [CollatzResearch.WordTrace]
  refine ⟨257605600261279925351081393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171737066840853283567387595 257605600261279925351081393)
  ·
    refine ⟨193204200195959944013311045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257605600261279925351081393 193204200195959944013311045)
    ·
      refine ⟨36225787536742489502495821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193204200195959944013311045 36225787536742489502495821)
      ·
        refine ⟨13584670326278433563435933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36225787536742489502495821 13584670326278433563435933)
        ·
          refine ⟨5094251372354412586288475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13584670326278433563435933 5094251372354412586288475)
          ·
            refine ⟨7641377058531618879432713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094251372354412586288475 7641377058531618879432713)
            ·
              refine ⟨5731032793898714159574535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7641377058531618879432713 5731032793898714159574535)
              ·
                refine ⟨8596549190848071239361803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731032793898714159574535 8596549190848071239361803)
                ·
                  refine ⟨12894823786272106859042705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8596549190848071239361803 12894823786272106859042705)
                  ·
                    refine ⟨9671117839704080144282029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12894823786272106859042705 9671117839704080144282029)
                    ·
                      refine ⟨3626669189889030054105761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671117839704080144282029 3626669189889030054105761)
                      ·
                        rfl

theorem cell23_7062913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7062913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062913 prefixEnd_7062913 := by exact prefixLift 7062913
  have htrace : WordTrace (prefixWord ++ tailWord_7062913) baseStart_7062913 baseEnd_7062913 := by
    simpa [prefixWord, tailWord_7062913, baseEnd_7062913] using wordTrace_append hprefix tailTrace_7062913
  have hstable : (prefixWord ++ tailWord_7062913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062913).length < 2 ^ (prefixWord ++ tailWord_7062913).sum := by decide
  have hdescent : baseEnd_7062913 < baseStart_7062913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062919 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_7062919 : Nat := 118140960795 + 7062919 * 2 ^ 59
def prefixEnd_7062919 : Nat := 4983230072969 + 3 ^ 40 * 7062919 * 2
def baseEnd_7062919 : Nat := 3626672270772957030630733

theorem tailTrace_7062919 : CollatzResearch.WordTrace tailWord_7062919 prefixEnd_7062919 3626672270772957030630733 := by
  unfold tailWord_7062919
  simp only [CollatzResearch.WordTrace]
  refine ⟨257605819099258188375799811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171737212732838792250533207 257605819099258188375799811)
  ·
    refine ⟨386408728648887282563699717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257605819099258188375799811 386408728648887282563699717)
    ·
      refine ⟨72451636621666365480693697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386408728648887282563699717 72451636621666365480693697)
      ·
        refine ⟨54338727466249774110520273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72451636621666365480693697 54338727466249774110520273)
        ·
          refine ⟨40754045599687330582890205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54338727466249774110520273 40754045599687330582890205)
          ·
            refine ⟨15282767099882748968583827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40754045599687330582890205 15282767099882748968583827)
            ·
              refine ⟨22924150649824123452875741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15282767099882748968583827 22924150649824123452875741)
              ·
                refine ⟨8596556493684046294828403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22924150649824123452875741 8596556493684046294828403)
                ·
                  refine ⟨12894834740526069442242605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8596556493684046294828403 12894834740526069442242605)
                  ·
                    refine ⟨4835563027697276040840977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12894834740526069442242605 4835563027697276040840977)
                    ·
                      refine ⟨3626672270772957030630733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835563027697276040840977 3626672270772957030630733)
                      ·
                        rfl

theorem cell23_7062919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_7062919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062919 prefixEnd_7062919 := by exact prefixLift 7062919
  have htrace : WordTrace (prefixWord ++ tailWord_7062919) baseStart_7062919 baseEnd_7062919 := by
    simpa [prefixWord, tailWord_7062919, baseEnd_7062919] using wordTrace_append hprefix tailTrace_7062919
  have hstable : (prefixWord ++ tailWord_7062919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062919).length < 2 ^ (prefixWord ++ tailWord_7062919).sum := by decide
  have hdescent : baseEnd_7062919 < baseStart_7062919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063049 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 1, 4]
def baseStart_7063049 : Nat := 118140960795 + 7063049 * 2 ^ 59
def prefixEnd_7063049 : Nat := 4983230072969 + 3 ^ 40 * 7063049 * 2
def baseEnd_7063049 : Nat := 1208913007752680507335045

theorem tailTrace_7063049 : CollatzResearch.WordTrace tailWord_7063049 prefixEnd_7063049 1208913007752680507335045 := by
  unfold tailWord_7063049
  simp only [CollatzResearch.WordTrace]
  refine ⟨257610560588787220578032201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171740373725858147052021467 257610560588787220578032201)
  ·
    refine ⟨193207920441590415433524151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257610560588787220578032201 193207920441590415433524151)
    ·
      refine ⟨289811880662385623150286227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193207920441590415433524151 289811880662385623150286227)
      ·
        refine ⟨434717820993578434725429341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289811880662385623150286227 434717820993578434725429341)
        ·
          refine ⟨163019182872591913022036003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434717820993578434725429341 163019182872591913022036003)
          ·
            refine ⟨244528774308887869533054005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163019182872591913022036003 244528774308887869533054005)
            ·
              refine ⟨22924572591458237768723813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244528774308887869533054005 22924572591458237768723813)
              ·
                refine ⟨4298357360898419581635715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22924572591458237768723813 4298357360898419581635715)
                ·
                  refine ⟨6447536041347629372453573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298357360898419581635715 6447536041347629372453573)
                  ·
                    refine ⟨1208913007752680507335045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447536041347629372453573 1208913007752680507335045)
                    ·
                      rfl

theorem cell23_7063049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 4].length) (baseStart_7063049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063049 prefixEnd_7063049 := by exact prefixLift 7063049
  have htrace : WordTrace (prefixWord ++ tailWord_7063049) baseStart_7063049 baseEnd_7063049 := by
    simpa [prefixWord, tailWord_7063049, baseEnd_7063049] using wordTrace_append hprefix tailTrace_7063049
  have hstable : (prefixWord ++ tailWord_7063049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063049).length < 2 ^ (prefixWord ++ tailWord_7063049).sum := by decide
  have hdescent : baseEnd_7063049 < baseStart_7063049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063070 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7063070 : Nat := 118140960795 + 7063070 * 2 ^ 59
def prefixEnd_7063070 : Nat := 4983230072969 + 3 ^ 40 * 7063070 * 2
def baseEnd_7063070 : Nat := 1208916602117261979947513

theorem tailTrace_7063070 : CollatzResearch.WordTrace tailWord_7063070 prefixEnd_7063070 1208916602117261979947513 := by
  unfold tailWord_7063070
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201415815213892645568333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171740884347807427443031109 32201415815213892645568333)
  ·
    refine ⟨12075530930705209742088125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32201415815213892645568333 12075530930705209742088125)
    ·
      refine ⟨4528324099014453653283047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12075530930705209742088125 4528324099014453653283047)
      ·
        refine ⟨6792486148521680479924571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528324099014453653283047 6792486148521680479924571)
        ·
          refine ⟨10188729222782520719886857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792486148521680479924571 10188729222782520719886857)
          ·
            refine ⟨7641546917086890539915143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10188729222782520719886857 7641546917086890539915143)
            ·
              refine ⟨11462320375630335809872715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641546917086890539915143 11462320375630335809872715)
              ·
                refine ⟨17193480563445503714809073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462320375630335809872715 17193480563445503714809073)
                ·
                  refine ⟨12895110422584127786106805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17193480563445503714809073 12895110422584127786106805)
                  ·
                    refine ⟨1208916602117261979947513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12895110422584127786106805 1208916602117261979947513)
                    ·
                      rfl

theorem cell23_7063070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7063070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063070 prefixEnd_7063070 := by exact prefixLift 7063070
  have htrace : WordTrace (prefixWord ++ tailWord_7063070) baseStart_7063070 baseEnd_7063070 := by
    simpa [prefixWord, tailWord_7063070, baseEnd_7063070] using wordTrace_append hprefix tailTrace_7063070
  have hstable : (prefixWord ++ tailWord_7063070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063070).length < 2 ^ (prefixWord ++ tailWord_7063070).sum := by decide
  have hdescent : baseEnd_7063070 < baseStart_7063070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063152 : List Nat := [2, 1, 1, 1, 6, 3, 9]
def baseStart_7063152 : Nat := 118140960795 + 7063152 * 2 ^ 59
def prefixEnd_7063152 : Nat := 4983230072969 + 3 ^ 40 * 7063152 * 2
def baseEnd_7063152 : Nat := 44775208787227834802681

theorem tailTrace_7063152 : CollatzResearch.WordTrace tailWord_7063152 prefixEnd_7063152 44775208787227834802681 := by
  unfold tailWord_7063152
  simp only [CollatzResearch.WordTrace]
  refine ⟨128807158653707034584515855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171742878204942712779354473 128807158653707034584515855)
  ·
    refine ⟨193210737980560551876773783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128807158653707034584515855 193210737980560551876773783)
    ·
      refine ⟨289816106970840827815160675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193210737980560551876773783 289816106970840827815160675)
      ·
        refine ⟨434724160456261241722741013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289816106970840827815160675 434724160456261241722741013)
        ·
          refine ⟨20377695021387245705753485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 434724160456261241722741013 20377695021387245705753485)
          ·
            refine ⟨7641635633020217139657557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20377695021387245705753485 7641635633020217139657557)
            ·
              refine ⟨44775208787227834802681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7641635633020217139657557 44775208787227834802681)
              ·
                rfl

theorem cell23_7063152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 9].length) (baseStart_7063152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063152 prefixEnd_7063152 := by exact prefixLift 7063152
  have htrace : WordTrace (prefixWord ++ tailWord_7063152) baseStart_7063152 baseEnd_7063152 := by
    simpa [prefixWord, tailWord_7063152, baseEnd_7063152] using wordTrace_append hprefix tailTrace_7063152
  have hstable : (prefixWord ++ tailWord_7063152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063152).length < 2 ^ (prefixWord ++ tailWord_7063152).sum := by decide
  have hdescent : baseEnd_7063152 < baseStart_7063152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_7063162 : Nat := 118140960795 + 7063162 * 2 ^ 59
def prefixEnd_7063162 : Nat := 4983230072969 + 3 ^ 40 * 7063162 * 2
def baseEnd_7063162 : Nat := 3626797046571999579892115

theorem tailTrace_7063162 : CollatzResearch.WordTrace tailWord_7063162 prefixEnd_7063162 3626797046571999579892115 := by
  unfold tailWord_7063162
  simp only [CollatzResearch.WordTrace]
  refine ⟨64403670509344460219223935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171743121358251893917930493 64403670509344460219223935)
  ·
    refine ⟨96605505764016690328835903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64403670509344460219223935 96605505764016690328835903)
    ·
      refine ⟨144908258646025035493253855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96605505764016690328835903 144908258646025035493253855)
      ·
        refine ⟨217362387969037553239880783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144908258646025035493253855 217362387969037553239880783)
        ·
          refine ⟨326043581953556329859821175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217362387969037553239880783 326043581953556329859821175)
          ·
            refine ⟨489065372930334494789731763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326043581953556329859821175 489065372930334494789731763)
            ·
              refine ⟨733598059395501742184597645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489065372930334494789731763 733598059395501742184597645)
              ·
                refine ⟨275099272273313153319224117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733598059395501742184597645 275099272273313153319224117)
                ·
                  refine ⟨25790556775623108123677261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275099272273313153319224117 25790556775623108123677261)
                  ·
                    refine ⟨9671458790858665546378973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25790556775623108123677261 9671458790858665546378973)
                    ·
                      refine ⟨3626797046571999579892115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671458790858665546378973 3626797046571999579892115)
                      ·
                        rfl

theorem cell23_7063162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_7063162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063162 prefixEnd_7063162 := by exact prefixLift 7063162
  have htrace : WordTrace (prefixWord ++ tailWord_7063162) baseStart_7063162 baseEnd_7063162 := by
    simpa [prefixWord, tailWord_7063162, baseEnd_7063162] using wordTrace_append hprefix tailTrace_7063162
  have hstable : (prefixWord ++ tailWord_7063162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063162).length < 2 ^ (prefixWord ++ tailWord_7063162).sum := by decide
  have hdescent : baseEnd_7063162 < baseStart_7063162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063196 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7063196 : Nat := 118140960795 + 7063196 * 2 ^ 59
def prefixEnd_7063196 : Nat := 4983230072969 + 3 ^ 40 * 7063196 * 2
def baseEnd_7063196 : Nat := 3626814504914252446866959

theorem tailTrace_7063196 : CollatzResearch.WordTrace tailWord_7063196 prefixEnd_7063196 3626814504914252446866959 := by
  unfold tailWord_7063196
  simp only [CollatzResearch.WordTrace]
  refine ⟨128807961059627332341816721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171743948079503109789088961 128807961059627332341816721)
  ·
    refine ⟨96605970794720499256362541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128807961059627332341816721 96605970794720499256362541)
    ·
      refine ⟨36227239048020187221135953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96605970794720499256362541 36227239048020187221135953)
      ·
        refine ⟨27170429286015140415851965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36227239048020187221135953 27170429286015140415851965)
        ·
          refine ⟨10188910982255677655944487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27170429286015140415851965 10188910982255677655944487)
          ·
            refine ⟨15283366473383516483916731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10188910982255677655944487 15283366473383516483916731)
            ·
              refine ⟨22925049710075274725875097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15283366473383516483916731 22925049710075274725875097)
              ·
                refine ⟨17193787282556456044406323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22925049710075274725875097 17193787282556456044406323)
                ·
                  refine ⟨25790680923834684066609485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17193787282556456044406323 25790680923834684066609485)
                  ·
                    refine ⟨9671505346438006524978557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25790680923834684066609485 9671505346438006524978557)
                    ·
                      refine ⟨3626814504914252446866959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671505346438006524978557 3626814504914252446866959)
                      ·
                        rfl

theorem cell23_7063196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7063196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063196 prefixEnd_7063196 := by exact prefixLift 7063196
  have htrace : WordTrace (prefixWord ++ tailWord_7063196) baseStart_7063196 baseEnd_7063196 := by
    simpa [prefixWord, tailWord_7063196, baseEnd_7063196] using wordTrace_append hprefix tailTrace_7063196
  have hstable : (prefixWord ++ tailWord_7063196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063196).length < 2 ^ (prefixWord ++ tailWord_7063196).sum := by decide
  have hdescent : baseEnd_7063196 < baseStart_7063196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063213 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7063213 : Nat := 118140960795 + 7063213 * 2 ^ 59
def prefixEnd_7063213 : Nat := 4983230072969 + 3 ^ 40 * 7063213 * 2
def baseEnd_7063213 : Nat := 3626823234085378880354381

theorem tailTrace_7063213 : CollatzResearch.WordTrace tailWord_7063213 prefixEnd_7063213 3626823234085378880354381 := by
  unfold tailWord_7063213
  simp only [CollatzResearch.WordTrace]
  refine ⟨257616542160193076587002293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171744361440128717724668195 257616542160193076587002293)
  ·
    refine ⟨24151550827518100930031465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257616542160193076587002293 24151550827518100930031465)
    ·
      refine ⟨18113663120638575697523599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24151550827518100930031465 18113663120638575697523599)
      ·
        refine ⟨27170494680957863546285399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18113663120638575697523599 27170494680957863546285399)
        ·
          refine ⟨40755742021436795319428099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27170494680957863546285399 40755742021436795319428099)
          ·
            refine ⟨61133613032155192979142149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40755742021436795319428099 61133613032155192979142149)
            ·
              refine ⟨11462552443529098683589153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61133613032155192979142149 11462552443529098683589153)
              ·
                refine ⟨8596914332646824012691865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11462552443529098683589153 8596914332646824012691865)
                ·
                  refine ⟨6447685749485118009518899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8596914332646824012691865 6447685749485118009518899)
                  ·
                    refine ⟨9671528624227677014278349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6447685749485118009518899 9671528624227677014278349)
                    ·
                      refine ⟨3626823234085378880354381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671528624227677014278349 3626823234085378880354381)
                      ·
                        rfl

theorem cell23_7063213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7063213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063213 prefixEnd_7063213 := by exact prefixLift 7063213
  have htrace : WordTrace (prefixWord ++ tailWord_7063213) baseStart_7063213 baseEnd_7063213 := by
    simpa [prefixWord, tailWord_7063213, baseEnd_7063213] using wordTrace_append hprefix tailTrace_7063213
  have hstable : (prefixWord ++ tailWord_7063213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063213).length < 2 ^ (prefixWord ++ tailWord_7063213).sum := by decide
  have hdescent : baseEnd_7063213 < baseStart_7063213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063219 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 3, 4, 2]
def baseStart_7063219 : Nat := 118140960795 + 7063219 * 2 ^ 59
def prefixEnd_7063219 : Nat := 4983230072969 + 3 ^ 40 * 7063219 * 2
def baseEnd_7063219 : Nat := 3626826314969305856879353

theorem tailTrace_7063219 : CollatzResearch.WordTrace tailWord_7063219 prefixEnd_7063219 3626826314969305856879353 := by
  unfold tailWord_7063219
  simp only [CollatzResearch.WordTrace]
  refine ⟨257616760998171339611720711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171744507332114226407813807 257616760998171339611720711)
  ·
    refine ⟨386425141497257009417581067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257616760998171339611720711 386425141497257009417581067)
    ·
      refine ⟨579637712245885514126371601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386425141497257009417581067 579637712245885514126371601)
      ·
        refine ⟨434728284184414135594778701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579637712245885514126371601 434728284184414135594778701)
        ·
          refine ⟨163023106569155300848042013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434728284184414135594778701 163023106569155300848042013)
          ·
            refine ⟨61133664963433237818015755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163023106569155300848042013 61133664963433237818015755)
            ·
              refine ⟨91700497445149856727023633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61133664963433237818015755 91700497445149856727023633)
              ·
                refine ⟨68775373083862392545267725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91700497445149856727023633 68775373083862392545267725)
                ·
                  refine ⟨25790764906448397204475397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68775373083862392545267725 25790764906448397204475397)
                  ·
                    refine ⟨4835768419959074475839137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25790764906448397204475397 4835768419959074475839137)
                    ·
                      refine ⟨3626826314969305856879353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835768419959074475839137 3626826314969305856879353)
                      ·
                        rfl

theorem cell23_7063219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4, 2].length) (baseStart_7063219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063219 prefixEnd_7063219 := by exact prefixLift 7063219
  have htrace : WordTrace (prefixWord ++ tailWord_7063219) baseStart_7063219 baseEnd_7063219 := by
    simpa [prefixWord, tailWord_7063219, baseEnd_7063219] using wordTrace_append hprefix tailTrace_7063219
  have hstable : (prefixWord ++ tailWord_7063219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063219).length < 2 ^ (prefixWord ++ tailWord_7063219).sum := by decide
  have hdescent : baseEnd_7063219 < baseStart_7063219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063269 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_7063269 : Nat := 118140960795 + 7063269 * 2 ^ 59
def prefixEnd_7063269 : Nat := 4983230072969 + 3 ^ 40 * 7063269 * 2
def baseEnd_7063269 : Nat := 3626851989002030661254123

theorem tailTrace_7063269 : CollatzResearch.WordTrace tailWord_7063269 prefixEnd_7063269 3626851989002030661254123 := by
  unfold tailWord_7063269
  simp only [CollatzResearch.WordTrace]
  refine ⟨257618584647990198151040861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171745723098660132100693907 257618584647990198151040861)
  ·
    refine ⟨96606969242996324306640323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257618584647990198151040861 96606969242996324306640323)
    ·
      refine ⟨144910453864494486459960485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96606969242996324306640323 144910453864494486459960485)
      ·
        refine ⟨27170710099592716211242591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144910453864494486459960485 27170710099592716211242591)
        ·
          refine ⟨40756065149389074316863887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27170710099592716211242591 40756065149389074316863887)
          ·
            refine ⟨61134097724083611475295831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40756065149389074316863887 61134097724083611475295831)
            ·
              refine ⟨91701146586125417212943747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61134097724083611475295831 91701146586125417212943747)
              ·
                refine ⟨137551719879188125819415621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91701146586125417212943747 137551719879188125819415621)
                ·
                  refine ⟨25790947477347773591140429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137551719879188125819415621 25790947477347773591140429)
                  ·
                    refine ⟨9671605304005415096677661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25790947477347773591140429 9671605304005415096677661)
                    ·
                      refine ⟨3626851989002030661254123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671605304005415096677661 3626851989002030661254123)
                      ·
                        rfl

theorem cell23_7063269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_7063269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063269 prefixEnd_7063269 := by exact prefixLift 7063269
  have htrace : WordTrace (prefixWord ++ tailWord_7063269) baseStart_7063269 baseEnd_7063269 := by
    simpa [prefixWord, tailWord_7063269, baseEnd_7063269] using wordTrace_append hprefix tailTrace_7063269
  have hstable : (prefixWord ++ tailWord_7063269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063269).length < 2 ^ (prefixWord ++ tailWord_7063269).sum := by decide
  have hdescent : baseEnd_7063269 < baseStart_7063269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063286 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_7063286 : Nat := 118140960795 + 7063286 * 2 ^ 59
def prefixEnd_7063286 : Nat := 4983230072969 + 3 ^ 40 * 7063286 * 2
def baseEnd_7063286 : Nat := 3626860718173157094741545

theorem tailTrace_7063286 : CollatzResearch.WordTrace tailWord_7063286 prefixEnd_7063286 3626860718173157094741545 := by
  unfold tailWord_7063286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101200293058038128400607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171746136459285740036273141 16101200293058038128400607)
  ·
    refine ⟨24151800439587057192600911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16101200293058038128400607 24151800439587057192600911)
    ·
      refine ⟨36227700659380585788901367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24151800439587057192600911 36227700659380585788901367)
      ·
        refine ⟨54341550989070878683352051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36227700659380585788901367 54341550989070878683352051)
        ·
          refine ⟨81512326483606318025028077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54341550989070878683352051 81512326483606318025028077)
          ·
            refine ⟨30567122431352369259385529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81512326483606318025028077 30567122431352369259385529)
            ·
              refine ⟨22925341823514276944539147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30567122431352369259385529 22925341823514276944539147)
              ·
                refine ⟨34388012735271415416808721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22925341823514276944539147 34388012735271415416808721)
                ·
                  refine ⟨25791009551453561562606541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34388012735271415416808721 25791009551453561562606541)
                  ·
                    refine ⟨9671628581795085585977453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25791009551453561562606541 9671628581795085585977453)
                    ·
                      refine ⟨3626860718173157094741545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671628581795085585977453 3626860718173157094741545)
                      ·
                        rfl

theorem cell23_7063286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_7063286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063286 prefixEnd_7063286 := by exact prefixLift 7063286
  have htrace : WordTrace (prefixWord ++ tailWord_7063286) baseStart_7063286 baseEnd_7063286 := by
    simpa [prefixWord, tailWord_7063286, baseEnd_7063286] using wordTrace_append hprefix tailTrace_7063286
  have hstable : (prefixWord ++ tailWord_7063286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063286).length < 2 ^ (prefixWord ++ tailWord_7063286).sum := by decide
  have hdescent : baseEnd_7063286 < baseStart_7063286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063433 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 5, 2, 2]
def baseStart_7063433 : Nat := 118140960795 + 7063433 * 2 ^ 59
def prefixEnd_7063433 : Nat := 4983230072969 + 3 ^ 40 * 7063433 * 2
def baseEnd_7063433 : Nat := 3626936199829368019603369

theorem tailTrace_7063433 : CollatzResearch.WordTrace tailWord_7063433 prefixEnd_7063433 3626936199829368019603369 := by
  unfold tailWord_7063433
  simp only [CollatzResearch.WordTrace]
  refine ⟨257624566219396054160010953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171749710812930702773340635 257624566219396054160010953)
  ·
    refine ⟨193218424664547040620008215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257624566219396054160010953 193218424664547040620008215)
    ·
      refine ⟨289827636996820560930012323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193218424664547040620008215 289827636996820560930012323)
      ·
        refine ⟨434741455495230841395018485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289827636996820560930012323 434741455495230841395018485)
        ·
          refine ⟨40757011452677891380782983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 434741455495230841395018485 40757011452677891380782983)
          ·
            refine ⟨61135517179016837071174475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40757011452677891380782983 61135517179016837071174475)
            ·
              refine ⟨91703275768525255606761713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61135517179016837071174475 91703275768525255606761713)
              ·
                refine ⟨68777456826393941705071285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91703275768525255606761713 68777456826393941705071285)
                ·
                  refine ⟨6447886577474432034850433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68777456826393941705071285 6447886577474432034850433)
                  ·
                    refine ⟨4835914933105824026137825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6447886577474432034850433 4835914933105824026137825)
                    ·
                      refine ⟨3626936199829368019603369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835914933105824026137825 3626936199829368019603369)
                      ·
                        rfl

theorem cell23_7063433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 2, 2].length) (baseStart_7063433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063433 prefixEnd_7063433 := by exact prefixLift 7063433
  have htrace : WordTrace (prefixWord ++ tailWord_7063433) baseStart_7063433 baseEnd_7063433 := by
    simpa [prefixWord, tailWord_7063433, baseEnd_7063433] using wordTrace_append hprefix tailTrace_7063433
  have hstable : (prefixWord ++ tailWord_7063433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063433).length < 2 ^ (prefixWord ++ tailWord_7063433).sum := by decide
  have hdescent : baseEnd_7063433 < baseStart_7063433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063450 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2]
def baseStart_7063450 : Nat := 118140960795 + 7063450 * 2 ^ 59
def prefixEnd_7063450 : Nat := 4983230072969 + 3 ^ 40 * 7063450 * 2
def baseEnd_7063450 : Nat := 3626944929000494453090791

theorem tailTrace_7063450 : CollatzResearch.WordTrace tailWord_7063450 prefixEnd_7063450 3626944929000494453090791 := by
  unfold tailWord_7063450
  simp only [CollatzResearch.WordTrace]
  refine ⟨64406296565083616515844951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171750124173556310708919869 64406296565083616515844951)
  ·
    refine ⟨96609444847625424773767427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64406296565083616515844951 96609444847625424773767427)
    ·
      refine ⟨144914167271438137160651141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96609444847625424773767427 144914167271438137160651141)
      ·
        refine ⟨27171406363394650717622089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144914167271438137160651141 27171406363394650717622089)
        ·
          refine ⟨20378554772545988038216567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27171406363394650717622089 20378554772545988038216567)
          ·
            refine ⟨30567832158818982057324851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20378554772545988038216567 30567832158818982057324851)
            ·
              refine ⟨45851748238228473085987277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30567832158818982057324851 45851748238228473085987277)
              ·
                refine ⟨17194405589335677407245229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45851748238228473085987277 17194405589335677407245229)
                ·
                  refine ⟨6447902096000879027716961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17194405589335677407245229 6447902096000879027716961)
                  ·
                    refine ⟨4835926572000659270787721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6447902096000879027716961 4835926572000659270787721)
                    ·
                      refine ⟨3626944929000494453090791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835926572000659270787721 3626944929000494453090791)
                      ·
                        rfl

theorem cell23_7063450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_7063450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063450 prefixEnd_7063450 := by exact prefixLift 7063450
  have htrace : WordTrace (prefixWord ++ tailWord_7063450) baseStart_7063450 baseEnd_7063450 := by
    simpa [prefixWord, tailWord_7063450, baseEnd_7063450] using wordTrace_append hprefix tailTrace_7063450
  have hstable : (prefixWord ++ tailWord_7063450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063450).length < 2 ^ (prefixWord ++ tailWord_7063450).sum := by decide
  have hdescent : baseEnd_7063450 < baseStart_7063450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063460 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_7063460 : Nat := 118140960795 + 7063460 * 2 ^ 59
def prefixEnd_7063460 : Nat := 4983230072969 + 3 ^ 40 * 7063460 * 2
def baseEnd_7063460 : Nat := 1208983354602346471321915

theorem tailTrace_7063460 : CollatzResearch.WordTrace tailWord_7063460 prefixEnd_7063460 1208983354602346471321915 := by
  unfold tailWord_7063460
  simp only [CollatzResearch.WordTrace]
  refine ⟨128812775495149118885621917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171750367326865491847495889 128812775495149118885621917)
  ·
    refine ⟨48304790810680919582108219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128812775495149118885621917 48304790810680919582108219)
    ·
      refine ⟨72457186216021379373162329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48304790810680919582108219 72457186216021379373162329)
      ·
        refine ⟨54342889662016034529871747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72457186216021379373162329 54342889662016034529871747)
        ·
          refine ⟨81514334493024051794807621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54342889662016034529871747 81514334493024051794807621)
          ·
            refine ⟨15283937717442009711526429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81514334493024051794807621 15283937717442009711526429)
            ·
              refine ⟨5731476644040753641822411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15283937717442009711526429 5731476644040753641822411)
              ·
                refine ⟨8597214966061130462733617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731476644040753641822411 8597214966061130462733617)
                ·
                  refine ⟨6447911224545847847050213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8597214966061130462733617 6447911224545847847050213)
                  ·
                    refine ⟨1208983354602346471321915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447911224545847847050213 1208983354602346471321915)
                    ·
                      rfl

theorem cell23_7063460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_7063460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063460 prefixEnd_7063460 := by exact prefixLift 7063460
  have htrace : WordTrace (prefixWord ++ tailWord_7063460) baseStart_7063460 baseEnd_7063460 := by
    simpa [prefixWord, tailWord_7063460, baseEnd_7063460] using wordTrace_append hprefix tailTrace_7063460
  have hstable : (prefixWord ++ tailWord_7063460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063460).length < 2 ^ (prefixWord ++ tailWord_7063460).sum := by decide
  have hdescent : baseEnd_7063460 < baseStart_7063460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063463 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_7063463 : Nat := 118140960795 + 7063463 * 2 ^ 59
def prefixEnd_7063463 : Nat := 4983230072969 + 3 ^ 40 * 7063463 * 2
def baseEnd_7063463 : Nat := 3626951604249002902228231

theorem tailTrace_7063463 : CollatzResearch.WordTrace tailWord_7063463 prefixEnd_7063463 3626951604249002902228231 := by
  unfold tailWord_7063463
  simp only [CollatzResearch.WordTrace]
  refine ⟨257625660409287369283603043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171750440272858246189068695 257625660409287369283603043)
  ·
    refine ⟨386438490613931053925404565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257625660409287369283603043 386438490613931053925404565)
    ·
      refine ⟨18114304247528018152753339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 386438490613931053925404565 18114304247528018152753339)
      ·
        refine ⟨27171456371292027229130009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18114304247528018152753339 27171456371292027229130009)
        ·
          refine ⟨20378592278469020421847507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27171456371292027229130009 20378592278469020421847507)
          ·
            refine ⟨30567888417703530632771261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20378592278469020421847507 30567888417703530632771261)
            ·
              refine ⟨11462958156638823987289223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30567888417703530632771261 11462958156638823987289223)
              ·
                refine ⟨17194437234958235980933835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462958156638823987289223 17194437234958235980933835)
                ·
                  refine ⟨25791655852437353971400753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17194437234958235980933835 25791655852437353971400753)
                  ·
                    refine ⟨19343741889328015478550565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25791655852437353971400753 19343741889328015478550565)
                    ·
                      refine ⟨3626951604249002902228231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19343741889328015478550565 3626951604249002902228231)
                      ·
                        rfl

theorem cell23_7063463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_7063463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063463 prefixEnd_7063463 := by exact prefixLift 7063463
  have htrace : WordTrace (prefixWord ++ tailWord_7063463) baseStart_7063463 baseEnd_7063463 := by
    simpa [prefixWord, tailWord_7063463, baseEnd_7063463] using wordTrace_append hprefix tailTrace_7063463
  have hstable : (prefixWord ++ tailWord_7063463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063463).length < 2 ^ (prefixWord ++ tailWord_7063463).sum := by decide
  have hdescent : baseEnd_7063463 < baseStart_7063463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063473 : List Nat := [1, 2, 2, 4, 2, 3, 2, 7]
def baseStart_7063473 : Nat := 118140960795 + 7063473 * 2 ^ 59
def prefixEnd_7063473 : Nat := 4983230072969 + 3 ^ 40 * 7063473 * 2
def baseEnd_7063473 : Nat := 134331731076131402337155

theorem tailTrace_7063473 : CollatzResearch.WordTrace tailWord_7063473 prefixEnd_7063473 134331731076131402337155 := by
  unfold tailWord_7063473
  simp only [CollatzResearch.WordTrace]
  refine ⟨257626025139251140991467073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171750683426167427327644715 257626025139251140991467073)
  ·
    refine ⟨193219518854438355743600305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257626025139251140991467073 193219518854438355743600305)
    ·
      refine ⟨144914639140828766807700229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193219518854438355743600305 144914639140828766807700229)
      ·
        refine ⟨27171494838905393776443793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144914639140828766807700229 27171494838905393776443793)
        ·
          refine ⟨20378621129179045332332845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27171494838905393776443793 20378621129179045332332845)
          ·
            refine ⟨7641982923442141999624817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20378621129179045332332845 7641982923442141999624817)
            ·
              refine ⟨5731487192581606499718613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7641982923442141999624817 5731487192581606499718613)
              ·
                refine ⟨134331731076131402337155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5731487192581606499718613 134331731076131402337155)
                ·
                  rfl

theorem cell23_7063473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 7].length) (baseStart_7063473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063473 prefixEnd_7063473 := by exact prefixLift 7063473
  have htrace : WordTrace (prefixWord ++ tailWord_7063473) baseStart_7063473 baseEnd_7063473 := by
    simpa [prefixWord, tailWord_7063473, baseEnd_7063473] using wordTrace_append hprefix tailTrace_7063473
  have hstable : (prefixWord ++ tailWord_7063473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063473).length < 2 ^ (prefixWord ++ tailWord_7063473).sum := by decide
  have hdescent : baseEnd_7063473 < baseStart_7063473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063517 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_7063517 : Nat := 118140960795 + 7063517 * 2 ^ 59
def prefixEnd_7063517 : Nat := 4983230072969 + 3 ^ 40 * 7063517 * 2
def baseEnd_7063517 : Nat := 3626979332204345690952983

theorem tailTrace_7063517 : CollatzResearch.WordTrace tailWord_7063517 prefixEnd_7063517 3626979332204345690952983 := by
  unfold tailWord_7063517
  simp only [CollatzResearch.WordTrace]
  refine ⟨257627629951091736506068805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171751753300727824337379203 257627629951091736506068805)
  ·
    refine ⟨48305180615829700594887901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257627629951091736506068805 48305180615829700594887901)
    ·
      refine ⟨18114442730936137723082963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48305180615829700594887901 18114442730936137723082963)
      ·
        refine ⟨27171664096404206584624445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18114442730936137723082963 27171664096404206584624445)
        ·
          refine ⟨10189374036151577469234167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27171664096404206584624445 10189374036151577469234167)
          ·
            refine ⟨15284061054227366203851251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189374036151577469234167 15284061054227366203851251)
            ·
              refine ⟨22926091581341049305776877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15284061054227366203851251 22926091581341049305776877)
              ·
                refine ⟨8597284343002893489666329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22926091581341049305776877 8597284343002893489666329)
                ·
                  refine ⟨6447963257252170117249747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8597284343002893489666329 6447963257252170117249747)
                  ·
                    refine ⟨9671944885878255175874621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6447963257252170117249747 9671944885878255175874621)
                    ·
                      refine ⟨3626979332204345690952983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9671944885878255175874621 3626979332204345690952983)
                      ·
                        rfl

theorem cell23_7063517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_7063517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063517 prefixEnd_7063517 := by exact prefixLift 7063517
  have htrace : WordTrace (prefixWord ++ tailWord_7063517) baseStart_7063517 baseEnd_7063517 := by
    simpa [prefixWord, tailWord_7063517, baseEnd_7063517] using wordTrace_append hprefix tailTrace_7063517
  have hstable : (prefixWord ++ tailWord_7063517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063517).length < 2 ^ (prefixWord ++ tailWord_7063517).sum := by decide
  have hdescent : baseEnd_7063517 < baseStart_7063517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063557 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 2, 2, 2]
def baseStart_7063557 : Nat := 118140960795 + 7063557 * 2 ^ 59
def prefixEnd_7063557 : Nat := 4983230072969 + 3 ^ 40 * 7063557 * 2
def baseEnd_7063557 : Nat := 3626999871430525534452799

theorem tailTrace_7063557 : CollatzResearch.WordTrace tailWord_7063557 prefixEnd_7063557 3626999871430525534452799 := by
  unfold tailWord_7063557
  simp only [CollatzResearch.WordTrace]
  refine ⟨257629088870946823337524925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171752725913964548891683283 257629088870946823337524925)
  ·
    refine ⟨96610908326605058751571847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257629088870946823337524925 96610908326605058751571847)
    ·
      refine ⟨144916362489907588127357771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96610908326605058751571847 144916362489907588127357771)
      ·
        refine ⟨217374543734861382191036657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144916362489907588127357771 217374543734861382191036657)
        ·
          refine ⟨163030907801146036643277493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217374543734861382191036657 163030907801146036643277493)
          ·
            refine ⟨15284147606357440935307265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163030907801146036643277493 15284147606357440935307265)
            ·
              refine ⟨11463110704768080701480449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15284147606357440935307265 11463110704768080701480449)
              ·
                refine ⟨8597333028576060526110337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11463110704768080701480449 8597333028576060526110337)
                ·
                  refine ⟨6447999771432045394582753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8597333028576060526110337 6447999771432045394582753)
                  ·
                    refine ⟨4835999828574034045937065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6447999771432045394582753 4835999828574034045937065)
                    ·
                      refine ⟨3626999871430525534452799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835999828574034045937065 3626999871430525534452799)
                      ·
                        rfl

theorem cell23_7063557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_7063557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063557 prefixEnd_7063557 := by exact prefixLift 7063557
  have htrace : WordTrace (prefixWord ++ tailWord_7063557) baseStart_7063557 baseEnd_7063557 := by
    simpa [prefixWord, tailWord_7063557, baseEnd_7063557] using wordTrace_append hprefix tailTrace_7063557
  have hstable : (prefixWord ++ tailWord_7063557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063557).length < 2 ^ (prefixWord ++ tailWord_7063557).sum := by decide
  have hdescent : baseEnd_7063557 < baseStart_7063557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063563 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 5]
def baseStart_7063563 : Nat := 118140960795 + 7063563 * 2 ^ 59
def prefixEnd_7063563 : Nat := 4983230072969 + 3 ^ 40 * 7063563 * 2
def baseEnd_7063563 : Nat := 403000328034939167886419

theorem tailTrace_7063563 : CollatzResearch.WordTrace tailWord_7063563 prefixEnd_7063563 403000328034939167886419 := by
  unfold tailWord_7063563
  simp only [CollatzResearch.WordTrace]
  refine ⟨257629307708925086362243343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171752871805950057574828895 257629307708925086362243343)
  ·
    refine ⟨386443961563387629543365015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257629307708925086362243343 386443961563387629543365015)
    ·
      refine ⟨579665942345081444315047523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386443961563387629543365015 579665942345081444315047523)
      ·
        refine ⟨869498913517622166472571285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579665942345081444315047523 869498913517622166472571285)
        ·
          refine ⟨40757761571138539053401779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 869498913517622166472571285 40757761571138539053401779)
          ·
            refine ⟨61136642356707808580102669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40757761571138539053401779 61136642356707808580102669)
            ·
              refine ⟨22926240883765428217538501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61136642356707808580102669 22926240883765428217538501)
              ·
                refine ⟨4298670165706017790788469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22926240883765428217538501 4298670165706017790788469)
                ·
                  refine ⟨403000328034939167886419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4298670165706017790788469 403000328034939167886419)
                  ·
                    rfl

theorem cell23_7063563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 5].length) (baseStart_7063563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063563 prefixEnd_7063563 := by exact prefixLift 7063563
  have htrace : WordTrace (prefixWord ++ tailWord_7063563) baseStart_7063563 baseEnd_7063563 := by
    simpa [prefixWord, tailWord_7063563, baseEnd_7063563] using wordTrace_append hprefix tailTrace_7063563
  have hstable : (prefixWord ++ tailWord_7063563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063563).length < 2 ^ (prefixWord ++ tailWord_7063563).sum := by decide
  have hdescent : baseEnd_7063563 < baseStart_7063563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063576 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_7063576 : Nat := 118140960795 + 7063576 * 2 ^ 59
def prefixEnd_7063576 : Nat := 4983230072969 + 3 ^ 40 * 7063576 * 2
def baseEnd_7063576 : Nat := 1209003209187653653371737

theorem tailTrace_7063576 : CollatzResearch.WordTrace tailWord_7063576 prefixEnd_7063576 1209003209187653653371737 := by
  unfold tailWord_7063576
  simp only [CollatzResearch.WordTrace]
  refine ⟨128814890928938994791233291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171753187905251993054977721 128814890928938994791233291)
  ·
    refine ⟨193222336393408492186849937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128814890928938994791233291 193222336393408492186849937)
    ·
      refine ⟨144916752295056369140137453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193222336393408492186849937 144916752295056369140137453)
      ·
        refine ⟨54343782110646138427551545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144916752295056369140137453 54343782110646138427551545)
        ·
          refine ⟨40757836582984603820663659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54343782110646138427551545 40757836582984603820663659)
          ·
            refine ⟨61136754874476905730995489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40757836582984603820663659 61136754874476905730995489)
            ·
              refine ⟨45852566155857679298246617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61136754874476905730995489 45852566155857679298246617)
              ·
                refine ⟨34389424616893259473684963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45852566155857679298246617 34389424616893259473684963)
                ·
                  refine ⟨51584136925339889210527445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34389424616893259473684963 51584136925339889210527445)
                  ·
                    refine ⟨1209003209187653653371737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51584136925339889210527445 1209003209187653653371737)
                    ·
                      rfl

theorem cell23_7063576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_7063576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063576 prefixEnd_7063576 := by exact prefixLift 7063576
  have htrace : WordTrace (prefixWord ++ tailWord_7063576) baseStart_7063576 baseEnd_7063576 := by
    simpa [prefixWord, tailWord_7063576, baseEnd_7063576] using wordTrace_append hprefix tailTrace_7063576
  have hstable : (prefixWord ++ tailWord_7063576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063576).length < 2 ^ (prefixWord ++ tailWord_7063576).sum := by decide
  have hdescent : baseEnd_7063576 < baseStart_7063576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063583 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 2, 5, 2]
def baseStart_7063583 : Nat := 118140960795 + 7063583 * 2 ^ 59
def prefixEnd_7063583 : Nat := 4983230072969 + 3 ^ 40 * 7063583 * 2
def baseEnd_7063583 : Nat := 3627013221927542432727679

theorem tailTrace_7063583 : CollatzResearch.WordTrace tailWord_7063583 prefixEnd_7063583 3627013221927542432727679 := by
  unfold tailWord_7063583
  simp only [CollatzResearch.WordTrace]
  refine ⟨257630037168852629777971403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171753358112568419851980935 257630037168852629777971403)
  ·
    refine ⟨386445055753278944666957105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257630037168852629777971403 386445055753278944666957105)
    ·
      refine ⟨289833791814959208500217829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386445055753278944666957105 289833791814959208500217829)
      ·
        refine ⟨54343835965304851593790843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289833791814959208500217829 54343835965304851593790843)
        ·
          refine ⟨81515753947957277390686265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54343835965304851593790843 81515753947957277390686265)
          ·
            refine ⟨61136815460967958043014699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81515753947957277390686265 61136815460967958043014699)
            ·
              refine ⟨91705223191451937064522049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61136815460967958043014699 91705223191451937064522049)
              ·
                refine ⟨68778917393588952798391537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91705223191451937064522049 68778917393588952798391537)
                ·
                  refine ⟨51584188045191714598793653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68778917393588952798391537 51584188045191714598793653)
                  ·
                    refine ⟨4836017629236723243636905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51584188045191714598793653 4836017629236723243636905)
                    ·
                      refine ⟨3627013221927542432727679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836017629236723243636905 3627013221927542432727679)
                      ·
                        rfl

theorem cell23_7063583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_7063583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063583 prefixEnd_7063583 := by exact prefixLift 7063583
  have htrace : WordTrace (prefixWord ++ tailWord_7063583) baseStart_7063583 baseEnd_7063583 := by
    simpa [prefixWord, tailWord_7063583, baseEnd_7063583] using wordTrace_append hprefix tailTrace_7063583
  have hstable : (prefixWord ++ tailWord_7063583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063583).length < 2 ^ (prefixWord ++ tailWord_7063583).sum := by decide
  have hdescent : baseEnd_7063583 < baseStart_7063583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063613 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7063613 : Nat := 118140960795 + 7063613 * 2 ^ 59
def prefixEnd_7063613 : Nat := 4983230072969 + 3 ^ 40 * 7063613 * 2
def baseEnd_7063613 : Nat := 3627028626347177315352541

theorem tailTrace_7063613 : CollatzResearch.WordTrace tailWord_7063613 prefixEnd_7063613 3627028626347177315352541 := by
  unfold tailWord_7063613
  simp only [CollatzResearch.WordTrace]
  refine ⟨257631131358743944901563493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171754087572495963267708995 257631131358743944901563493)
  ·
    refine ⟨48305837129764489669043155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257631131358743944901563493 48305837129764489669043155)
    ·
      refine ⟨72458755694646734503564733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48305837129764489669043155 72458755694646734503564733)
      ·
        refine ⟨27172033385492525438836775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72458755694646734503564733 27172033385492525438836775)
        ·
          refine ⟨40758050078238788158255163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27172033385492525438836775 40758050078238788158255163)
          ·
            refine ⟨61137075117358182237382745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40758050078238788158255163 61137075117358182237382745)
            ·
              refine ⟨45852806338018636678037059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61137075117358182237382745 45852806338018636678037059)
              ·
                refine ⟨68779209507027955017055589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45852806338018636678037059 68779209507027955017055589)
                ·
                  refine ⟨12896101782567741565697923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68779209507027955017055589 12896101782567741565697923)
                  ·
                    refine ⟨19344152673851612348546885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12896101782567741565697923 19344152673851612348546885)
                    ·
                      refine ⟨3627028626347177315352541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19344152673851612348546885 3627028626347177315352541)
                      ·
                        rfl

theorem cell23_7063613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7063613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063613 prefixEnd_7063613 := by exact prefixLift 7063613
  have htrace : WordTrace (prefixWord ++ tailWord_7063613) baseStart_7063613 baseEnd_7063613 := by
    simpa [prefixWord, tailWord_7063613, baseEnd_7063613] using wordTrace_append hprefix tailTrace_7063613
  have hstable : (prefixWord ++ tailWord_7063613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063613).length < 2 ^ (prefixWord ++ tailWord_7063613).sum := by decide
  have hdescent : baseEnd_7063613 < baseStart_7063613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063626 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_7063626 : Nat := 118140960795 + 7063626 * 2 ^ 59
def prefixEnd_7063626 : Nat := 4983230072969 + 3 ^ 40 * 7063626 * 2
def baseEnd_7063626 : Nat := 3627035301595685764489981

theorem tailTrace_7063626 : CollatzResearch.WordTrace tailWord_7063626 prefixEnd_7063626 3627035301595685764489981 := by
  unfold tailWord_7063626
  simp only [CollatzResearch.WordTrace]
  refine ⟨64407901376924212030446683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171754403671797898747857821 64407901376924212030446683)
  ·
    refine ⟨96611852065386318045670025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64407901376924212030446683 96611852065386318045670025)
    ·
      refine ⟨72458889049039738534252519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96611852065386318045670025 72458889049039738534252519)
      ·
        refine ⟨108688333573559607801378779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72458889049039738534252519 108688333573559607801378779)
        ·
          refine ⟨163032500360339411702068169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108688333573559607801378779 163032500360339411702068169)
          ·
            refine ⟨122274375270254558776551127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163032500360339411702068169 122274375270254558776551127)
            ·
              refine ⟨183411562905381838164826691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122274375270254558776551127 183411562905381838164826691)
              ·
                refine ⟨275117344358072757247240037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183411562905381838164826691 275117344358072757247240037)
                ·
                  refine ⟨51584502067138641983857507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275117344358072757247240037 51584502067138641983857507)
                  ·
                    refine ⟨77376753100707962975786261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51584502067138641983857507 77376753100707962975786261)
                    ·
                      refine ⟨3627035301595685764489981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77376753100707962975786261 3627035301595685764489981)
                      ·
                        rfl

theorem cell23_7063626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_7063626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063626 prefixEnd_7063626 := by exact prefixLift 7063626
  have htrace : WordTrace (prefixWord ++ tailWord_7063626) baseStart_7063626 baseEnd_7063626 := by
    simpa [prefixWord, tailWord_7063626, baseEnd_7063626] using wordTrace_append hprefix tailTrace_7063626
  have hstable : (prefixWord ++ tailWord_7063626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063626).length < 2 ^ (prefixWord ++ tailWord_7063626).sum := by decide
  have hdescent : baseEnd_7063626 < baseStart_7063626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063630 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_7063630 : Nat := 118140960795 + 7063630 * 2 ^ 59
def prefixEnd_7063630 : Nat := 4983230072969 + 3 ^ 40 * 7063630 * 2
def baseEnd_7063630 : Nat := 3627037355518303748839963

theorem tailTrace_7063630 : CollatzResearch.WordTrace tailWord_7063630 prefixEnd_7063630 3627037355518303748839963 := by
  unfold tailWord_7063630
  simp only [CollatzResearch.WordTrace]
  refine ⟨32203968924960294600616543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171754500933121571203288229 32203968924960294600616543)
  ·
    refine ⟨48305953387440441900924815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32203968924960294600616543 48305953387440441900924815)
    ·
      refine ⟨72458930081160662851387223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48305953387440441900924815 72458930081160662851387223)
      ·
        refine ⟨108688395121740994277080835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72458930081160662851387223 108688395121740994277080835)
        ·
          refine ⟨163032592682611491415621253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108688395121740994277080835 163032592682611491415621253)
          ·
            refine ⟨30568611127989654640428985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163032592682611491415621253 30568611127989654640428985)
            ·
              refine ⟨22926458345992240980321739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30568611127989654640428985 22926458345992240980321739)
              ·
                refine ⟨34389687518988361470482609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22926458345992240980321739 34389687518988361470482609)
                ·
                  refine ⟨25792265639241271102861957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34389687518988361470482609 25792265639241271102861957)
                  ·
                    refine ⟨4836049807357738331786617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25792265639241271102861957 4836049807357738331786617)
                    ·
                      refine ⟨3627037355518303748839963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836049807357738331786617 3627037355518303748839963)
                      ·
                        rfl

theorem cell23_7063630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_7063630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063630 prefixEnd_7063630 := by exact prefixLift 7063630
  have htrace : WordTrace (prefixWord ++ tailWord_7063630) baseStart_7063630 baseEnd_7063630 := by
    simpa [prefixWord, tailWord_7063630, baseEnd_7063630] using wordTrace_append hprefix tailTrace_7063630
  have hstable : (prefixWord ++ tailWord_7063630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063630).length < 2 ^ (prefixWord ++ tailWord_7063630).sum := by decide
  have hdescent : baseEnd_7063630 < baseStart_7063630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063713 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_7063713 : Nat := 118140960795 + 7063713 * 2 ^ 59
def prefixEnd_7063713 : Nat := 4983230072969 + 3 ^ 40 * 7063713 * 2
def baseEnd_7063713 : Nat := 1209026658137542308034027

theorem tailTrace_7063713 : CollatzResearch.WordTrace tailWord_7063713 prefixEnd_7063713 1209026658137542308034027 := by
  unfold tailWord_7063713
  simp only [CollatzResearch.WordTrace]
  refine ⟨257634778658381661980203793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171756519105587774653469195 257634778658381661980203793)
  ·
    refine ⟨193226083993786246485152845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257634778658381661980203793 193226083993786246485152845)
    ·
      refine ⟨72459781497669842431932317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193226083993786246485152845 72459781497669842431932317)
      ·
        refine ⟨27172418061626190911974619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72459781497669842431932317 27172418061626190911974619)
        ·
          refine ⟨40758627092439286367961929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27172418061626190911974619 40758627092439286367961929)
          ·
            refine ⟨30568970319329464775971447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40758627092439286367961929 30568970319329464775971447)
            ·
              refine ⟨45853455478994197163957171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30568970319329464775971447 45853455478994197163957171)
              ·
                refine ⟨68780183218491295745935757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45853455478994197163957171 68780183218491295745935757)
                ·
                  refine ⟨25792568706934235904725909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68780183218491295745935757 25792568706934235904725909)
                  ·
                    refine ⟨1209026658137542308034027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25792568706934235904725909 1209026658137542308034027)
                    ·
                      rfl

theorem cell23_7063713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_7063713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063713 prefixEnd_7063713 := by exact prefixLift 7063713
  have htrace : WordTrace (prefixWord ++ tailWord_7063713) baseStart_7063713 baseEnd_7063713 := by
    simpa [prefixWord, tailWord_7063713, baseEnd_7063713] using wordTrace_append hprefix tailTrace_7063713
  have hstable : (prefixWord ++ tailWord_7063713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063713).length < 2 ^ (prefixWord ++ tailWord_7063713).sum := by decide
  have hdescent : baseEnd_7063713 < baseStart_7063713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063737 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 3, 2, 2]
def baseStart_7063737 : Nat := 118140960795 + 7063737 * 2 ^ 59
def prefixEnd_7063737 : Nat := 4983230072969 + 3 ^ 40 * 7063737 * 2
def baseEnd_7063737 : Nat := 3627092297948334830201971

theorem tailTrace_7063737 : CollatzResearch.WordTrace tailWord_7063737 prefixEnd_7063737 3627092297948334830201971 := by
  unfold tailWord_7063737
  simp only [CollatzResearch.WordTrace]
  refine ⟨257635654010294714079077465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171757102673529809386051643 257635654010294714079077465)
  ·
    refine ⟨193226740507721035559308099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257635654010294714079077465 193226740507721035559308099)
    ·
      refine ⟨289840110761581553338962149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193226740507721035559308099 289840110761581553338962149)
      ·
        refine ⟨54345020767796541251055403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289840110761581553338962149 54345020767796541251055403)
        ·
          refine ⟨81517531151694811876583105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54345020767796541251055403 81517531151694811876583105)
          ·
            refine ⟨61138148363771108907437329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81517531151694811876583105 61138148363771108907437329)
            ·
              refine ⟨45853611272828331680577997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61138148363771108907437329 45853611272828331680577997)
              ·
                refine ⟨17195104227310624380216749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45853611272828331680577997 17195104227310624380216749)
                ·
                  refine ⟨6448164085241484142581281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17195104227310624380216749 6448164085241484142581281)
                  ·
                    refine ⟨4836123063931113106935961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6448164085241484142581281 4836123063931113106935961)
                    ·
                      refine ⟨3627092297948334830201971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836123063931113106935961 3627092297948334830201971)
                      ·
                        rfl

theorem cell23_7063737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_7063737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063737 prefixEnd_7063737 := by exact prefixLift 7063737
  have htrace : WordTrace (prefixWord ++ tailWord_7063737) baseStart_7063737 baseEnd_7063737 := by
    simpa [prefixWord, tailWord_7063737, baseEnd_7063737] using wordTrace_append hprefix tailTrace_7063737
  have hstable : (prefixWord ++ tailWord_7063737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063737).length < 2 ^ (prefixWord ++ tailWord_7063737).sum := by decide
  have hdescent : baseEnd_7063737 < baseStart_7063737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063770 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_7063770 : Nat := 118140960795 + 7063770 * 2 ^ 59
def prefixEnd_7063770 : Nat := 4983230072969 + 3 ^ 40 * 7063770 * 2
def baseEnd_7063770 : Nat := 3627109242809933201089319

theorem tailTrace_7063770 : CollatzResearch.WordTrace tailWord_7063770 prefixEnd_7063770 3627109242809933201089319 := by
  unfold tailWord_7063770
  simp only [CollatzResearch.WordTrace]
  refine ⟨64409214404793790178757191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171757905079450107143352509 64409214404793790178757191)
  ·
    refine ⟨96613821607190685268135787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64409214404793790178757191 96613821607190685268135787)
    ·
      refine ⟨144920732410786027902203681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96613821607190685268135787 144920732410786027902203681)
      ·
        refine ⟨108690549308089520926652761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144920732410786027902203681 108690549308089520926652761)
        ·
          refine ⟨81517911981067140694989571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108690549308089520926652761 81517911981067140694989571)
          ·
            refine ⟨122276867971600711042484357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81517911981067140694989571 122276867971600711042484357)
            ·
              refine ⟨22926912744675133320465817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122276867971600711042484357 22926912744675133320465817)
              ·
                refine ⟨17195184558506349990349363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22926912744675133320465817 17195184558506349990349363)
                ·
                  refine ⟨25792776837759524985524045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17195184558506349990349363 25792776837759524985524045)
                  ·
                    refine ⟨9672291314159821869571517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25792776837759524985524045 9672291314159821869571517)
                    ·
                      refine ⟨3627109242809933201089319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9672291314159821869571517 3627109242809933201089319)
                      ·
                        rfl

theorem cell23_7063770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_7063770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063770 prefixEnd_7063770 := by exact prefixLift 7063770
  have htrace : WordTrace (prefixWord ++ tailWord_7063770) baseStart_7063770 baseEnd_7063770 := by
    simpa [prefixWord, tailWord_7063770, baseEnd_7063770] using wordTrace_append hprefix tailTrace_7063770
  have hstable : (prefixWord ++ tailWord_7063770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063770).length < 2 ^ (prefixWord ++ tailWord_7063770).sum := by decide
  have hdescent : baseEnd_7063770 < baseStart_7063770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063793 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_7063793 : Nat := 118140960795 + 7063793 * 2 ^ 59
def prefixEnd_7063793 : Nat := 4983230072969 + 3 ^ 40 * 7063793 * 2
def baseEnd_7063793 : Nat := 3627121052864986611101713

theorem tailTrace_7063793 : CollatzResearch.WordTrace tailWord_7063793 prefixEnd_7063793 3627121052864986611101713 := by
  unfold tailWord_7063793
  simp only [CollatzResearch.WordTrace]
  refine ⟨257637696498091835643116033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171758464332061223762077355 257637696498091835643116033)
  ·
    refine ⟨193228272373568876732337025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257637696498091835643116033 193228272373568876732337025)
    ·
      refine ⟨144921204280176657549252769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193228272373568876732337025 144921204280176657549252769)
      ·
        refine ⟨108690903210132493161939577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144921204280176657549252769 108690903210132493161939577)
        ·
          refine ⟨81518177407599369871454683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108690903210132493161939577 81518177407599369871454683)
          ·
            refine ⟨122277266111399054807182025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81518177407599369871454683 122277266111399054807182025)
            ·
              refine ⟨91707949583549291105386519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122277266111399054807182025 91707949583549291105386519)
              ·
                refine ⟨137561924375323936658079779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91707949583549291105386519 137561924375323936658079779)
                ·
                  refine ⟨206342886562985904987119669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137561924375323936658079779 206342886562985904987119669)
                  ·
                    refine ⟨19344645615279928592542469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 206342886562985904987119669 19344645615279928592542469)
                    ·
                      refine ⟨3627121052864986611101713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19344645615279928592542469 3627121052864986611101713)
                      ·
                        rfl

theorem cell23_7063793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_7063793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063793 prefixEnd_7063793 := by exact prefixLift 7063793
  have htrace : WordTrace (prefixWord ++ tailWord_7063793) baseStart_7063793 baseEnd_7063793 := by
    simpa [prefixWord, tailWord_7063793, baseEnd_7063793] using wordTrace_append hprefix tailTrace_7063793
  have hstable : (prefixWord ++ tailWord_7063793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063793).length < 2 ^ (prefixWord ++ tailWord_7063793).sum := by decide
  have hdescent : baseEnd_7063793 < baseStart_7063793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063823 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_7063823 : Nat := 118140960795 + 7063823 * 2 ^ 59
def prefixEnd_7063823 : Nat := 4983230072969 + 3 ^ 40 * 7063823 * 2
def baseEnd_7063823 : Nat := 3627136457284621493726575

theorem tailTrace_7063823 : CollatzResearch.WordTrace tailWord_7063823 prefixEnd_7063823 3627136457284621493726575 := by
  unfold tailWord_7063823
  simp only [CollatzResearch.WordTrace]
  refine ⟨257638790687983150766708123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171759193791988767177805415 257638790687983150766708123)
  ·
    refine ⟨386458186031974726150062185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257638790687983150766708123 386458186031974726150062185)
    ·
      refine ⟨289843639523981044612546639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386458186031974726150062185 289843639523981044612546639)
      ·
        refine ⟨434765459285971566918819959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289843639523981044612546639 434765459285971566918819959)
        ·
          refine ⟨652148188928957350378229939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434765459285971566918819959 652148188928957350378229939)
          ·
            refine ⟨978222283393436025567344909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652148188928957350378229939 978222283393436025567344909)
            ·
              refine ⟨366833356272538509587754341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 978222283393436025567344909 366833356272538509587754341)
              ·
                refine ⟨68781254301100970547703939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366833356272538509587754341 68781254301100970547703939)
                ·
                  refine ⟨103171881451651455821555909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68781254301100970547703939 103171881451651455821555909)
                  ·
                    refine ⟨19344727772184647966541733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103171881451651455821555909 19344727772184647966541733)
                    ·
                      refine ⟨3627136457284621493726575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19344727772184647966541733 3627136457284621493726575)
                      ·
                        rfl

theorem cell23_7063823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_7063823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063823 prefixEnd_7063823 := by exact prefixLift 7063823
  have htrace : WordTrace (prefixWord ++ tailWord_7063823) baseStart_7063823 baseEnd_7063823 := by
    simpa [prefixWord, tailWord_7063823, baseEnd_7063823] using wordTrace_append hprefix tailTrace_7063823
  have hstable : (prefixWord ++ tailWord_7063823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063823).length < 2 ^ (prefixWord ++ tailWord_7063823).sum := by decide
  have hdescent : baseEnd_7063823 < baseStart_7063823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063843 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_7063843 : Nat := 118140960795 + 7063843 * 2 ^ 59
def prefixEnd_7063843 : Nat := 4983230072969 + 3 ^ 40 * 7063843 * 2
def baseEnd_7063843 : Nat := 3627146726897711415476483

theorem tailTrace_7063843 : CollatzResearch.WordTrace tailWord_7063843 prefixEnd_7063843 3627146726897711415476483 := by
  unfold tailWord_7063843
  simp only [CollatzResearch.WordTrace]
  refine ⟨257639520147910694182436183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171759680098607129454957455 257639520147910694182436183)
  ·
    refine ⟨386459280221866041273654275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257639520147910694182436183 386459280221866041273654275)
    ·
      refine ⟨579688920332799061910481413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386459280221866041273654275 579688920332799061910481413)
      ·
        refine ⟨108691672562399824108215265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579688920332799061910481413 108691672562399824108215265)
        ·
          refine ⟨81518754421799868081161449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108691672562399824108215265 81518754421799868081161449)
          ·
            refine ⟨61139065816349901060871087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81518754421799868081161449 61139065816349901060871087)
            ·
              refine ⟨91708598724524851591306631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61139065816349901060871087 91708598724524851591306631)
              ·
                refine ⟨137562898086787277386959947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91708598724524851591306631 137562898086787277386959947)
                ·
                  refine ⟨206344347130180916080439921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137562898086787277386959947 206344347130180916080439921)
                  ·
                    refine ⟨154758260347635687060329941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206344347130180916080439921 154758260347635687060329941)
                    ·
                      refine ⟨3627146726897711415476483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154758260347635687060329941 3627146726897711415476483)
                      ·
                        rfl

theorem cell23_7063843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_7063843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063843 prefixEnd_7063843 := by exact prefixLift 7063843
  have htrace : WordTrace (prefixWord ++ tailWord_7063843) baseStart_7063843 baseEnd_7063843 := by
    simpa [prefixWord, tailWord_7063843, baseEnd_7063843] using wordTrace_append hprefix tailTrace_7063843
  have hstable : (prefixWord ++ tailWord_7063843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063843).length < 2 ^ (prefixWord ++ tailWord_7063843).sum := by decide
  have hdescent : baseEnd_7063843 < baseStart_7063843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063844 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_7063844 : Nat := 118140960795 + 7063844 * 2 ^ 59
def prefixEnd_7063844 : Nat := 4983230072969 + 3 ^ 40 * 7063844 * 2
def baseEnd_7063844 : Nat := 3627147240378365911563979

theorem tailTrace_7063844 : CollatzResearch.WordTrace tailWord_7063844 prefixEnd_7063844 3627147240378365911563979 := by
  unfold tailWord_7063844
  simp only [CollatzResearch.WordTrace]
  refine ⟨128819778310453535676611293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171759704413938047568815057 128819778310453535676611293)
  ·
    refine ⟨48307416866420075878729235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128819778310453535676611293 48307416866420075878729235)
    ·
      refine ⟨72461125299630113818093853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48307416866420075878729235 72461125299630113818093853)
      ·
        refine ⟨27172921987361292681785195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72461125299630113818093853 27172921987361292681785195)
        ·
          refine ⟨40759382981041939022677793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27172921987361292681785195 40759382981041939022677793)
          ·
            refine ⟨30569537235781454267008345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40759382981041939022677793 30569537235781454267008345)
            ·
              refine ⟨22927152926836090700256259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30569537235781454267008345 22927152926836090700256259)
              ·
                refine ⟨34390729390254136050384389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22927152926836090700256259 34390729390254136050384389)
                ·
                  refine ⟨6448261760672650509447073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34390729390254136050384389 6448261760672650509447073)
                  ·
                    refine ⟨4836196320504487882085305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6448261760672650509447073 4836196320504487882085305)
                    ·
                      refine ⟨3627147240378365911563979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836196320504487882085305 3627147240378365911563979)
                      ·
                        rfl

theorem cell23_7063844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_7063844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063844 prefixEnd_7063844 := by exact prefixLift 7063844
  have htrace : WordTrace (prefixWord ++ tailWord_7063844) baseStart_7063844 baseEnd_7063844 := by
    simpa [prefixWord, tailWord_7063844, baseEnd_7063844] using wordTrace_append hprefix tailTrace_7063844
  have hstable : (prefixWord ++ tailWord_7063844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063844).length < 2 ^ (prefixWord ++ tailWord_7063844).sum := by decide
  have hdescent : baseEnd_7063844 < baseStart_7063844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063863 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 3, 7]
def baseStart_7063863 : Nat := 118140960795 + 7063863 * 2 ^ 59
def prefixEnd_7063863 : Nat := 4983230072969 + 3 ^ 40 * 7063863 * 2
def baseEnd_7063863 : Nat := 1209052332170267112408797

theorem tailTrace_7063863 : CollatzResearch.WordTrace tailWord_7063863 prefixEnd_7063863 1209052332170267112408797 := by
  unfold tailWord_7063863
  simp only [CollatzResearch.WordTrace]
  refine ⟨257640249607838237598164243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171760166405225491732109495 257640249607838237598164243)
  ·
    refine ⟨386460374411757356397246365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257640249607838237598164243 386460374411757356397246365)
    ·
      refine ⟨144922640404409008648967387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386460374411757356397246365 144922640404409008648967387)
      ·
        refine ⟨217383960606613512973451081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144922640404409008648967387 217383960606613512973451081)
        ·
          refine ⟨163037970454960134730088311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217383960606613512973451081 163037970454960134730088311)
          ·
            refine ⟨244556955682440202095132467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163037970454960134730088311 244556955682440202095132467)
            ·
              refine ⟨366835433523660303142698701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244556955682440202095132467 366835433523660303142698701)
              ·
                refine ⟨137563287571372613678512013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366835433523660303142698701 137563287571372613678512013)
                ·
                  refine ⟨51586232839264730129442005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137563287571372613678512013 51586232839264730129442005)
                  ·
                    refine ⟨1209052332170267112408797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51586232839264730129442005 1209052332170267112408797)
                    ·
                      rfl

theorem cell23_7063863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_7063863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063863 prefixEnd_7063863 := by exact prefixLift 7063863
  have htrace : WordTrace (prefixWord ++ tailWord_7063863) baseStart_7063863 baseEnd_7063863 := by
    simpa [prefixWord, tailWord_7063863, baseEnd_7063863] using wordTrace_append hprefix tailTrace_7063863
  have hstable : (prefixWord ++ tailWord_7063863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063863).length < 2 ^ (prefixWord ++ tailWord_7063863).sum := by decide
  have hdescent : baseEnd_7063863 < baseStart_7063863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063880 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_7063880 : Nat := 118140960795 + 7063880 * 2 ^ 59
def prefixEnd_7063880 : Nat := 4983230072969 + 3 ^ 40 * 7063880 * 2
def baseEnd_7063880 : Nat := 1209055241893975923571271

theorem tailTrace_7063880 : CollatzResearch.WordTrace tailWord_7063880 prefixEnd_7063880 1209055241893975923571271 := by
  unfold tailWord_7063880
  simp only [CollatzResearch.WordTrace]
  refine ⟨128820434824388324750766547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171760579765851099667688729 128820434824388324750766547)
  ·
    refine ⟨193230652236582487126149821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128820434824388324750766547 193230652236582487126149821)
    ·
      refine ⟨72461494588718432672306183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193230652236582487126149821 72461494588718432672306183)
      ·
        refine ⟨108692241883077649008459275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72461494588718432672306183 108692241883077649008459275)
        ·
          refine ⟨163038362824616473512688913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108692241883077649008459275 163038362824616473512688913)
          ·
            refine ⟨122278772118462355134516685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163038362824616473512688913 122278772118462355134516685)
            ·
              refine ⟨45854539544423383175443757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122278772118462355134516685 45854539544423383175443757)
              ·
                refine ⟨17195452329158768690791409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45854539544423383175443757 17195452329158768690791409)
                ·
                  refine ⟨12896589246869076518093557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17195452329158768690791409 12896589246869076518093557)
                  ·
                    refine ⟨1209055241893975923571271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12896589246869076518093557 1209055241893975923571271)
                    ·
                      rfl

theorem cell23_7063880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_7063880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063880 prefixEnd_7063880 := by exact prefixLift 7063880
  have htrace : WordTrace (prefixWord ++ tailWord_7063880) baseStart_7063880 baseEnd_7063880 := by
    simpa [prefixWord, tailWord_7063880, baseEnd_7063880] using wordTrace_append hprefix tailTrace_7063880
  have hstable : (prefixWord ++ tailWord_7063880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063880).length < 2 ^ (prefixWord ++ tailWord_7063880).sum := by decide
  have hdescent : baseEnd_7063880 < baseStart_7063880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063890 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_7063890 : Nat := 118140960795 + 7063890 * 2 ^ 59
def prefixEnd_7063890 : Nat := 4983230072969 + 3 ^ 40 * 7063890 * 2
def baseEnd_7063890 : Nat := 3627170860488472731588767

theorem tailTrace_7063890 : CollatzResearch.WordTrace tailWord_7063890 prefixEnd_7063890 3627170860488472731588767 := by
  unfold tailWord_7063890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64410308594685105302349281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171760822919160280806264749 64410308594685105302349281)
  ·
    refine ⟨48307731446013828976761961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64410308594685105302349281 48307731446013828976761961)
    ·
      refine ⟨36230798584510371732571471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48307731446013828976761961 36230798584510371732571471)
      ·
        refine ⟨54346197876765557598857207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36230798584510371732571471 54346197876765557598857207)
        ·
          refine ⟨81519296815148336398285811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54346197876765557598857207 81519296815148336398285811)
          ·
            refine ⟨122278945222722504597428717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81519296815148336398285811 122278945222722504597428717)
            ·
              refine ⟨45854604458520939224035769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122278945222722504597428717 45854604458520939224035769)
              ·
                refine ⟨34390953343890704418026827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45854604458520939224035769 34390953343890704418026827)
                ·
                  refine ⟨51586430015836056627040241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34390953343890704418026827 51586430015836056627040241)
                  ·
                    refine ⟨38689822511877042470280181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51586430015836056627040241 38689822511877042470280181)
                    ·
                      refine ⟨3627170860488472731588767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38689822511877042470280181 3627170860488472731588767)
                      ·
                        rfl

theorem cell23_7063890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_7063890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063890 prefixEnd_7063890 := by exact prefixLift 7063890
  have htrace : WordTrace (prefixWord ++ tailWord_7063890) baseStart_7063890 baseEnd_7063890 := by
    simpa [prefixWord, tailWord_7063890, baseEnd_7063890] using wordTrace_append hprefix tailTrace_7063890
  have hstable : (prefixWord ++ tailWord_7063890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063890).length < 2 ^ (prefixWord ++ tailWord_7063890).sum := by decide
  have hdescent : baseEnd_7063890 < baseStart_7063890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7063940 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 8]
def baseStart_7063940 : Nat := 118140960795 + 7063940 * 2 ^ 59
def prefixEnd_7063940 : Nat := 4983230072969 + 3 ^ 40 * 7063940 * 2
def baseEnd_7063940 : Nat := 403021837169021948440393

theorem tailTrace_7063940 : CollatzResearch.WordTrace tailWord_7063940 prefixEnd_7063940 403021837169021948440393 := by
  unfold tailWord_7063940
  simp only [CollatzResearch.WordTrace]
  refine ⟨128821529014279639874358637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171762038685706186499144849 128821529014279639874358637)
  ·
    refine ⟨48308073380354864952884489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128821529014279639874358637 48308073380354864952884489)
    ·
      refine ⟨36231055035266148714663367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48308073380354864952884489 36231055035266148714663367)
      ·
        refine ⟨54346582552899223071995051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36231055035266148714663367 54346582552899223071995051)
        ·
          refine ⟨81519873829348834607992577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54346582552899223071995051 81519873829348834607992577)
          ·
            refine ⟨61139905372011625955994433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81519873829348834607992577 61139905372011625955994433)
            ·
              refine ⟨45854929029008719466995825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61139905372011625955994433 45854929029008719466995825)
              ·
                refine ⟨34391196771756539600246869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45854929029008719466995825 34391196771756539600246869)
                ·
                  refine ⟨403021837169021948440393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34391196771756539600246869 403021837169021948440393)
                  ·
                    rfl

theorem cell23_7063940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_7063940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7063940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7063940 prefixEnd_7063940 := by exact prefixLift 7063940
  have htrace : WordTrace (prefixWord ++ tailWord_7063940) baseStart_7063940 baseEnd_7063940 := by
    simpa [prefixWord, tailWord_7063940, baseEnd_7063940] using wordTrace_append hprefix tailTrace_7063940
  have hstable : (prefixWord ++ tailWord_7063940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7063940).length < 2 ^ (prefixWord ++ tailWord_7063940).sum := by decide
  have hdescent : baseEnd_7063940 < baseStart_7063940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7063940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064000 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_7064000 : Nat := 118140960795 + 7064000 * 2 ^ 59
def prefixEnd_7064000 : Nat := 4983230072969 + 3 ^ 40 * 7064000 * 2
def baseEnd_7064000 : Nat := 1209075781120155767071087

theorem tailTrace_7064000 : CollatzResearch.WordTrace tailWord_7064000 prefixEnd_7064000 1209075781120155767071087 := by
  unfold tailWord_7064000
  simp only [CollatzResearch.WordTrace]
  refine ⟨128822623204170954997950727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171763497605561273330600969 128822623204170954997950727)
  ·
    refine ⟨193233934806256432496926091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128822623204170954997950727 193233934806256432496926091)
    ·
      refine ⟨289850902209384648745389137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193233934806256432496926091 289850902209384648745389137)
      ·
        refine ⟨217388176657038486559041853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289850902209384648745389137 217388176657038486559041853)
        ·
          refine ⟨81520566246389432459640695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217388176657038486559041853 81520566246389432459640695)
          ·
            refine ⟨122280849369584148689461043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81520566246389432459640695 122280849369584148689461043)
            ·
              refine ⟨183421274054376223034191565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122280849369584148689461043 183421274054376223034191565)
              ·
                refine ⟨68782977770391083637821837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183421274054376223034191565 68782977770391083637821837)
                ·
                  refine ⟨25793616663896656364183189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68782977770391083637821837 25793616663896656364183189)
                  ·
                    refine ⟨1209075781120155767071087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25793616663896656364183189 1209075781120155767071087)
                    ·
                      rfl

theorem cell23_7064000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_7064000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064000 prefixEnd_7064000 := by exact prefixLift 7064000
  have htrace : WordTrace (prefixWord ++ tailWord_7064000) baseStart_7064000 baseEnd_7064000 := by
    simpa [prefixWord, tailWord_7064000, baseEnd_7064000] using wordTrace_append hprefix tailTrace_7064000
  have hstable : (prefixWord ++ tailWord_7064000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064000).length < 2 ^ (prefixWord ++ tailWord_7064000).sum := by decide
  have hdescent : baseEnd_7064000 < baseStart_7064000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064054 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7064054 : Nat := 118140960795 + 7064054 * 2 ^ 59
def prefixEnd_7064054 : Nat := 4983230072969 + 3 ^ 40 * 7064054 * 2
def baseEnd_7064054 : Nat := 3627255071315810089938013

theorem tailTrace_7064054 : CollatzResearch.WordTrace tailWord_7064054 prefixEnd_7064054 3627255071315810089938013 := by
  unfold tailWord_7064054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102950996884142326147951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171764810633430851478911477 16102950996884142326147951)
  ·
    refine ⟨24154426495326213489221927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16102950996884142326147951 24154426495326213489221927)
    ·
      refine ⟨36231639742989320233832891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24154426495326213489221927 36231639742989320233832891)
      ·
        refine ⟨54347459614483980350749337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36231639742989320233832891 54347459614483980350749337)
        ·
          refine ⟨40760594710862985263062003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54347459614483980350749337 40760594710862985263062003)
          ·
            refine ⟨61140892066294477894593005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40760594710862985263062003 61140892066294477894593005)
            ·
              refine ⟨22927834524860429210472377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61140892066294477894593005 22927834524860429210472377)
              ·
                refine ⟨17195875893645321907854283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22927834524860429210472377 17195875893645321907854283)
                ·
                  refine ⟨25793813840467982861781425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17195875893645321907854283 25793813840467982861781425)
                  ·
                    refine ⟨19345360380350987146336069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25793813840467982861781425 19345360380350987146336069)
                    ·
                      refine ⟨3627255071315810089938013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19345360380350987146336069 3627255071315810089938013)
                      ·
                        rfl

theorem cell23_7064054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7064054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064054 prefixEnd_7064054 := by exact prefixLift 7064054
  have htrace : WordTrace (prefixWord ++ tailWord_7064054) baseStart_7064054 baseEnd_7064054 := by
    simpa [prefixWord, tailWord_7064054, baseEnd_7064054] using wordTrace_append hprefix tailTrace_7064054
  have hstable : (prefixWord ++ tailWord_7064054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064054).length < 2 ^ (prefixWord ++ tailWord_7064054).sum := by decide
  have hdescent : baseEnd_7064054 < baseStart_7064054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064057 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_7064057 : Nat := 118140960795 + 7064057 * 2 ^ 59
def prefixEnd_7064057 : Nat := 4983230072969 + 3 ^ 40 * 7064057 * 2
def baseEnd_7064057 : Nat := 3627256611757773578200499

theorem tailTrace_7064057 : CollatzResearch.WordTrace tailWord_7064057 prefixEnd_7064057 3627256611757773578200499 := by
  unfold tailWord_7064057
  simp only [CollatzResearch.WordTrace]
  refine ⟨257647325369135408730726425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171764883579423605820484283 257647325369135408730726425)
  ·
    refine ⟨193235494026851556548044819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257647325369135408730726425 193235494026851556548044819)
    ·
      refine ⟨289853241040277334822067229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193235494026851556548044819 289853241040277334822067229)
      ·
        refine ⟨108694965390104000558275211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289853241040277334822067229 108694965390104000558275211)
        ·
          refine ⟨163042448085156000837412817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108694965390104000558275211 163042448085156000837412817)
          ·
            refine ⟨122281836063867000628059613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163042448085156000837412817 122281836063867000628059613)
            ·
              refine ⟨45855688523950125235522355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122281836063867000628059613 45855688523950125235522355)
              ·
                refine ⟨68783532785925187853283533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45855688523950125235522355 68783532785925187853283533)
                ·
                  refine ⟨25793824794721945444981325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68783532785925187853283533 25793824794721945444981325)
                  ·
                    refine ⟨9672684298020729541867997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25793824794721945444981325 9672684298020729541867997)
                    ·
                      refine ⟨3627256611757773578200499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9672684298020729541867997 3627256611757773578200499)
                      ·
                        rfl

theorem cell23_7064057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_7064057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064057 prefixEnd_7064057 := by exact prefixLift 7064057
  have htrace : WordTrace (prefixWord ++ tailWord_7064057) baseStart_7064057 baseEnd_7064057 := by
    simpa [prefixWord, tailWord_7064057, baseEnd_7064057] using wordTrace_append hprefix tailTrace_7064057
  have hstable : (prefixWord ++ tailWord_7064057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064057).length < 2 ^ (prefixWord ++ tailWord_7064057).sum := by decide
  have hdescent : baseEnd_7064057 < baseStart_7064057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064061 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_7064061 : Nat := 118140960795 + 7064061 * 2 ^ 59
def prefixEnd_7064061 : Nat := 4983230072969 + 3 ^ 40 * 7064061 * 2
def baseEnd_7064061 : Nat := 3627258665680391562550481

theorem tailTrace_7064061 : CollatzResearch.WordTrace tailWord_7064061 prefixEnd_7064061 3627258665680391562550481 := by
  unfold tailWord_7064061
  simp only [CollatzResearch.WordTrace]
  refine ⟨257647471261120917413872037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171764980840747278275914691 257647471261120917413872037)
  ·
    refine ⟨48308900861460172015101007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257647471261120917413872037 48308900861460172015101007)
    ·
      refine ⟨72463351292190258022651511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48308900861460172015101007 72463351292190258022651511)
      ·
        refine ⟨108695026938285387033977267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72463351292190258022651511 108695026938285387033977267)
        ·
          refine ⟨163042540407428080550965901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108695026938285387033977267 163042540407428080550965901)
          ·
            refine ⟨61140952652785530206612213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163042540407428080550965901 61140952652785530206612213)
            ·
              refine ⟨5731964311198643456869895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61140952652785530206612213 5731964311198643456869895)
              ·
                refine ⟨8597946466797965185304843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731964311198643456869895 8597946466797965185304843)
                ·
                  refine ⟨12896919700196947777957265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8597946466797965185304843 12896919700196947777957265)
                  ·
                    refine ⟨9672689775147710833467949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12896919700196947777957265 9672689775147710833467949)
                    ·
                      refine ⟨3627258665680391562550481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9672689775147710833467949 3627258665680391562550481)
                      ·
                        rfl

theorem cell23_7064061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_7064061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064061 prefixEnd_7064061 := by exact prefixLift 7064061
  have htrace : WordTrace (prefixWord ++ tailWord_7064061) baseStart_7064061 baseEnd_7064061 := by
    simpa [prefixWord, tailWord_7064061, baseEnd_7064061] using wordTrace_append hprefix tailTrace_7064061
  have hstable : (prefixWord ++ tailWord_7064061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064061).length < 2 ^ (prefixWord ++ tailWord_7064061).sum := by decide
  have hdescent : baseEnd_7064061 < baseStart_7064061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064075 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 1, 2, 2]
def baseStart_7064075 : Nat := 118140960795 + 7064075 * 2 ^ 59
def prefixEnd_7064075 : Nat := 4983230072969 + 3 ^ 40 * 7064075 * 2
def baseEnd_7064075 : Nat := 3627265854409554507775417

theorem tailTrace_7064075 : CollatzResearch.WordTrace tailWord_7064075 prefixEnd_7064075 3627265854409554507775417 := by
  unfold tailWord_7064075
  simp only [CollatzResearch.WordTrace]
  refine ⟨257647981883070197804881679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171765321255380131869921119 257647981883070197804881679)
  ·
    refine ⟨386471972824605296707322519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257647981883070197804881679 386471972824605296707322519)
    ·
      refine ⟨579707959236907945060983779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386471972824605296707322519 579707959236907945060983779)
      ·
        refine ⟨869561938855361917591475669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579707959236907945060983779 869561938855361917591475669)
        ·
          refine ⟨20380357941922544943550211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 869561938855361917591475669 20380357941922544943550211)
          ·
            refine ⟨30570536912883817415325317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20380357941922544943550211 30570536912883817415325317)
            ·
              refine ⟨5731975671165715765373497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30570536912883817415325317 5731975671165715765373497)
              ·
                refine ⟨4298981753374286824030123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5731975671165715765373497 4298981753374286824030123)
                ·
                  refine ⟨6448472630061430236045185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298981753374286824030123 6448472630061430236045185)
                  ·
                    refine ⟨4836354472546072677033889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6448472630061430236045185 4836354472546072677033889)
                    ·
                      refine ⟨3627265854409554507775417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836354472546072677033889 3627265854409554507775417)
                      ·
                        rfl

theorem cell23_7064075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 2, 2].length) (baseStart_7064075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064075 prefixEnd_7064075 := by exact prefixLift 7064075
  have htrace : WordTrace (prefixWord ++ tailWord_7064075) baseStart_7064075 baseEnd_7064075 := by
    simpa [prefixWord, tailWord_7064075, baseEnd_7064075] using wordTrace_append hprefix tailTrace_7064075
  have hstable : (prefixWord ++ tailWord_7064075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064075).length < 2 ^ (prefixWord ++ tailWord_7064075).sum := by decide
  have hdescent : baseEnd_7064075 < baseStart_7064075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064080 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_7064080 : Nat := 118140960795 + 7064080 * 2 ^ 59
def prefixEnd_7064080 : Nat := 4983230072969 + 3 ^ 40 * 7064080 * 2
def baseEnd_7064080 : Nat := 3627268421812826988212893

theorem tailTrace_7064080 : CollatzResearch.WordTrace tailWord_7064080 prefixEnd_7064080 3627268421812826988212893 := by
  unfold tailWord_7064080
  simp only [CollatzResearch.WordTrace]
  refine ⟨128824082124026041829406847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171765442832034722439209129 128824082124026041829406847)
  ·
    refine ⟨193236123186039062744110271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128824082124026041829406847 193236123186039062744110271)
    ·
      refine ⟨289854184779058594116165407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193236123186039062744110271 289854184779058594116165407)
      ·
        refine ⟨434781277168587891174248111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289854184779058594116165407 434781277168587891174248111)
        ·
          refine ⟨652171915752881836761372167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434781277168587891174248111 652171915752881836761372167)
          ·
            refine ⟨978257873629322755142058251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652171915752881836761372167 978257873629322755142058251)
            ·
              refine ⟨1467386810443984132713087377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978257873629322755142058251 1467386810443984132713087377)
              ·
                refine ⟨1100540107832988099534815533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467386810443984132713087377 1100540107832988099534815533)
                ·
                  refine ⟨412702540437370537325555825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100540107832988099534815533 412702540437370537325555825)
                  ·
                    refine ⟨309526905328027902994166869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 412702540437370537325555825 309526905328027902994166869)
                    ·
                      refine ⟨3627268421812826988212893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 309526905328027902994166869 3627268421812826988212893)
                      ·
                        rfl

theorem cell23_7064080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_7064080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064080 prefixEnd_7064080 := by exact prefixLift 7064080
  have htrace : WordTrace (prefixWord ++ tailWord_7064080) baseStart_7064080 baseEnd_7064080 := by
    simpa [prefixWord, tailWord_7064080, baseEnd_7064080] using wordTrace_append hprefix tailTrace_7064080
  have hstable : (prefixWord ++ tailWord_7064080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064080).length < 2 ^ (prefixWord ++ tailWord_7064080).sum := by decide
  have hdescent : baseEnd_7064080 < baseStart_7064080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064097 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7064097 : Nat := 118140960795 + 7064097 * 2 ^ 59
def prefixEnd_7064097 : Nat := 4983230072969 + 3 ^ 40 * 7064097 * 2
def baseEnd_7064097 : Nat := 3627277150983953421700315

theorem tailTrace_7064097 : CollatzResearch.WordTrace tailWord_7064097 prefixEnd_7064097 3627277150983953421700315 := by
  unfold tailWord_7064097
  simp only [CollatzResearch.WordTrace]
  refine ⟨257648784288990495562182545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171765856192660330374788363 257648784288990495562182545)
  ·
    refine ⟨193236588216742871671636909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257648784288990495562182545 193236588216742871671636909)
    ·
      refine ⟨72463720581278576876863841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193236588216742871671636909 72463720581278576876863841)
      ·
        refine ⟨54347790435958932657647881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72463720581278576876863841 54347790435958932657647881)
        ·
          refine ⟨40760842826969199493235911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54347790435958932657647881 40760842826969199493235911)
          ·
            refine ⟨61141264240453799239853867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40760842826969199493235911 61141264240453799239853867)
            ·
              refine ⟨91711896360680698859780801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61141264240453799239853867 91711896360680698859780801)
              ·
                refine ⟨68783922270510524144835601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91711896360680698859780801 68783922270510524144835601)
                ·
                  refine ⟨51587941702882893108626701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68783922270510524144835601 51587941702882893108626701)
                  ·
                    refine ⟨19345478138581084915735013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51587941702882893108626701 19345478138581084915735013)
                    ·
                      refine ⟨3627277150983953421700315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19345478138581084915735013 3627277150983953421700315)
                      ·
                        rfl

theorem cell23_7064097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7064097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064097 prefixEnd_7064097 := by exact prefixLift 7064097
  have htrace : WordTrace (prefixWord ++ tailWord_7064097) baseStart_7064097 baseEnd_7064097 := by
    simpa [prefixWord, tailWord_7064097, baseEnd_7064097] using wordTrace_append hprefix tailTrace_7064097
  have hstable : (prefixWord ++ tailWord_7064097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064097).length < 2 ^ (prefixWord ++ tailWord_7064097).sum := by decide
  have hdescent : baseEnd_7064097 < baseStart_7064097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064109 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7064109 : Nat := 118140960795 + 7064109 * 2 ^ 59
def prefixEnd_7064109 : Nat := 4983230072969 + 3 ^ 40 * 7064109 * 2
def baseEnd_7064109 : Nat := 3627283312751807374750261

theorem tailTrace_7064109 : CollatzResearch.WordTrace tailWord_7064109 prefixEnd_7064109 3627283312751807374750261 := by
  unfold tailWord_7064109
  simp only [CollatzResearch.WordTrace]
  refine ⟨257649221964947021611619381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171766147976631347741079587 257649221964947021611619381)
  ·
    refine ⟨24154614559213783276089317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257649221964947021611619381 24154614559213783276089317)
    ·
      refine ⟨4528990229852584364266747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24154614559213783276089317 4528990229852584364266747)
      ·
        refine ⟨6793485344778876546400121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528990229852584364266747 6793485344778876546400121)
        ·
          refine ⟨5095114008584157409800091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6793485344778876546400121 5095114008584157409800091)
          ·
            refine ⟨7642671012876236114700137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095114008584157409800091 7642671012876236114700137)
            ·
              refine ⟨5732003259657177086025103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7642671012876236114700137 5732003259657177086025103)
              ·
                refine ⟨8598004889485765629037655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732003259657177086025103 8598004889485765629037655)
                ·
                  refine ⟨12897007334228648443556483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598004889485765629037655 12897007334228648443556483)
                  ·
                    refine ⟨19345511001342972665334725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12897007334228648443556483 19345511001342972665334725)
                    ·
                      refine ⟨3627283312751807374750261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19345511001342972665334725 3627283312751807374750261)
                      ·
                        rfl

theorem cell23_7064109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7064109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064109 prefixEnd_7064109 := by exact prefixLift 7064109
  have htrace : WordTrace (prefixWord ++ tailWord_7064109) baseStart_7064109 baseEnd_7064109 := by
    simpa [prefixWord, tailWord_7064109, baseEnd_7064109] using wordTrace_append hprefix tailTrace_7064109
  have hstable : (prefixWord ++ tailWord_7064109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064109).length < 2 ^ (prefixWord ++ tailWord_7064109).sum := by decide
  have hdescent : baseEnd_7064109 < baseStart_7064109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064117 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_7064117 : Nat := 118140960795 + 7064117 * 2 ^ 59
def prefixEnd_7064117 : Nat := 4983230072969 + 3 ^ 40 * 7064117 * 2
def baseEnd_7064117 : Nat := 3627287420597043343450223

theorem tailTrace_7064117 : CollatzResearch.WordTrace tailWord_7064117 prefixEnd_7064117 3627287420597043343450223 := by
  unfold tailWord_7064117
  simp only [CollatzResearch.WordTrace]
  refine ⟨257649513748918038977910605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171766342499278692651940403 257649513748918038977910605)
  ·
    refine ⟨96618567655844264616716477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257649513748918038977910605 96618567655844264616716477)
    ·
      refine ⟨36231962870941599231268679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96618567655844264616716477 36231962870941599231268679)
      ·
        refine ⟨54347944306412398846903019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36231962870941599231268679 54347944306412398846903019)
        ·
          refine ⟨81521916459618598270354529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54347944306412398846903019 81521916459618598270354529)
          ·
            refine ⟨61141437344713948702765897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81521916459618598270354529 61141437344713948702765897)
            ·
              refine ⟨45856078008535461527074423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61141437344713948702765897 45856078008535461527074423)
              ·
                refine ⟨68784117012803192290611635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45856078008535461527074423 68784117012803192290611635)
                ·
                  refine ⟨103176175519204788435917453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68784117012803192290611635 103176175519204788435917453)
                  ·
                    refine ⟨38691065819701795663469045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103176175519204788435917453 38691065819701795663469045)
                    ·
                      refine ⟨3627287420597043343450223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38691065819701795663469045 3627287420597043343450223)
                      ·
                        rfl

theorem cell23_7064117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_7064117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064117 prefixEnd_7064117 := by exact prefixLift 7064117
  have htrace : WordTrace (prefixWord ++ tailWord_7064117) baseStart_7064117 baseEnd_7064117 := by
    simpa [prefixWord, tailWord_7064117, baseEnd_7064117] using wordTrace_append hprefix tailTrace_7064117
  have hstable : (prefixWord ++ tailWord_7064117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064117).length < 2 ^ (prefixWord ++ tailWord_7064117).sum := by decide
  have hdescent : baseEnd_7064117 < baseStart_7064117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064127 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_7064127 : Nat := 118140960795 + 7064127 * 2 ^ 59
def prefixEnd_7064127 : Nat := 4983230072969 + 3 ^ 40 * 7064127 * 2
def baseEnd_7064127 : Nat := 3627292555403588304325177

theorem tailTrace_7064127 : CollatzResearch.WordTrace tailWord_7064127 prefixEnd_7064127 3627292555403588304325177 := by
  unfold tailWord_7064127
  simp only [CollatzResearch.WordTrace]
  refine ⟨257649878478881810685774635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171766585652587873790516423 257649878478881810685774635)
  ·
    refine ⟨386474817718322716028661953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257649878478881810685774635 386474817718322716028661953)
    ·
      refine ⟨289856113288742037021496465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386474817718322716028661953 289856113288742037021496465)
      ·
        refine ⟨217392084966556527766122349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289856113288742037021496465 217392084966556527766122349)
        ·
          refine ⟨81522031862458697912295881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217392084966556527766122349 81522031862458697912295881)
          ·
            refine ⟨61141523896844023434221911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81522031862458697912295881 61141523896844023434221911)
            ·
              refine ⟨91712285845266035151332867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61141523896844023434221911 91712285845266035151332867)
              ·
                refine ⟨137568428767899052726999301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91712285845266035151332867 137568428767899052726999301)
                ·
                  refine ⟨25794080393981072386312369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137568428767899052726999301 25794080393981072386312369)
                  ·
                    refine ⟨19345560295485804289734277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25794080393981072386312369 19345560295485804289734277)
                    ·
                      refine ⟨3627292555403588304325177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19345560295485804289734277 3627292555403588304325177)
                      ·
                        rfl

theorem cell23_7064127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_7064127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064127 prefixEnd_7064127 := by exact prefixLift 7064127
  have htrace : WordTrace (prefixWord ++ tailWord_7064127) baseStart_7064127 baseEnd_7064127 := by
    simpa [prefixWord, tailWord_7064127, baseEnd_7064127] using wordTrace_append hprefix tailTrace_7064127
  have hstable : (prefixWord ++ tailWord_7064127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064127).length < 2 ^ (prefixWord ++ tailWord_7064127).sum := by decide
  have hdescent : baseEnd_7064127 < baseStart_7064127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064148 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_7064148 : Nat := 118140960795 + 7064148 * 2 ^ 59
def prefixEnd_7064148 : Nat := 4983230072969 + 3 ^ 40 * 7064148 * 2
def baseEnd_7064148 : Nat := 3627303338497332722162581

theorem tailTrace_7064148 : CollatzResearch.WordTrace tailWord_7064148 prefixEnd_7064148 3627303338497332722162581 := by
  unfold tailWord_7064148
  simp only [CollatzResearch.WordTrace]
  refine ⟨128825322205902865636144549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171767096274537154181526065 128825322205902865636144549)
  ·
    refine ⟨24154747913606787306777103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128825322205902865636144549 24154747913606787306777103)
    ·
      refine ⟨36232121870410180960165655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24154747913606787306777103 36232121870410180960165655)
      ·
        refine ⟨54348182805615271440248483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36232121870410180960165655 54348182805615271440248483)
        ·
          refine ⟨81522274208422907160372725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54348182805615271440248483 81522274208422907160372725)
          ·
            refine ⟨7642713207039647546284943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81522274208422907160372725 7642713207039647546284943)
            ·
              refine ⟨11464069810559471319427415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7642713207039647546284943 11464069810559471319427415)
              ·
                refine ⟨17196104715839206979141123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11464069810559471319427415 17196104715839206979141123)
                ·
                  refine ⟨25794157073758810468711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17196104715839206979141123 25794157073758810468711685)
                  ·
                    refine ⟨4836404451329776962883441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25794157073758810468711685 4836404451329776962883441)
                    ·
                      refine ⟨3627303338497332722162581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836404451329776962883441 3627303338497332722162581)
                      ·
                        rfl

theorem cell23_7064148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_7064148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064148 prefixEnd_7064148 := by exact prefixLift 7064148
  have htrace : WordTrace (prefixWord ++ tailWord_7064148) baseStart_7064148 baseEnd_7064148 := by
    simpa [prefixWord, tailWord_7064148, baseEnd_7064148] using wordTrace_append hprefix tailTrace_7064148
  have hstable : (prefixWord ++ tailWord_7064148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064148).length < 2 ^ (prefixWord ++ tailWord_7064148).sum := by decide
  have hdescent : baseEnd_7064148 < baseStart_7064148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064187 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4]
def baseStart_7064187 : Nat := 118140960795 + 7064187 * 2 ^ 59
def prefixEnd_7064187 : Nat := 4983230072969 + 3 ^ 40 * 7064187 * 2
def baseEnd_7064187 : Nat := 3627323364242858069574901

theorem tailTrace_7064187 : CollatzResearch.WordTrace tailWord_7064187 prefixEnd_7064187 3627323364242858069574901 := by
  unfold tailWord_7064187
  simp only [CollatzResearch.WordTrace]
  refine ⟨257652066858664440932958815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171768044572442960621972543 257652066858664440932958815)
  ·
    refine ⟨386478100287996661399438223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257652066858664440932958815 386478100287996661399438223)
    ·
      refine ⟨579717150431994992099157335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386478100287996661399438223 579717150431994992099157335)
      ·
        refine ⟨869575725647992488148736003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579717150431994992099157335 869575725647992488148736003)
        ·
          refine ⟨1304363588471988732223104005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869575725647992488148736003 1304363588471988732223104005)
          ·
            refine ⟨244568172838497887291832001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1304363588471988732223104005 244568172838497887291832001)
            ·
              refine ⟨183426129628873415468874001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244568172838497887291832001 183426129628873415468874001)
              ·
                refine ⟨137569597221655061601655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183426129628873415468874001 137569597221655061601655501)
                ·
                  refine ⟨51588598958120648100620813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137569597221655061601655501 51588598958120648100620813)
                  ·
                    refine ⟨19345724609295243037732805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51588598958120648100620813 19345724609295243037732805)
                    ·
                      refine ⟨3627323364242858069574901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19345724609295243037732805 3627323364242858069574901)
                      ·
                        rfl

theorem cell23_7064187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_7064187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064187 prefixEnd_7064187 := by exact prefixLift 7064187
  have htrace : WordTrace (prefixWord ++ tailWord_7064187) baseStart_7064187 baseEnd_7064187 := by
    simpa [prefixWord, tailWord_7064187, baseEnd_7064187] using wordTrace_append hprefix tailTrace_7064187
  have hstable : (prefixWord ++ tailWord_7064187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064187).length < 2 ^ (prefixWord ++ tailWord_7064187).sum := by decide
  have hdescent : baseEnd_7064187 < baseStart_7064187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064218 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_7064218 : Nat := 118140960795 + 7064218 * 2 ^ 59
def prefixEnd_7064218 : Nat := 4983230072969 + 3 ^ 40 * 7064218 * 2
def baseEnd_7064218 : Nat := 1209113094047715816095753

theorem tailTrace_7064218 : CollatzResearch.WordTrace tailWord_7064218 prefixEnd_7064218 1209113094047715816095753 := by
  unfold tailWord_7064218
  simp only [CollatzResearch.WordTrace]
  refine ⟨64413299380388033306834327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171768798347701422151558205 64413299380388033306834327)
  ·
    refine ⟨96619949070582049960251491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64413299380388033306834327 96619949070582049960251491)
    ·
      refine ⟨144929923605873074940377237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96619949070582049960251491 144929923605873074940377237)
      ·
        refine ⟨6793590169025300387830183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144929923605873074940377237 6793590169025300387830183)
        ·
          refine ⟨10190385253537950581745275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793590169025300387830183 10190385253537950581745275)
          ·
            refine ⟨15285577880306925872617913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10190385253537950581745275 15285577880306925872617913)
            ·
              refine ⟨11464183410230194404463435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15285577880306925872617913 11464183410230194404463435)
              ·
                refine ⟨17196275115345291606695153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11464183410230194404463435 17196275115345291606695153)
                ·
                  refine ⟨12897206336508968705021365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17196275115345291606695153 12897206336508968705021365)
                  ·
                    refine ⟨1209113094047715816095753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12897206336508968705021365 1209113094047715816095753)
                    ·
                      rfl

theorem cell23_7064218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_7064218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064218 prefixEnd_7064218 := by exact prefixLift 7064218
  have htrace : WordTrace (prefixWord ++ tailWord_7064218) baseStart_7064218 baseEnd_7064218 := by
    simpa [prefixWord, tailWord_7064218, baseEnd_7064218] using wordTrace_append hprefix tailTrace_7064218
  have hstable : (prefixWord ++ tailWord_7064218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064218).length < 2 ^ (prefixWord ++ tailWord_7064218).sum := by decide
  have hdescent : baseEnd_7064218 < baseStart_7064218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064227 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 8]
def baseStart_7064227 : Nat := 118140960795 + 7064227 * 2 ^ 59
def prefixEnd_7064227 : Nat := 4983230072969 + 3 ^ 40 * 7064227 * 2
def baseEnd_7064227 : Nat := 403038211496559768119413

theorem tailTrace_7064227 : CollatzResearch.WordTrace tailWord_7064227 prefixEnd_7064227 403038211496559768119413 := by
  unfold tailWord_7064227
  simp only [CollatzResearch.WordTrace]
  refine ⟨257653525778519527764414935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171769017185679685176276623 257653525778519527764414935)
  ·
    refine ⟨386480288667779291646622403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257653525778519527764414935 386480288667779291646622403)
    ·
      refine ⟨579720433001668937469933605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386480288667779291646622403 579720433001668937469933605)
      ·
        refine ⟨108697581187812925775612551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579720433001668937469933605 108697581187812925775612551)
        ·
          refine ⟨163046371781719388663418827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108697581187812925775612551 163046371781719388663418827)
          ·
            refine ⟨244569557672579082995128241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163046371781719388663418827 244569557672579082995128241)
            ·
              refine ⟨183427168254434312246346181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244569557672579082995128241 183427168254434312246346181)
              ·
                refine ⟨34392594047706433546189909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183427168254434312246346181 34392594047706433546189909)
                ·
                  refine ⟨403038211496559768119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34392594047706433546189909 403038211496559768119413)
                  ·
                    rfl

theorem cell23_7064227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 8].length) (baseStart_7064227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064227 prefixEnd_7064227 := by exact prefixLift 7064227
  have htrace : WordTrace (prefixWord ++ tailWord_7064227) baseStart_7064227 baseEnd_7064227 := by
    simpa [prefixWord, tailWord_7064227, baseEnd_7064227] using wordTrace_append hprefix tailTrace_7064227
  have hstable : (prefixWord ++ tailWord_7064227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064227).length < 2 ^ (prefixWord ++ tailWord_7064227).sum := by decide
  have hdescent : baseEnd_7064227 < baseStart_7064227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064238 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7064238 : Nat := 118140960795 + 7064238 * 2 ^ 59
def prefixEnd_7064238 : Nat := 4983230072969 + 3 ^ 40 * 7064238 * 2
def baseEnd_7064238 : Nat := 3627349551756237370037167

theorem tailTrace_7064238 : CollatzResearch.WordTrace tailWord_7064238 prefixEnd_7064238 3627349551756237370037167 := by
  unfold tailWord_7064238
  simp only [CollatzResearch.WordTrace]
  refine ⟨32206740872684959580383171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171769284654319784428710245 32206740872684959580383171)
  ·
    refine ⟨48310111309027439370574757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32206740872684959580383171 48310111309027439370574757)
    ·
      refine ⟨9058145870442644881982767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48310111309027439370574757 9058145870442644881982767)
      ·
        refine ⟨13587218805663967322974151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9058145870442644881982767 13587218805663967322974151)
        ·
          refine ⟨20380828208495950984461227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13587218805663967322974151 20380828208495950984461227)
          ·
            refine ⟨30571242312743926476691841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20380828208495950984461227 30571242312743926476691841)
            ·
              refine ⟨22928431734557944857518881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30571242312743926476691841 22928431734557944857518881)
              ·
                refine ⟨17196323800918458643139161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22928431734557944857518881 17196323800918458643139161)
                ·
                  refine ⟨12897242850688843982354371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17196323800918458643139161 12897242850688843982354371)
                  ·
                    refine ⟨19345864276033265973531557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12897242850688843982354371 19345864276033265973531557)
                    ·
                      refine ⟨3627349551756237370037167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19345864276033265973531557 3627349551756237370037167)
                      ·
                        rfl

theorem cell23_7064238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7064238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064238 prefixEnd_7064238 := by exact prefixLift 7064238
  have htrace : WordTrace (prefixWord ++ tailWord_7064238) baseStart_7064238 baseEnd_7064238 := by
    simpa [prefixWord, tailWord_7064238, baseEnd_7064238] using wordTrace_append hprefix tailTrace_7064238
  have hstable : (prefixWord ++ tailWord_7064238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064238).length < 2 ^ (prefixWord ++ tailWord_7064238).sum := by decide
  have hdescent : baseEnd_7064238 < baseStart_7064238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064281 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 1, 5, 2]
def baseStart_7064281 : Nat := 118140960795 + 7064281 * 2 ^ 59
def prefixEnd_7064281 : Nat := 4983230072969 + 3 ^ 40 * 7064281 * 2
def baseEnd_7064281 : Nat := 3627371631424380701799469

theorem tailTrace_7064281 : CollatzResearch.WordTrace tailWord_7064281 prefixEnd_7064281 3627371631424380701799469 := by
  unfold tailWord_7064281
  simp only [CollatzResearch.WordTrace]
  refine ⟨257655495320323894986880697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171770330213549263324587131 257655495320323894986880697)
  ·
    refine ⟨193241621490242921240160523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257655495320323894986880697 193241621490242921240160523)
    ·
      refine ⟨289862432235364381860240785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193241621490242921240160523 289862432235364381860240785)
      ·
        refine ⟨217396824176523286395180589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289862432235364381860240785 217396824176523286395180589)
        ·
          refine ⟨81523809066196232398192721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217396824176523286395180589 81523809066196232398192721)
          ·
            refine ⟨61142856799647174298644541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81523809066196232398192721 61142856799647174298644541)
            ·
              refine ⟨22928571299867690361991703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61142856799647174298644541 22928571299867690361991703)
              ·
                refine ⟨34392856949801535542987555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22928571299867690361991703 34392856949801535542987555)
                ·
                  refine ⟨51589285424702303314481333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34392856949801535542987555 51589285424702303314481333)
                  ·
                    refine ⟨4836495508565840935732625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51589285424702303314481333 4836495508565840935732625)
                    ·
                      refine ⟨3627371631424380701799469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836495508565840935732625 3627371631424380701799469)
                      ·
                        rfl

theorem cell23_7064281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_7064281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064281 prefixEnd_7064281 := by exact prefixLift 7064281
  have htrace : WordTrace (prefixWord ++ tailWord_7064281) baseStart_7064281 baseEnd_7064281 := by
    simpa [prefixWord, tailWord_7064281, baseEnd_7064281] using wordTrace_append hprefix tailTrace_7064281
  have hstable : (prefixWord ++ tailWord_7064281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064281).length < 2 ^ (prefixWord ++ tailWord_7064281).sum := by decide
  have hdescent : baseEnd_7064281 < baseStart_7064281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064314 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_7064314 : Nat := 118140960795 + 7064314 * 2 ^ 59
def prefixEnd_7064314 : Nat := 4983230072969 + 3 ^ 40 * 7064314 * 2
def baseEnd_7064314 : Nat := 3627388576285979072686817

theorem tailTrace_7064314 : CollatzResearch.WordTrace tailWord_7064314 prefixEnd_7064314 3627388576285979072686817 := by
  unfold tailWord_7064314
  simp only [CollatzResearch.WordTrace]
  refine ⟨64414174732301085405707999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171771132619469561081887997 64414174732301085405707999)
  ·
    refine ⟨96621262098451628108561999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64414174732301085405707999 96621262098451628108561999)
    ·
      refine ⟨144931893147677442162842999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96621262098451628108561999 144931893147677442162842999)
      ·
        refine ⟨217397839721516163244264499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144931893147677442162842999 217397839721516163244264499)
        ·
          refine ⟨326096759582274244866396749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217397839721516163244264499 326096759582274244866396749)
          ·
            refine ⟨122286284843352841824898781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326096759582274244866396749 122286284843352841824898781)
            ·
              refine ⟨45857356816257315684337043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122286284843352841824898781 45857356816257315684337043)
              ·
                refine ⟨68786035224385973526505565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45857356816257315684337043 68786035224385973526505565)
                ·
                  refine ⟨25794763209144740072439587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68786035224385973526505565 25794763209144740072439587)
                  ·
                    refine ⟨38692144813717110108659381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25794763209144740072439587 38692144813717110108659381)
                    ·
                      refine ⟨3627388576285979072686817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38692144813717110108659381 3627388576285979072686817)
                      ·
                        rfl

theorem cell23_7064314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_7064314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064314 prefixEnd_7064314 := by exact prefixLift 7064314
  have htrace : WordTrace (prefixWord ++ tailWord_7064314) baseStart_7064314 baseEnd_7064314 := by
    simpa [prefixWord, tailWord_7064314, baseEnd_7064314] using wordTrace_append hprefix tailTrace_7064314
  have hstable : (prefixWord ++ tailWord_7064314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064314).length < 2 ^ (prefixWord ++ tailWord_7064314).sum := by decide
  have hdescent : baseEnd_7064314 < baseStart_7064314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064328 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_7064328 : Nat := 118140960795 + 7064328 * 2 ^ 59
def prefixEnd_7064328 : Nat := 4983230072969 + 3 ^ 40 * 7064328 * 2
def baseEnd_7064328 : Nat := 3627395765015142017911753

theorem tailTrace_7064328 : CollatzResearch.WordTrace tailWord_7064328 prefixEnd_7064328 3627395765015142017911753 := by
  unfold tailWord_7064328
  simp only [CollatzResearch.WordTrace]
  refine ⟨128828604775576811006920819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171771473034102414675894425 128828604775576811006920819)
  ·
    refine ⟨193242907163365216510381229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128828604775576811006920819 193242907163365216510381229)
    ·
      refine ⟨72466090186261956191392961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193242907163365216510381229 72466090186261956191392961)
      ·
        refine ⟨54349567639696467143544721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72466090186261956191392961 54349567639696467143544721)
        ·
          refine ⟨40762175729772350357658541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54349567639696467143544721 40762175729772350357658541)
          ·
            refine ⟨15285815898664631384121953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40762175729772350357658541 15285815898664631384121953)
            ·
              refine ⟨11464361923998473538091465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15285815898664631384121953 11464361923998473538091465)
              ·
                refine ⟨8598271442998855153568599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11464361923998473538091465 8598271442998855153568599)
                ·
                  refine ⟨12897407164498282730352899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598271442998855153568599 12897407164498282730352899)
                  ·
                    refine ⟨19346110746747424095529349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12897407164498282730352899 19346110746747424095529349)
                    ·
                      refine ⟨3627395765015142017911753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19346110746747424095529349 3627395765015142017911753)
                      ·
                        rfl

theorem cell23_7064328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_7064328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064328 prefixEnd_7064328 := by exact prefixLift 7064328
  have htrace : WordTrace (prefixWord ++ tailWord_7064328) baseStart_7064328 baseEnd_7064328 := by
    simpa [prefixWord, tailWord_7064328, baseEnd_7064328] using wordTrace_append hprefix tailTrace_7064328
  have hstable : (prefixWord ++ tailWord_7064328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064328).length < 2 ^ (prefixWord ++ tailWord_7064328).sum := by decide
  have hdescent : baseEnd_7064328 < baseStart_7064328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064345 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 1, 2, 2]
def baseStart_7064345 : Nat := 118140960795 + 7064345 * 2 ^ 59
def prefixEnd_7064345 : Nat := 4983230072969 + 3 ^ 40 * 7064345 * 2
def baseEnd_7064345 : Nat := 3627404494186268451399175

theorem tailTrace_7064345 : CollatzResearch.WordTrace tailWord_7064345 prefixEnd_7064345 3627404494186268451399175 := by
  unfold tailWord_7064345
  simp only [CollatzResearch.WordTrace]
  refine ⟨257657829592092033917210489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171771886394728022611473659 257657829592092033917210489)
  ·
    refine ⟨193243372194069025437907867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257657829592092033917210489 193243372194069025437907867)
    ·
      refine ⟨289865058291103538156861801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193243372194069025437907867 289865058291103538156861801)
      ·
        refine ⟨217398793718327653617646351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289865058291103538156861801 217398793718327653617646351)
        ·
          refine ⟨326098190577491480426469527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217398793718327653617646351 326098190577491480426469527)
          ·
            refine ⟨489147285866237220639704291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326098190577491480426469527 489147285866237220639704291)
            ·
              refine ⟨733720928799355830959556437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489147285866237220639704291 733720928799355830959556437)
              ·
                refine ⟨4299146067183725572028651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 733720928799355830959556437 4299146067183725572028651)
                ·
                  refine ⟨6448719100775588358042977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299146067183725572028651 6448719100775588358042977)
                  ·
                    refine ⟨4836539325581691268532233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6448719100775588358042977 4836539325581691268532233)
                    ·
                      refine ⟨3627404494186268451399175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836539325581691268532233 3627404494186268451399175)
                      ·
                        rfl

theorem cell23_7064345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_7064345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064345 prefixEnd_7064345 := by exact prefixLift 7064345
  have htrace : WordTrace (prefixWord ++ tailWord_7064345) baseStart_7064345 baseEnd_7064345 := by
    simpa [prefixWord, tailWord_7064345, baseEnd_7064345] using wordTrace_append hprefix tailTrace_7064345
  have hstable : (prefixWord ++ tailWord_7064345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064345).length < 2 ^ (prefixWord ++ tailWord_7064345).sum := by decide
  have hdescent : baseEnd_7064345 < baseStart_7064345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064348 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_7064348 : Nat := 118140960795 + 7064348 * 2 ^ 59
def prefixEnd_7064348 : Nat := 4983230072969 + 3 ^ 40 * 7064348 * 2
def baseEnd_7064348 : Nat := 3627406034628231939661661

theorem tailTrace_7064348 : CollatzResearch.WordTrace tailWord_7064348 prefixEnd_7064348 3627406034628231939661661 := by
  unfold tailWord_7064348
  simp only [CollatzResearch.WordTrace]
  refine ⟨128828969505540582714784849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171771959340720776953046465 128828969505540582714784849)
  ·
    refine ⟨96621727129155437036088637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128828969505540582714784849 96621727129155437036088637)
    ·
      refine ⟨36233147673433288888533239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96621727129155437036088637 36233147673433288888533239)
      ·
        refine ⟨54349721510149933332799859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36233147673433288888533239 54349721510149933332799859)
        ·
          refine ⟨81524582265224899999199789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54349721510149933332799859 81524582265224899999199789)
          ·
            refine ⟨30571718349459337499699921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81524582265224899999199789 30571718349459337499699921)
            ·
              refine ⟨22928788762094503124774941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30571718349459337499699921 22928788762094503124774941)
              ·
                refine ⟨8598295785785438671790603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22928788762094503124774941 8598295785785438671790603)
                ·
                  refine ⟨12897443678678158007685905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598295785785438671790603 12897443678678158007685905)
                  ·
                    refine ⟨9673082759008618505764429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12897443678678158007685905 9673082759008618505764429)
                    ·
                      refine ⟨3627406034628231939661661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9673082759008618505764429 3627406034628231939661661)
                      ·
                        rfl

theorem cell23_7064348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_7064348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064348 prefixEnd_7064348 := by exact prefixLift 7064348
  have htrace : WordTrace (prefixWord ++ tailWord_7064348) baseStart_7064348 baseEnd_7064348 := by
    simpa [prefixWord, tailWord_7064348, baseEnd_7064348] using wordTrace_append hprefix tailTrace_7064348
  have hstable : (prefixWord ++ tailWord_7064348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064348).length < 2 ^ (prefixWord ++ tailWord_7064348).sum := by decide
  have hdescent : baseEnd_7064348 < baseStart_7064348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064364 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_7064364 : Nat := 118140960795 + 7064364 * 2 ^ 59
def prefixEnd_7064364 : Nat := 4983230072969 + 3 ^ 40 * 7064364 * 2
def baseEnd_7064364 : Nat := 1209138083439567959020529

theorem tailTrace_7064364 : CollatzResearch.WordTrace tailWord_7064364 prefixEnd_7064364 1209138083439567959020529 := by
  unfold tailWord_7064364
  simp only [CollatzResearch.WordTrace]
  refine ⟨128829261289511600081076073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171772348386015466774768097 128829261289511600081076073)
  ·
    refine ⟨96621945967133700060807055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128829261289511600081076073 96621945967133700060807055)
    ·
      refine ⟨144932918950700550091210583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96621945967133700060807055 144932918950700550091210583)
      ·
        refine ⟨217399378426050825136815875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144932918950700550091210583 217399378426050825136815875)
        ·
          refine ⟨326099067639076237705223813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217399378426050825136815875 326099067639076237705223813)
          ·
            refine ⟨61143575182326794569729465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326099067639076237705223813 61143575182326794569729465)
            ·
              refine ⟨45857681386745095927297099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61143575182326794569729465 45857681386745095927297099)
              ·
                refine ⟨68786522080117643890945649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45857681386745095927297099 68786522080117643890945649)
                ·
                  refine ⟨51589891560088232918209237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68786522080117643890945649 51589891560088232918209237)
                  ·
                    refine ⟨1209138083439567959020529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51589891560088232918209237 1209138083439567959020529)
                    ·
                      rfl

theorem cell23_7064364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_7064364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064364 prefixEnd_7064364 := by exact prefixLift 7064364
  have htrace : WordTrace (prefixWord ++ tailWord_7064364) baseStart_7064364 baseEnd_7064364 := by
    simpa [prefixWord, tailWord_7064364, baseEnd_7064364] using wordTrace_append hprefix tailTrace_7064364
  have hstable : (prefixWord ++ tailWord_7064364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064364).length < 2 ^ (prefixWord ++ tailWord_7064364).sum := by decide
  have hdescent : baseEnd_7064364 < baseStart_7064364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064382 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_7064382 : Nat := 118140960795 + 7064382 * 2 ^ 59
def prefixEnd_7064382 : Nat := 4983230072969 + 3 ^ 40 * 7064382 * 2
def baseEnd_7064382 : Nat := 3627423492970484806636505

theorem tailTrace_7064382 : CollatzResearch.WordTrace tailWord_7064382 prefixEnd_7064382 3627423492970484806636505 := by
  unfold tailWord_7064382
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207397386619748654538425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171772786061971992824204933 32207397386619748654538425)
  ·
    refine ⟨24155548039964811490903819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32207397386619748654538425 24155548039964811490903819)
    ·
      refine ⟨36233322059947217236355729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24155548039964811490903819 36233322059947217236355729)
      ·
        refine ⟨27174991544960412927266797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36233322059947217236355729 27174991544960412927266797)
        ·
          refine ⟨10190621829360154847725049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27174991544960412927266797 10190621829360154847725049)
          ·
            refine ⟨7642966372020116135793787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10190621829360154847725049 7642966372020116135793787)
            ·
              refine ⟨11464449558030174203690681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7642966372020116135793787 11464449558030174203690681)
              ·
                refine ⟨8598337168522630652768011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11464449558030174203690681 8598337168522630652768011)
                ·
                  refine ⟨12897505752783945979152017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598337168522630652768011 12897505752783945979152017)
                  ·
                    refine ⟨9673129314587959484364013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12897505752783945979152017 9673129314587959484364013)
                    ·
                      refine ⟨3627423492970484806636505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9673129314587959484364013 3627423492970484806636505)
                      ·
                        rfl

theorem cell23_7064382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_7064382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064382 prefixEnd_7064382 := by exact prefixLift 7064382
  have htrace : WordTrace (prefixWord ++ tailWord_7064382) baseStart_7064382 baseEnd_7064382 := by
    simpa [prefixWord, tailWord_7064382, baseEnd_7064382] using wordTrace_append hprefix tailTrace_7064382
  have hstable : (prefixWord ++ tailWord_7064382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064382).length < 2 ^ (prefixWord ++ tailWord_7064382).sum := by decide
  have hdescent : baseEnd_7064382 < baseStart_7064382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064394 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_7064394 : Nat := 118140960795 + 7064394 * 2 ^ 59
def prefixEnd_7064394 : Nat := 4983230072969 + 3 ^ 40 * 7064394 * 2
def baseEnd_7064394 : Nat := 1209143218246112919895483

theorem tailTrace_7064394 : CollatzResearch.WordTrace tailWord_7064394 prefixEnd_7064394 1209143218246112919895483 := by
  unfold tailWord_7064394
  simp only [CollatzResearch.WordTrace]
  refine ⟨64414904192228628821436059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171773077845943010190496157 64414904192228628821436059)
  ·
    refine ⟨96622356288342943232154089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64414904192228628821436059 96622356288342943232154089)
    ·
      refine ⟨72466767216257207424115567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96622356288342943232154089 72466767216257207424115567)
      ·
        refine ⟨108700150824385811136173351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72466767216257207424115567 108700150824385811136173351)
        ·
          refine ⟨163050226236578716704260027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108700150824385811136173351 163050226236578716704260027)
          ·
            refine ⟨244575339354868075056390041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163050226236578716704260027 244575339354868075056390041)
            ·
              refine ⟨183431504516151056292292531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244575339354868075056390041 183431504516151056292292531)
              ·
                refine ⟨275147256774226584438438797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183431504516151056292292531 275147256774226584438438797)
                ·
                  refine ⟨103180221290334969164414549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275147256774226584438438797 103180221290334969164414549)
                  ·
                    refine ⟨1209143218246112919895483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103180221290334969164414549 1209143218246112919895483)
                    ·
                      rfl

theorem cell23_7064394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_7064394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064394 prefixEnd_7064394 := by exact prefixLift 7064394
  have htrace : WordTrace (prefixWord ++ tailWord_7064394) baseStart_7064394 baseEnd_7064394 := by
    simpa [prefixWord, tailWord_7064394, baseEnd_7064394] using wordTrace_append hprefix tailTrace_7064394
  have hstable : (prefixWord ++ tailWord_7064394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064394).length < 2 ^ (prefixWord ++ tailWord_7064394).sum := by decide
  have hdescent : baseEnd_7064394 < baseStart_7064394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064412 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7064412 : Nat := 118140960795 + 7064412 * 2 ^ 59
def prefixEnd_7064412 : Nat := 4983230072969 + 3 ^ 40 * 7064412 * 2
def baseEnd_7064412 : Nat := 3627438897390119689261367

theorem tailTrace_7064412 : CollatzResearch.WordTrace tailWord_7064412 prefixEnd_7064412 3627438897390119689261367 := by
  unfold tailWord_7064412
  simp only [CollatzResearch.WordTrace]
  refine ⟨128830136641424652179949745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171773515521899536239932993 128830136641424652179949745)
  ·
    refine ⟨96622602481068489134962309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128830136641424652179949745 96622602481068489134962309)
    ·
      refine ⟨18116737965200341712805433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96622602481068489134962309 18116737965200341712805433)
      ·
        refine ⟨13587553473900256284604075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18116737965200341712805433 13587553473900256284604075)
        ·
          refine ⟨20381330210850384426906113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13587553473900256284604075 20381330210850384426906113)
          ·
            refine ⟨15285997658137788320179585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20381330210850384426906113 15285997658137788320179585)
            ·
              refine ⟨11464498243603341240134689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15285997658137788320179585 11464498243603341240134689)
              ·
                refine ⟨8598373682702505930101017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11464498243603341240134689 8598373682702505930101017)
                ·
                  refine ⟨6448780262026879447575763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8598373682702505930101017 6448780262026879447575763)
                  ·
                    refine ⟨9673170393040319171363645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6448780262026879447575763 9673170393040319171363645)
                    ·
                      refine ⟨3627438897390119689261367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9673170393040319171363645 3627438897390119689261367)
                      ·
                        rfl

theorem cell23_7064412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7064412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064412 prefixEnd_7064412 := by exact prefixLift 7064412
  have htrace : WordTrace (prefixWord ++ tailWord_7064412) baseStart_7064412 baseEnd_7064412 := by
    simpa [prefixWord, tailWord_7064412, baseEnd_7064412] using wordTrace_append hprefix tailTrace_7064412
  have hstable : (prefixWord ++ tailWord_7064412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064412).length < 2 ^ (prefixWord ++ tailWord_7064412).sum := by decide
  have hdescent : baseEnd_7064412 < baseStart_7064412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064421 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_7064421 : Nat := 118140960795 + 7064421 * 2 ^ 59
def prefixEnd_7064421 : Nat := 4983230072969 + 3 ^ 40 * 7064421 * 2
def baseEnd_7064421 : Nat := 3627443518716010154048825

theorem tailTrace_7064421 : CollatzResearch.WordTrace tailWord_7064421 prefixEnd_7064421 3627443518716010154048825 := by
  unfold tailWord_7064421
  simp only [CollatzResearch.WordTrace]
  refine ⟨257660601539816698896977117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171773734359877799264651411 257660601539816698896977117)
  ·
    refine ⟨96622725577431262086366419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257660601539816698896977117 96622725577431262086366419)
    ·
      refine ⟨144934088366146893129549629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96622725577431262086366419 144934088366146893129549629)
      ·
        refine ⟨54350283137305084923581111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144934088366146893129549629 54350283137305084923581111)
        ·
          refine ⟨81525424705957627385371667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54350283137305084923581111 81525424705957627385371667)
          ·
            refine ⟨122288137058936441078057501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81525424705957627385371667 122288137058936441078057501)
            ·
              refine ⟨45858051397101165404271563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122288137058936441078057501 45858051397101165404271563)
              ·
                refine ⟨68787077095651748106407345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45858051397101165404271563 68787077095651748106407345)
                ·
                  refine ⟨51590307821738811079805509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68787077095651748106407345 51590307821738811079805509)
                  ·
                    refine ⟨9673182716576027077463533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51590307821738811079805509 9673182716576027077463533)
                    ·
                      refine ⟨3627443518716010154048825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9673182716576027077463533 3627443518716010154048825)
                      ·
                        rfl

theorem cell23_7064421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_7064421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064421 prefixEnd_7064421 := by exact prefixLift 7064421
  have htrace : WordTrace (prefixWord ++ tailWord_7064421) baseStart_7064421 baseEnd_7064421 := by
    simpa [prefixWord, tailWord_7064421, baseEnd_7064421] using wordTrace_append hprefix tailTrace_7064421
  have hstable : (prefixWord ++ tailWord_7064421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064421).length < 2 ^ (prefixWord ++ tailWord_7064421).sum := by decide
  have hdescent : baseEnd_7064421 < baseStart_7064421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064435 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 2, 2, 2]
def baseStart_7064435 : Nat := 118140960795 + 7064435 * 2 ^ 59
def prefixEnd_7064435 : Nat := 4983230072969 + 3 ^ 40 * 7064435 * 2
def baseEnd_7064435 : Nat := 3627450707445173099273761

theorem tailTrace_7064435 : CollatzResearch.WordTrace tailWord_7064435 prefixEnd_7064435 3627450707445173099273761 := by
  unfold tailWord_7064435
  simp only [CollatzResearch.WordTrace]
  refine ⟨257661112161765979287986759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171774074774510652858657839 257661112161765979287986759)
  ·
    refine ⟨386491668242648968931980139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257661112161765979287986759 386491668242648968931980139)
    ·
      refine ⟨579737502363973453397970209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386491668242648968931980139 579737502363973453397970209)
      ·
        refine ⟨434803126772980090048477657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579737502363973453397970209 434803126772980090048477657)
        ·
          refine ⟨326102345079735067536358243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434803126772980090048477657 326102345079735067536358243)
          ·
            refine ⟨489153517619602601304537365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326102345079735067536358243 489153517619602601304537365)
            ·
              refine ⟨22929071138418871936150189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 489153517619602601304537365 22929071138418871936150189)
              ·
                refine ⟨8598401676907076976056321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22929071138418871936150189 8598401676907076976056321)
                ·
                  refine ⟨6448801257680307732042241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8598401676907076976056321 6448801257680307732042241)
                  ·
                    refine ⟨4836600943260230799031681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6448801257680307732042241 4836600943260230799031681)
                    ·
                      refine ⟨3627450707445173099273761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836600943260230799031681 3627450707445173099273761)
                      ·
                        rfl

theorem cell23_7064435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 2, 2].length) (baseStart_7064435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064435 prefixEnd_7064435 := by exact prefixLift 7064435
  have htrace : WordTrace (prefixWord ++ tailWord_7064435) baseStart_7064435 baseEnd_7064435 := by
    simpa [prefixWord, tailWord_7064435, baseEnd_7064435] using wordTrace_append hprefix tailTrace_7064435
  have hstable : (prefixWord ++ tailWord_7064435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064435).length < 2 ^ (prefixWord ++ tailWord_7064435).sum := by decide
  have hdescent : baseEnd_7064435 < baseStart_7064435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064441 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 7]
def baseStart_7064441 : Nat := 118140960795 + 7064441 * 2 ^ 59
def prefixEnd_7064441 : Nat := 4983230072969 + 3 ^ 40 * 7064441 * 2
def baseEnd_7064441 : Nat := 403050420925455563977637

theorem tailTrace_7064441 : CollatzResearch.WordTrace tailWord_7064441 prefixEnd_7064441 403050420925455563977637 := by
  unfold tailWord_7064441
  simp only [CollatzResearch.WordTrace]
  refine ⟨257661330999744242312705177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171774220666496161541803451 257661330999744242312705177)
  ·
    refine ⟨193245998249808181734528883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257661330999744242312705177 193245998249808181734528883)
    ·
      refine ⟨289868997374712272601793325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193245998249808181734528883 289868997374712272601793325)
      ·
        refine ⟨108700874015517102225672497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289868997374712272601793325 108700874015517102225672497)
        ·
          refine ⟨81525655511637826669254373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108700874015517102225672497 81525655511637826669254373)
          ·
            refine ⟨15286060408432092500485195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81525655511637826669254373 15286060408432092500485195)
            ·
              refine ⟨22929090612648138750727793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15286060408432092500485195 22929090612648138750727793)
              ·
                refine ⟨17196817959486104063045845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22929090612648138750727793 17196817959486104063045845)
                ·
                  refine ⟨403050420925455563977637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17196817959486104063045845 403050420925455563977637)
                  ·
                    rfl

theorem cell23_7064441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_7064441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064441 prefixEnd_7064441 := by exact prefixLift 7064441
  have htrace : WordTrace (prefixWord ++ tailWord_7064441) baseStart_7064441 baseEnd_7064441 := by
    simpa [prefixWord, tailWord_7064441, baseEnd_7064441] using wordTrace_append hprefix tailTrace_7064441
  have hstable : (prefixWord ++ tailWord_7064441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064441).length < 2 ^ (prefixWord ++ tailWord_7064441).sum := by decide
  have hdescent : baseEnd_7064441 < baseStart_7064441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064451 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 3]
def baseStart_7064451 : Nat := 118140960795 + 7064451 * 2 ^ 59
def prefixEnd_7064451 : Nat := 4983230072969 + 3 ^ 40 * 7064451 * 2
def baseEnd_7064451 : Nat := 3627458923135645036673687

theorem tailTrace_7064451 : CollatzResearch.WordTrace tailWord_7064451 prefixEnd_7064451 3627458923135645036673687 := by
  unfold tailWord_7064451
  simp only [CollatzResearch.WordTrace]
  refine ⟨257661695729708014020569207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171774463819805342680379471 257661695729708014020569207)
  ·
    refine ⟨386492543594562021030853811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257661695729708014020569207 386492543594562021030853811)
    ·
      refine ⟨579738815391843031546280717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386492543594562021030853811 579738815391843031546280717)
      ·
        refine ⟨217402055771941136829855269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579738815391843031546280717 217402055771941136829855269)
        ·
          refine ⟨40762885457238963155597863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217402055771941136829855269 40762885457238963155597863)
          ·
            refine ⟨61144328185858444733396795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40762885457238963155597863 61144328185858444733396795)
            ·
              refine ⟨91716492278787667100095193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61144328185858444733396795 91716492278787667100095193)
              ·
                refine ⟨68787369209090750325071395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91716492278787667100095193 68787369209090750325071395)
                ·
                  refine ⟨103181053813636125487607093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68787369209090750325071395 103181053813636125487607093)
                  ·
                    refine ⟨9673223795028386764463165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103181053813636125487607093 9673223795028386764463165)
                    ·
                      refine ⟨3627458923135645036673687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9673223795028386764463165 3627458923135645036673687)
                      ·
                        rfl

theorem cell23_7064451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_7064451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064451 prefixEnd_7064451 := by exact prefixLift 7064451
  have htrace : WordTrace (prefixWord ++ tailWord_7064451) baseStart_7064451 baseEnd_7064451 := by
    simpa [prefixWord, tailWord_7064451, baseEnd_7064451] using wordTrace_append hprefix tailTrace_7064451
  have hstable : (prefixWord ++ tailWord_7064451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064451).length < 2 ^ (prefixWord ++ tailWord_7064451).sum := by decide
  have hdescent : baseEnd_7064451 < baseStart_7064451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064468 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_7064468 : Nat := 118140960795 + 7064468 * 2 ^ 59
def prefixEnd_7064468 : Nat := 4983230072969 + 3 ^ 40 * 7064468 * 2
def baseEnd_7064468 : Nat := 3627467652306771470161109

theorem tailTrace_7064468 : CollatzResearch.WordTrace tailWord_7064468 prefixEnd_7064468 3627467652306771470161109 := by
  unfold tailWord_7064468
  simp only [CollatzResearch.WordTrace]
  refine ⟨128831157885323212961969029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171774877180430950615958705 128831157885323212961969029)
  ·
    refine ⟨24155842103498102430369193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128831157885323212961969029 24155842103498102430369193)
    ·
      refine ⟨18116881577623576822776895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24155842103498102430369193 18116881577623576822776895)
      ·
        refine ⟨27175322366435365234165343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18116881577623576822776895 27175322366435365234165343)
        ·
          refine ⟨40762983549653047851248015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27175322366435365234165343 40762983549653047851248015)
          ·
            refine ⟨61144475324479571776872023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40762983549653047851248015 61144475324479571776872023)
            ·
              refine ⟨91716712986719357665308035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61144475324479571776872023 91716712986719357665308035)
              ·
                refine ⟨137575069480079036497962053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91716712986719357665308035 137575069480079036497962053)
                ·
                  refine ⟨25795325527514819343367885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137575069480079036497962053 25795325527514819343367885)
                  ·
                    refine ⟨9673247072818057253762957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25795325527514819343367885 9673247072818057253762957)
                    ·
                      refine ⟨3627467652306771470161109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9673247072818057253762957 3627467652306771470161109)
                      ·
                        rfl

theorem cell23_7064468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_7064468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064468 prefixEnd_7064468 := by exact prefixLift 7064468
  have htrace : WordTrace (prefixWord ++ tailWord_7064468) baseStart_7064468 baseEnd_7064468 := by
    simpa [prefixWord, tailWord_7064468, baseEnd_7064468] using wordTrace_append hprefix tailTrace_7064468
  have hstable : (prefixWord ++ tailWord_7064468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064468).length < 2 ^ (prefixWord ++ tailWord_7064468).sum := by decide
  have hdescent : baseEnd_7064468 < baseStart_7064468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064471 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 4, 5]
def baseStart_7064471 : Nat := 118140960795 + 7064471 * 2 ^ 59
def prefixEnd_7064471 : Nat := 4983230072969 + 3 ^ 40 * 7064471 * 2
def baseEnd_7064471 : Nat := 1209156397582911652807865

theorem tailTrace_7064471 : CollatzResearch.WordTrace tailWord_7064471 prefixEnd_7064471 1209156397582911652807865 := by
  unfold tailWord_7064471
  simp only [CollatzResearch.WordTrace]
  refine ⟨257662425189635557436297267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171774950126423704957531511 257662425189635557436297267)
  ·
    refine ⟨386493637784453336154445901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257662425189635557436297267 386493637784453336154445901)
    ·
      refine ⟨144935114169170001057917213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386493637784453336154445901 144935114169170001057917213)
      ·
        refine ⟨54350667813438750396718955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144935114169170001057917213 54350667813438750396718955)
        ·
          refine ⟨81526001720158125595078433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54350667813438750396718955 81526001720158125595078433)
          ·
            refine ⟨61144501290118594196308825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81526001720158125595078433 61144501290118594196308825)
            ·
              refine ⟨45858375967588945647231619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61144501290118594196308825 45858375967588945647231619)
              ·
                refine ⟨68787563951383418470847429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45858375967588945647231619 68787563951383418470847429)
                ·
                  refine ⟨12897668240884390963283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68787563951383418470847429 12897668240884390963283893)
                  ·
                    refine ⟨1209156397582911652807865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12897668240884390963283893 1209156397582911652807865)
                    ·
                      rfl

theorem cell23_7064471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_7064471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064471 prefixEnd_7064471 := by exact prefixLift 7064471
  have htrace : WordTrace (prefixWord ++ tailWord_7064471) baseStart_7064471 baseEnd_7064471 := by
    simpa [prefixWord, tailWord_7064471, baseEnd_7064471] using wordTrace_append hprefix tailTrace_7064471
  have hstable : (prefixWord ++ tailWord_7064471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064471).length < 2 ^ (prefixWord ++ tailWord_7064471).sum := by decide
  have hdescent : baseEnd_7064471 < baseStart_7064471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064491 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 4]
def baseStart_7064491 : Nat := 118140960795 + 7064491 * 2 ^ 59
def prefixEnd_7064491 : Nat := 4983230072969 + 3 ^ 40 * 7064491 * 2
def baseEnd_7064491 : Nat := 3627479462361824880173503

theorem tailTrace_7064491 : CollatzResearch.WordTrace tailWord_7064491 prefixEnd_7064491 3627479462361824880173503 := by
  unfold tailWord_7064491
  simp only [CollatzResearch.WordTrace]
  refine ⟨257663154649563100852025327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171775436433042067234683551 257663154649563100852025327)
  ·
    refine ⟨386494731974344651278037991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257663154649563100852025327 386494731974344651278037991)
    ·
      refine ⟨579742097961516976917056987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386494731974344651278037991 579742097961516976917056987)
      ·
        refine ⟨869613146942275465375585481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579742097961516976917056987 869613146942275465375585481)
        ·
          refine ⟨652209860206706599031689111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869613146942275465375585481 652209860206706599031689111)
          ·
            refine ⟨978314790310059898547533667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652209860206706599031689111 978314790310059898547533667)
            ·
              refine ⟨1467472185465089847821300501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978314790310059898547533667 1467472185465089847821300501)
              ·
                refine ⟨68787758693676086616623461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1467472185465089847821300501 68787758693676086616623461)
                ·
                  refine ⟨12897704755064266240616899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68787758693676086616623461 12897704755064266240616899)
                  ·
                    refine ⟨19346557132596399360925349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12897704755064266240616899 19346557132596399360925349)
                    ·
                      refine ⟨3627479462361824880173503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19346557132596399360925349 3627479462361824880173503)
                      ·
                        rfl

theorem cell23_7064491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 4].length) (baseStart_7064491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064491 prefixEnd_7064491 := by exact prefixLift 7064491
  have htrace : WordTrace (prefixWord ++ tailWord_7064491) baseStart_7064491 baseEnd_7064491 := by
    simpa [prefixWord, tailWord_7064491, baseEnd_7064491] using wordTrace_append hprefix tailTrace_7064491
  have hstable : (prefixWord ++ tailWord_7064491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064491).length < 2 ^ (prefixWord ++ tailWord_7064491).sum := by decide
  have hdescent : baseEnd_7064491 < baseStart_7064491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064501 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_7064501 : Nat := 118140960795 + 7064501 * 2 ^ 59
def prefixEnd_7064501 : Nat := 4983230072969 + 3 ^ 40 * 7064501 * 2
def baseEnd_7064501 : Nat := 1209161532389456613682819

theorem tailTrace_7064501 : CollatzResearch.WordTrace tailWord_7064501 prefixEnd_7064501 1209161532389456613682819 := by
  unfold tailWord_7064501
  simp only [CollatzResearch.WordTrace]
  refine ⟨257663519379526872559889357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171775679586351248373259571 257663519379526872559889357)
  ·
    refine ⟨96623819767322577209958509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257663519379526872559889357 96623819767322577209958509)
    ·
      refine ⟨36233932412745966453734441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96623819767322577209958509 36233932412745966453734441)
      ·
        refine ⟨27175449309559474840300831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36233932412745966453734441 27175449309559474840300831)
        ·
          refine ⟨40763173964339212260451247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27175449309559474840300831 40763173964339212260451247)
          ·
            refine ⟨61144760946508818390676871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40763173964339212260451247 61144760946508818390676871)
            ·
              refine ⟨91717141419763227586015307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61144760946508818390676871 91717141419763227586015307)
              ·
                refine ⟨137575712129644841379022961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91717141419763227586015307 137575712129644841379022961)
                ·
                  refine ⟨103181784097233631034267221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137575712129644841379022961 103181784097233631034267221)
                  ·
                    refine ⟨1209161532389456613682819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103181784097233631034267221 1209161532389456613682819)
                    ·
                      rfl

theorem cell23_7064501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_7064501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064501 prefixEnd_7064501 := by exact prefixLift 7064501
  have htrace : WordTrace (prefixWord ++ tailWord_7064501) baseStart_7064501 baseEnd_7064501 := by
    simpa [prefixWord, tailWord_7064501, baseEnd_7064501] using wordTrace_append hprefix tailTrace_7064501
  have hstable : (prefixWord ++ tailWord_7064501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064501).length < 2 ^ (prefixWord ++ tailWord_7064501).sum := by decide
  have hdescent : baseEnd_7064501 < baseStart_7064501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064632 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 1, 1, 4]
def baseStart_7064632 : Nat := 118140960795 + 7064632 * 2 ^ 59
def prefixEnd_7064632 : Nat := 4983230072969 + 3 ^ 40 * 7064632 * 2
def baseEnd_7064632 : Nat := 3627551863134108828510355

theorem tailTrace_7064632 : CollatzResearch.WordTrace tailWord_7064632 prefixEnd_7064632 3627551863134108828510355 := by
  unfold tailWord_7064632
  simp only [CollatzResearch.WordTrace]
  refine ⟨128834148671026140966454075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171778864894701521288605433 128834148671026140966454075)
  ·
    refine ⟨193251223006539211449681113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128834148671026140966454075 193251223006539211449681113)
    ·
      refine ⟨144938417254904408587260835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193251223006539211449681113 144938417254904408587260835)
      ·
        refine ⟨217407625882356612880891253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144938417254904408587260835 217407625882356612880891253)
        ·
          refine ⟨20381964926470932457583555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217407625882356612880891253 20381964926470932457583555)
          ·
            refine ⟨30572947389706398686375333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20381964926470932457583555 30572947389706398686375333)
            ·
              refine ⟨5732427635569949753695375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30572947389706398686375333 5732427635569949753695375)
              ·
                refine ⟨8598641453354924630543063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732427635569949753695375 8598641453354924630543063)
                ·
                  refine ⟨12897962180032386945814595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598641453354924630543063 12897962180032386945814595)
                  ·
                    refine ⟨19346943270048580418721893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12897962180032386945814595 19346943270048580418721893)
                    ·
                      refine ⟨3627551863134108828510355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19346943270048580418721893 3627551863134108828510355)
                      ·
                        rfl

theorem cell23_7064632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_7064632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064632 prefixEnd_7064632 := by exact prefixLift 7064632
  have htrace : WordTrace (prefixWord ++ tailWord_7064632) baseStart_7064632 baseEnd_7064632 := by
    simpa [prefixWord, tailWord_7064632, baseEnd_7064632] using wordTrace_append hprefix tailTrace_7064632
  have hstable : (prefixWord ++ tailWord_7064632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064632).length < 2 ^ (prefixWord ++ tailWord_7064632).sum := by decide
  have hdescent : baseEnd_7064632 < baseStart_7064632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064682 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_7064682 : Nat := 118140960795 + 7064682 * 2 ^ 59
def prefixEnd_7064682 : Nat := 4983230072969 + 3 ^ 40 * 7064682 * 2
def baseEnd_7064682 : Nat := 3627577537166833632885125

theorem tailTrace_7064682 : CollatzResearch.WordTrace tailWord_7064682 prefixEnd_7064682 3627577537166833632885125 := by
  unfold tailWord_7064682
  simp only [CollatzResearch.WordTrace]
  refine ⟨64417530247967785118057075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171780080661247426981485533 64417530247967785118057075)
  ·
    refine ⟨96626295371951677677085613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64417530247967785118057075 96626295371951677677085613)
    ·
      refine ⟨36234860764481879128907105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96626295371951677677085613 36234860764481879128907105)
      ·
        refine ⟨27176145573361409346680329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36234860764481879128907105 27176145573361409346680329)
        ·
          refine ⟨20382109180021057010010247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27176145573361409346680329 20382109180021057010010247)
          ·
            refine ⟨30573163770031585515015371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20382109180021057010010247 30573163770031585515015371)
            ·
              refine ⟨45859745655047378272523057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30573163770031585515015371 45859745655047378272523057)
              ·
                refine ⟨34394809241285533704392293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45859745655047378272523057 34394809241285533704392293)
                ·
                  refine ⟨6449026732741037569573555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34394809241285533704392293 6449026732741037569573555)
                  ·
                    refine ⟨9673540099111556354360333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6449026732741037569573555 9673540099111556354360333)
                    ·
                      refine ⟨3627577537166833632885125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9673540099111556354360333 3627577537166833632885125)
                      ·
                        rfl

theorem cell23_7064682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_7064682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064682 prefixEnd_7064682 := by exact prefixLift 7064682
  have htrace : WordTrace (prefixWord ++ tailWord_7064682) baseStart_7064682 baseEnd_7064682 := by
    simpa [prefixWord, tailWord_7064682, baseEnd_7064682] using wordTrace_append hprefix tailTrace_7064682
  have hstable : (prefixWord ++ tailWord_7064682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064682).length < 2 ^ (prefixWord ++ tailWord_7064682).sum := by decide
  have hdescent : baseEnd_7064682 < baseStart_7064682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064812 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 2, 4, 2]
def baseStart_7064812 : Nat := 118140960795 + 7064812 * 2 ^ 59
def prefixEnd_7064812 : Nat := 4983230072969 + 3 ^ 40 * 7064812 * 2
def baseEnd_7064812 : Nat := 3627644289651918124259527

theorem tailTrace_7064812 : CollatzResearch.WordTrace tailWord_7064812 prefixEnd_7064812 3627644289651918124259527 := by
  unfold tailWord_7064812
  simp only [CollatzResearch.WordTrace]
  refine ⟨128837431240700086337230345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171783241654266781782973793 128837431240700086337230345)
  ·
    refine ⟨96628073430525064752922759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128837431240700086337230345 96628073430525064752922759)
    ·
      refine ⟨144942110145787597129384139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96628073430525064752922759 144942110145787597129384139)
      ·
        refine ⟨217413165218681395694076209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144942110145787597129384139 217413165218681395694076209)
        ·
          refine ⟨163059873914011046770557157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217413165218681395694076209 163059873914011046770557157)
          ·
            refine ⟨30573726358877071269479467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163059873914011046770557157 30573726358877071269479467)
            ·
              refine ⟨45860589538315606904219201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30573726358877071269479467 45860589538315606904219201)
              ·
                refine ⟨34395442153736705178164401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45860589538315606904219201 34395442153736705178164401)
                ·
                  refine ⟨25796581615302528883623301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34395442153736705178164401 25796581615302528883623301)
                  ·
                    refine ⟨4836859052869224165679369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25796581615302528883623301 4836859052869224165679369)
                    ·
                      refine ⟨3627644289651918124259527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836859052869224165679369 3627644289651918124259527)
                      ·
                        rfl

theorem cell23_7064812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_7064812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064812 prefixEnd_7064812 := by exact prefixLift 7064812
  have htrace : WordTrace (prefixWord ++ tailWord_7064812) baseStart_7064812 baseEnd_7064812 := by
    simpa [prefixWord, tailWord_7064812, baseEnd_7064812] using wordTrace_append hprefix tailTrace_7064812
  have hstable : (prefixWord ++ tailWord_7064812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064812).length < 2 ^ (prefixWord ++ tailWord_7064812).sum := by decide
  have hdescent : baseEnd_7064812 < baseStart_7064812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064856 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 1, 4]
def baseStart_7064856 : Nat := 118140960795 + 7064856 * 2 ^ 59
def prefixEnd_7064856 : Nat := 4983230072969 + 3 ^ 40 * 7064856 * 2
def baseEnd_7064856 : Nat := 1209222294266905317369775

theorem tailTrace_7064856 : CollatzResearch.WordTrace tailWord_7064856 prefixEnd_7064856 1209222294266905317369775 := by
  unfold tailWord_7064856
  simp only [CollatzResearch.WordTrace]
  refine ⟨128838233646620384094531211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171784311528827178792708281 128838233646620384094531211)
  ·
    refine ⟨193257350469930576141796817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128838233646620384094531211 193257350469930576141796817)
    ·
      refine ⟨144943012852447932106347613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193257350469930576141796817 144943012852447932106347613)
      ·
        refine ⟨54353629819667974539880355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144943012852447932106347613 54353629819667974539880355)
        ·
          refine ⟨81530444729501961809820533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54353629819667974539880355 81530444729501961809820533)
          ·
            refine ⟨7643479193390808919670675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81530444729501961809820533 7643479193390808919670675)
            ·
              refine ⟨11465218790086213379506013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7643479193390808919670675 11465218790086213379506013)
              ·
                refine ⟨4299457046282330017314755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11465218790086213379506013 4299457046282330017314755)
                ·
                  refine ⟨6449185569423495025972133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299457046282330017314755 6449185569423495025972133)
                  ·
                    refine ⟨1209222294266905317369775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6449185569423495025972133 1209222294266905317369775)
                    ·
                      rfl

theorem cell23_7064856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_7064856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064856 prefixEnd_7064856 := by exact prefixLift 7064856
  have htrace : WordTrace (prefixWord ++ tailWord_7064856) baseStart_7064856 baseEnd_7064856 := by
    simpa [prefixWord, tailWord_7064856, baseEnd_7064856] using wordTrace_append hprefix tailTrace_7064856
  have hstable : (prefixWord ++ tailWord_7064856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064856).length < 2 ^ (prefixWord ++ tailWord_7064856).sum := by decide
  have hdescent : baseEnd_7064856 < baseStart_7064856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064865 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_7064865 : Nat := 118140960795 + 7064865 * 2 ^ 59
def prefixEnd_7064865 : Nat := 4983230072969 + 3 ^ 40 * 7064865 * 2
def baseEnd_7064865 : Nat := 1209223834708868805632261

theorem tailTrace_7064865 : CollatzResearch.WordTrace tailWord_7064865 prefixEnd_7064865 1209223834708868805632261 := by
  unfold tailWord_7064865
  simp only [CollatzResearch.WordTrace]
  refine ⟨257676795550208162726140049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171784530366805441817426699 257676795550208162726140049)
  ·
    refine ⟨193257596662656122044605037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257676795550208162726140049 193257596662656122044605037)
    ·
      refine ⟨72471598748496045766726889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193257596662656122044605037 72471598748496045766726889)
      ·
        refine ⟨54353699061372034325045167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72471598748496045766726889 54353699061372034325045167)
        ·
          refine ⟨81530548592058051487567751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54353699061372034325045167 81530548592058051487567751)
          ·
            refine ⟨122295822888087077231351627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81530548592058051487567751 122295822888087077231351627)
            ·
              refine ⟨183443734332130615847027441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122295822888087077231351627 183443734332130615847027441)
              ·
                refine ⟨137582800749097961885270581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183443734332130615847027441 137582800749097961885270581)
                ·
                  refine ⟨12898387570227933926744117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137582800749097961885270581 12898387570227933926744117)
                  ·
                    refine ⟨1209223834708868805632261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12898387570227933926744117 1209223834708868805632261)
                    ·
                      rfl

theorem cell23_7064865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_7064865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064865 prefixEnd_7064865 := by exact prefixLift 7064865
  have htrace : WordTrace (prefixWord ++ tailWord_7064865) baseStart_7064865 baseEnd_7064865 := by
    simpa [prefixWord, tailWord_7064865, baseEnd_7064865] using wordTrace_append hprefix tailTrace_7064865
  have hstable : (prefixWord ++ tailWord_7064865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064865).length < 2 ^ (prefixWord ++ tailWord_7064865).sum := by decide
  have hdescent : baseEnd_7064865 < baseStart_7064865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064886 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_7064886 : Nat := 118140960795 + 7064886 * 2 ^ 59
def prefixEnd_7064886 : Nat := 4983230072969 + 3 ^ 40 * 7064886 * 2
def baseEnd_7064886 : Nat := 403075809691150092748243

theorem tailTrace_7064886 : CollatzResearch.WordTrace tailWord_7064886 prefixEnd_7064886 403075809691150092748243 := by
  unfold tailWord_7064886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16104847592695755207040907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171785040988754722208436341 16104847592695755207040907)
  ·
    refine ⟨24157271389043632810561361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16104847592695755207040907 24157271389043632810561361)
    ·
      refine ⟨18117953541782724607921021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24157271389043632810561361 18117953541782724607921021)
      ·
        refine ⟨6794232578168521727970383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18117953541782724607921021 6794232578168521727970383)
        ·
          refine ⟨10191348867252782591955575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794232578168521727970383 10191348867252782591955575)
          ·
            refine ⟨15287023300879173887933363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191348867252782591955575 15287023300879173887933363)
            ·
              refine ⟨22930534951318760831900045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15287023300879173887933363 22930534951318760831900045)
              ·
                refine ⟨8598950606744535311962517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22930534951318760831900045 8598950606744535311962517)
                ·
                  refine ⟨403075809691150092748243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8598950606744535311962517 403075809691150092748243)
                  ·
                    rfl

theorem cell23_7064886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_7064886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064886 prefixEnd_7064886 := by exact prefixLift 7064886
  have htrace : WordTrace (prefixWord ++ tailWord_7064886) baseStart_7064886 baseEnd_7064886 := by
    simpa [prefixWord, tailWord_7064886, baseEnd_7064886] using wordTrace_append hprefix tailTrace_7064886
  have hstable : (prefixWord ++ tailWord_7064886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064886).length < 2 ^ (prefixWord ++ tailWord_7064886).sum := by decide
  have hdescent : baseEnd_7064886 < baseStart_7064886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064905 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_7064905 : Nat := 118140960795 + 7064905 * 2 ^ 59
def prefixEnd_7064905 : Nat := 4983230072969 + 3 ^ 40 * 7064905 * 2
def baseEnd_7064905 : Nat := 3627692043352786260396599

theorem tailTrace_7064905 : CollatzResearch.WordTrace tailWord_7064905 prefixEnd_7064905 3627692043352786260396599 := by
  unfold tailWord_7064905
  simp only [CollatzResearch.WordTrace]
  refine ⟨257678254470063249557596169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171785502980042166371730779 257678254470063249557596169)
  ·
    refine ⟨193258690852547437168197127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257678254470063249557596169 193258690852547437168197127)
    ·
      refine ⟨289888036278821155752295691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193258690852547437168197127 289888036278821155752295691)
      ·
        refine ⟨434832054418231733628443537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289888036278821155752295691 434832054418231733628443537)
        ·
          refine ⟨326124040813673800221332653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434832054418231733628443537 326124040813673800221332653)
          ·
            refine ⟨122296515305127675082999745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326124040813673800221332653 122296515305127675082999745)
            ·
              refine ⟨91722386478845756312249809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122296515305127675082999745 91722386478845756312249809)
              ·
                refine ⟨68791789859134317234187357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91722386478845756312249809 68791789859134317234187357)
                ·
                  refine ⟨25796921197175368962820259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68791789859134317234187357 25796921197175368962820259)
                  ·
                    refine ⟨38695381795763053444230389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25796921197175368962820259 38695381795763053444230389)
                    ·
                      refine ⟨3627692043352786260396599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38695381795763053444230389 3627692043352786260396599)
                      ·
                        rfl

theorem cell23_7064905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_7064905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064905 prefixEnd_7064905 := by exact prefixLift 7064905
  have htrace : WordTrace (prefixWord ++ tailWord_7064905) baseStart_7064905 baseEnd_7064905 := by
    simpa [prefixWord, tailWord_7064905, baseEnd_7064905] using wordTrace_append hprefix tailTrace_7064905
  have hstable : (prefixWord ++ tailWord_7064905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064905).length < 2 ^ (prefixWord ++ tailWord_7064905).sum := by decide
  have hdescent : baseEnd_7064905 < baseStart_7064905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064922 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_7064922 : Nat := 118140960795 + 7064922 * 2 ^ 59
def prefixEnd_7064922 : Nat := 4983230072969 + 3 ^ 40 * 7064922 * 2
def baseEnd_7064922 : Nat := 3627700772523912693884021

theorem tailTrace_7064922 : CollatzResearch.WordTrace tailWord_7064922 prefixEnd_7064922 3627700772523912693884021 := by
  unfold tailWord_7064922
  simp only [CollatzResearch.WordTrace]
  refine ⟨64419718627750415365241255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171785916340667774307310013 64419718627750415365241255)
  ·
    refine ⟨96629577941625623047861883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64419718627750415365241255 96629577941625623047861883)
    ·
      refine ⟨144944366912438434571792825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96629577941625623047861883 144944366912438434571792825)
      ·
        refine ⟨108708275184328825928844619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144944366912438434571792825 108708275184328825928844619)
        ·
          refine ⟨163062412776493238893266929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108708275184328825928844619 163062412776493238893266929)
          ·
            refine ⟨122296809582369929169950197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163062412776493238893266929 122296809582369929169950197)
            ·
              refine ⟨11465325898347180859682831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122296809582369929169950197 11465325898347180859682831)
              ·
                refine ⟨17197988847520771289524247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11465325898347180859682831 17197988847520771289524247)
                ·
                  refine ⟨25796983271281156934286371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17197988847520771289524247 25796983271281156934286371)
                  ·
                    refine ⟨38695474906921735401429557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25796983271281156934286371 38695474906921735401429557)
                    ·
                      refine ⟨3627700772523912693884021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38695474906921735401429557 3627700772523912693884021)
                      ·
                        rfl

theorem cell23_7064922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_7064922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064922 prefixEnd_7064922 := by exact prefixLift 7064922
  have htrace : WordTrace (prefixWord ++ tailWord_7064922) baseStart_7064922 baseEnd_7064922 := by
    simpa [prefixWord, tailWord_7064922, baseEnd_7064922] using wordTrace_append hprefix tailTrace_7064922
  have hstable : (prefixWord ++ tailWord_7064922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064922).length < 2 ^ (prefixWord ++ tailWord_7064922).sum := by decide
  have hdescent : baseEnd_7064922 < baseStart_7064922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064945 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_7064945 : Nat := 118140960795 + 7064945 * 2 ^ 59
def prefixEnd_7064945 : Nat := 4983230072969 + 3 ^ 40 * 7064945 * 2
def baseEnd_7064945 : Nat := 3627712582578966103896415

theorem tailTrace_7064945 : CollatzResearch.WordTrace tailWord_7064945 prefixEnd_7064945 3627712582578966103896415 := by
  unfold tailWord_7064945
  simp only [CollatzResearch.WordTrace]
  refine ⟨257679713389918336389052289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171786475593278890926034859 257679713389918336389052289)
  ·
    refine ⟨193259785042438752291789217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257679713389918336389052289 193259785042438752291789217)
    ·
      refine ⟨144944838781829064218841913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193259785042438752291789217 144944838781829064218841913)
      ·
        refine ⟨108708629086371798164131435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144944838781829064218841913 108708629086371798164131435)
        ·
          refine ⟨163062943629557697246197153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108708629086371798164131435 163062943629557697246197153)
          ·
            refine ⟨122297207722168272934647865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163062943629557697246197153 122297207722168272934647865)
            ·
              refine ⟨91722905791626204700985899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122297207722168272934647865 91722905791626204700985899)
              ·
                refine ⟨137584358687439307051478849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91722905791626204700985899 137584358687439307051478849)
                ·
                  refine ⟨103188269015579480288609137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137584358687439307051478849 103188269015579480288609137)
                  ·
                    refine ⟨77391201761684610216456853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103188269015579480288609137 77391201761684610216456853)
                    ·
                      refine ⟨3627712582578966103896415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77391201761684610216456853 3627712582578966103896415)
                      ·
                        rfl

theorem cell23_7064945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_7064945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064945 prefixEnd_7064945 := by exact prefixLift 7064945
  have htrace : WordTrace (prefixWord ++ tailWord_7064945) baseStart_7064945 baseEnd_7064945 := by
    simpa [prefixWord, tailWord_7064945, baseEnd_7064945] using wordTrace_append hprefix tailTrace_7064945
  have hstable : (prefixWord ++ tailWord_7064945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064945).length < 2 ^ (prefixWord ++ tailWord_7064945).sum := by decide
  have hdescent : baseEnd_7064945 < baseStart_7064945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7064955 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 2, 7]
def baseStart_7064955 : Nat := 118140960795 + 7064955 * 2 ^ 59
def prefixEnd_7064955 : Nat := 4983230072969 + 3 ^ 40 * 7064955 * 2
def baseEnd_7064955 : Nat := 1209239239128503688257123

theorem tailTrace_7064955 : CollatzResearch.WordTrace tailWord_7064955 prefixEnd_7064955 1209239239128503688257123 := by
  unfold tailWord_7064955
  simp only [CollatzResearch.WordTrace]
  refine ⟨257680078119882108096916319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171786718746588072064610879 257680078119882108096916319)
  ·
    refine ⟨386520117179823162145374479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257680078119882108096916319 386520117179823162145374479)
    ·
      refine ⟨579780175769734743218061719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386520117179823162145374479 579780175769734743218061719)
      ·
        refine ⟨869670263654602114827092579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579780175769734743218061719 869670263654602114827092579)
        ·
          refine ⟨1304505395481903172240638869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869670263654602114827092579 1304505395481903172240638869)
          ·
            refine ⟨61148690413214211198779947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1304505395481903172240638869 61148690413214211198779947)
            ·
              refine ⟨91723035619821316798169921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61148690413214211198779947 91723035619821316798169921)
              ·
                refine ⟨68792276714865987598627441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91723035619821316798169921 68792276714865987598627441)
                ·
                  refine ⟨51594207536149490698970581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68792276714865987598627441 51594207536149490698970581)
                  ·
                    refine ⟨1209239239128503688257123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51594207536149490698970581 1209239239128503688257123)
                    ·
                      rfl

theorem cell23_7064955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_7064955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7064955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7064955 prefixEnd_7064955 := by exact prefixLift 7064955
  have htrace : WordTrace (prefixWord ++ tailWord_7064955) baseStart_7064955 baseEnd_7064955 := by
    simpa [prefixWord, tailWord_7064955, baseEnd_7064955] using wordTrace_append hprefix tailTrace_7064955
  have hstable : (prefixWord ++ tailWord_7064955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7064955).length < 2 ^ (prefixWord ++ tailWord_7064955).sum := by decide
  have hdescent : baseEnd_7064955 < baseStart_7064955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7064955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065013 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_7065013 : Nat := 118140960795 + 7065013 * 2 ^ 59
def prefixEnd_7065013 : Nat := 4983230072969 + 3 ^ 40 * 7065013 * 2
def baseEnd_7065013 : Nat := 3627747499263471837846103

theorem tailTrace_7065013 : CollatzResearch.WordTrace tailWord_7065013 prefixEnd_7065013 3627747499263471837846103 := by
  unfold tailWord_7065013
  simp only [CollatzResearch.WordTrace]
  refine ⟨257682193553671984002527693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171788129035781322668351795 257682193553671984002527693)
  ·
    refine ⟨96630822582626994000947885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257682193553671984002527693 96630822582626994000947885)
    ·
      refine ⟨36236558468485122750355457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96630822582626994000947885 36236558468485122750355457)
      ·
        refine ⟨27177418851363842062766593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36236558468485122750355457 27177418851363842062766593)
        ·
          refine ⟨20383064138522881547074945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27177418851363842062766593 20383064138522881547074945)
          ·
            refine ⟨15287298103892161160306209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20383064138522881547074945 15287298103892161160306209)
            ·
              refine ⟨11465473577919120870229657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15287298103892161160306209 11465473577919120870229657)
              ·
                refine ⟨8599105183439340652672243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11465473577919120870229657 8599105183439340652672243)
                ·
                  refine ⟨12898657775159010979008365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8599105183439340652672243 12898657775159010979008365)
                  ·
                    refine ⟨4836996665684629117128137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12898657775159010979008365 4836996665684629117128137)
                    ·
                      refine ⟨3627747499263471837846103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4836996665684629117128137 3627747499263471837846103)
                      ·
                        rfl

theorem cell23_7065013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_7065013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065013 prefixEnd_7065013 := by exact prefixLift 7065013
  have htrace : WordTrace (prefixWord ++ tailWord_7065013) baseStart_7065013 baseEnd_7065013 := by
    simpa [prefixWord, tailWord_7065013, baseEnd_7065013] using wordTrace_append hprefix tailTrace_7065013
  have hstable : (prefixWord ++ tailWord_7065013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065013).length < 2 ^ (prefixWord ++ tailWord_7065013).sum := by decide
  have hdescent : baseEnd_7065013 < baseStart_7065013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065049 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 7]
def baseStart_7065049 : Nat := 118140960795 + 7065049 * 2 ^ 59
def prefixEnd_7065049 : Nat := 4983230072969 + 3 ^ 40 * 7065049 * 2
def baseEnd_7065049 : Nat := 403085109396337077443993

theorem tailTrace_7065049 : CollatzResearch.WordTrace tailWord_7065049 prefixEnd_7065049 403085109396337077443993 := by
  unfold tailWord_7065049
  simp only [CollatzResearch.WordTrace]
  refine ⟨257683506581541562150838201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171789004387694374767225467 257683506581541562150838201)
  ·
    refine ⟨193262629936156171613128651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257683506581541562150838201 193262629936156171613128651)
    ·
      refine ⟨289893944904234257419692977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193262629936156171613128651 289893944904234257419692977)
      ·
        refine ⟨217420458678175693064769733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289893944904234257419692977 217420458678175693064769733)
        ·
          refine ⟨40766336002157942449644325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217420458678175693064769733 40766336002157942449644325)
          ·
            refine ⟨7643688000404614209308311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40766336002157942449644325 7643688000404614209308311)
            ·
              refine ⟨11465532000606921313962467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7643688000404614209308311 11465532000606921313962467)
              ·
                refine ⟨17198298000910381970943701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11465532000606921313962467 17198298000910381970943701)
                ·
                  refine ⟨403085109396337077443993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17198298000910381970943701 403085109396337077443993)
                  ·
                    rfl

theorem cell23_7065049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_7065049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065049 prefixEnd_7065049 := by exact prefixLift 7065049
  have htrace : WordTrace (prefixWord ++ tailWord_7065049) baseStart_7065049 baseEnd_7065049 := by
    simpa [prefixWord, tailWord_7065049, baseEnd_7065049] using wordTrace_append hprefix tailTrace_7065049
  have hstable : (prefixWord ++ tailWord_7065049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065049).length < 2 ^ (prefixWord ++ tailWord_7065049).sum := by decide
  have hdescent : baseEnd_7065049 < baseStart_7065049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065100 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 5]
def baseStart_7065100 : Nat := 118140960795 + 7065100 * 2 ^ 59
def prefixEnd_7065100 : Nat := 4983230072969 + 3 ^ 40 * 7065100 * 2
def baseEnd_7065100 : Nat := 403088019120045888606467

theorem tailTrace_7065100 : CollatzResearch.WordTrace tailWord_7065100 prefixEnd_7065100 403088019120045888606467 := by
  unfold tailWord_7065100
  simp only [CollatzResearch.WordTrace]
  refine ⟨128842683352178398930472377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171790244469571198573963169 128842683352178398930472377)
  ·
    refine ⟨96632012514133799197854283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128842683352178398930472377 96632012514133799197854283)
    ·
      refine ⟨144948018771200698796781425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96632012514133799197854283 144948018771200698796781425)
      ·
        refine ⟨108711014078400524097586069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144948018771200698796781425 108711014078400524097586069)
        ·
          refine ⟨5095828784925024567074347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108711014078400524097586069 5095828784925024567074347)
          ·
            refine ⟨7643743177387536850611521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095828784925024567074347 7643743177387536850611521)
            ·
              refine ⟨5732807383040652637958641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7643743177387536850611521 5732807383040652637958641)
              ·
                refine ⟨4299605537280489478468981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5732807383040652637958641 4299605537280489478468981)
                ·
                  refine ⟨403088019120045888606467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4299605537280489478468981 403088019120045888606467)
                  ·
                    rfl

theorem cell23_7065100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_7065100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065100 prefixEnd_7065100 := by exact prefixLift 7065100
  have htrace : WordTrace (prefixWord ++ tailWord_7065100) baseStart_7065100 baseEnd_7065100 := by
    simpa [prefixWord, tailWord_7065100, baseEnd_7065100] using wordTrace_append hprefix tailTrace_7065100
  have hstable : (prefixWord ++ tailWord_7065100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065100).length < 2 ^ (prefixWord ++ tailWord_7065100).sum := by decide
  have hdescent : baseEnd_7065100 < baseStart_7065100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065116 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_7065116 : Nat := 118140960795 + 7065116 * 2 ^ 59
def prefixEnd_7065116 : Nat := 4983230072969 + 3 ^ 40 * 7065116 * 2
def baseEnd_7065116 : Nat := 3627800387770884934858129

theorem tailTrace_7065116 : CollatzResearch.WordTrace tailWord_7065116 prefixEnd_7065116 3627800387770884934858129 := by
  unfold tailWord_7065116
  simp only [CollatzResearch.WordTrace]
  refine ⟨128842975136149416296763601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171790633514865888395684801 128842975136149416296763601)
  ·
    refine ⟨96632231352112062222572701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128842975136149416296763601 96632231352112062222572701)
    ·
      refine ⟨36237086757042023333464763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96632231352112062222572701 36237086757042023333464763)
      ·
        refine ⟨54355630135563035000197145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36237086757042023333464763 54355630135563035000197145)
        ·
          refine ⟨40766722601672276250147859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54355630135563035000197145 40766722601672276250147859)
          ·
            refine ⟨61150083902508414375221789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40766722601672276250147859 61150083902508414375221789)
            ·
              refine ⟨22931281463440655390708171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61150083902508414375221789 22931281463440655390708171)
              ·
                refine ⟨34396922195160983086062257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22931281463440655390708171 34396922195160983086062257)
                ·
                  refine ⟨25797691646370737314546693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34396922195160983086062257 25797691646370737314546693)
                  ·
                    refine ⟨4837067183694513246477505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25797691646370737314546693 4837067183694513246477505)
                    ·
                      refine ⟨3627800387770884934858129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837067183694513246477505 3627800387770884934858129)
                      ·
                        rfl

theorem cell23_7065116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_7065116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065116 prefixEnd_7065116 := by exact prefixLift 7065116
  have htrace : WordTrace (prefixWord ++ tailWord_7065116) baseStart_7065116 baseEnd_7065116 := by
    simpa [prefixWord, tailWord_7065116, baseEnd_7065116] using wordTrace_append hprefix tailTrace_7065116
  have hstable : (prefixWord ++ tailWord_7065116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065116).length < 2 ^ (prefixWord ++ tailWord_7065116).sum := by decide
  have hdescent : baseEnd_7065116 < baseStart_7065116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065119 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_7065119 : Nat := 118140960795 + 7065119 * 2 ^ 59
def prefixEnd_7065119 : Nat := 4983230072969 + 3 ^ 40 * 7065119 * 2
def baseEnd_7065119 : Nat := 3627801928212848423120615

theorem tailTrace_7065119 : CollatzResearch.WordTrace tailWord_7065119 prefixEnd_7065119 3627801928212848423120615 := by
  unfold tailWord_7065119
  simp only [CollatzResearch.WordTrace]
  refine ⟨257686059691287964105886411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171790706460858642737257607 257686059691287964105886411)
  ·
    refine ⟨386529089536931946158829617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257686059691287964105886411 386529089536931946158829617)
    ·
      refine ⟨289896817152698959619122213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386529089536931946158829617 289896817152698959619122213)
      ·
        refine ⟨54355653216131054928585415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289896817152698959619122213 54355653216131054928585415)
        ·
          refine ⟨81533479824196582392878123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54355653216131054928585415 81533479824196582392878123)
          ·
            refine ⟨122300219736294873589317185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81533479824196582392878123 122300219736294873589317185)
            ·
              refine ⟨91725164802221155191987889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122300219736294873589317185 91725164802221155191987889)
              ·
                refine ⟨68793873601665866393990917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91725164802221155191987889 68793873601665866393990917)
                ·
                  refine ⟨12898851300312349948873297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68793873601665866393990917 12898851300312349948873297)
                  ·
                    refine ⟨9674138475234262461654973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12898851300312349948873297 9674138475234262461654973)
                    ·
                      refine ⟨3627801928212848423120615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674138475234262461654973 3627801928212848423120615)
                      ·
                        rfl

theorem cell23_7065119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_7065119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065119 prefixEnd_7065119 := by exact prefixLift 7065119
  have htrace : WordTrace (prefixWord ++ tailWord_7065119) baseStart_7065119 baseEnd_7065119 := by
    simpa [prefixWord, tailWord_7065119, baseEnd_7065119] using wordTrace_append hprefix tailTrace_7065119
  have hstable : (prefixWord ++ tailWord_7065119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065119).length < 2 ^ (prefixWord ++ tailWord_7065119).sum := by decide
  have hdescent : baseEnd_7065119 < baseStart_7065119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065143 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 1, 4]
def baseStart_7065143 : Nat := 118140960795 + 7065143 * 2 ^ 59
def prefixEnd_7065143 : Nat := 4983230072969 + 3 ^ 40 * 7065143 * 2
def baseEnd_7065143 : Nat := 1209271417249518776406835

theorem tailTrace_7065143 : CollatzResearch.WordTrace tailWord_7065143 prefixEnd_7065143 1209271417249518776406835 := by
  unfold tailWord_7065143
  simp only [CollatzResearch.WordTrace]
  refine ⟨257686935043201016204760083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171791290028800677469840055 257686935043201016204760083)
  ·
    refine ⟨386530402564801524307140125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257686935043201016204760083 386530402564801524307140125)
    ·
      refine ⟨144948900961800571615177547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386530402564801524307140125 144948900961800571615177547)
      ·
        refine ⟨217423351442700857422766321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144948900961800571615177547 217423351442700857422766321)
        ·
          refine ⟨163067513582025643067074741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217423351442700857422766321 163067513582025643067074741)
          ·
            refine ⟨15287579398314904037538257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163067513582025643067074741 15287579398314904037538257)
            ·
              refine ⟨11465684548736178028153693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15287579398314904037538257 11465684548736178028153693)
              ·
                refine ⟨4299631705776066760557635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11465684548736178028153693 4299631705776066760557635)
                ·
                  refine ⟨6449447558664100140836453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299631705776066760557635 6449447558664100140836453)
                  ·
                    refine ⟨1209271417249518776406835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6449447558664100140836453 1209271417249518776406835)
                    ·
                      rfl

theorem cell23_7065143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_7065143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065143 prefixEnd_7065143 := by exact prefixLift 7065143
  have htrace : WordTrace (prefixWord ++ tailWord_7065143) baseStart_7065143 baseEnd_7065143 := by
    simpa [prefixWord, tailWord_7065143, baseEnd_7065143] using wordTrace_append hprefix tailTrace_7065143
  have hstable : (prefixWord ++ tailWord_7065143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065143).length < 2 ^ (prefixWord ++ tailWord_7065143).sum := by decide
  have hdescent : baseEnd_7065143 < baseStart_7065143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065200 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 1, 1, 3]
def baseStart_7065200 : Nat := 118140960795 + 7065200 * 2 ^ 59
def prefixEnd_7065200 : Nat := 4983230072969 + 3 ^ 40 * 7065200 * 2
def baseEnd_7065200 : Nat := 3627843520145862606207743

theorem tailTrace_7065200 : CollatzResearch.WordTrace tailWord_7065200 prefixEnd_7065200 3627843520145862606207743 := by
  unfold tailWord_7065200
  simp only [CollatzResearch.WordTrace]
  refine ⟨128844507001997257469792527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171792676002663009959723369 128844507001997257469792527)
  ·
    refine ⟨193266760502995886204688791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128844507001997257469792527 193266760502995886204688791)
    ·
      refine ⟨289900140754493829307033187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193266760502995886204688791 289900140754493829307033187)
      ·
        refine ⟨434850211131740743960549781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289900140754493829307033187 434850211131740743960549781)
        ·
          refine ⟨20383603646800347373150771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 434850211131740743960549781 20383603646800347373150771)
          ·
            refine ⟨30575405470200521059726157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20383603646800347373150771 30575405470200521059726157)
            ·
              refine ⟨11465777051325195397397309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30575405470200521059726157 11465777051325195397397309)
              ·
                refine ⟨4299666394246948274023991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11465777051325195397397309 4299666394246948274023991)
                ·
                  refine ⟨6449499591370422411035987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299666394246948274023991 6449499591370422411035987)
                  ·
                    refine ⟨9674249387055633616553981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6449499591370422411035987 9674249387055633616553981)
                    ·
                      refine ⟨3627843520145862606207743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674249387055633616553981 3627843520145862606207743)
                      ·
                        rfl

theorem cell23_7065200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 1, 3].length) (baseStart_7065200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065200 prefixEnd_7065200 := by exact prefixLift 7065200
  have htrace : WordTrace (prefixWord ++ tailWord_7065200) baseStart_7065200 baseEnd_7065200 := by
    simpa [prefixWord, tailWord_7065200, baseEnd_7065200] using wordTrace_append hprefix tailTrace_7065200
  have hstable : (prefixWord ++ tailWord_7065200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065200).length < 2 ^ (prefixWord ++ tailWord_7065200).sum := by decide
  have hdescent : baseEnd_7065200 < baseStart_7065200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065216 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 2, 4]
def baseStart_7065216 : Nat := 118140960795 + 7065216 * 2 ^ 59
def prefixEnd_7065216 : Nat := 4983230072969 + 3 ^ 40 * 7065216 * 2
def baseEnd_7065216 : Nat := 1209283911945444847869223

theorem tailTrace_7065216 : CollatzResearch.WordTrace tailWord_7065216 prefixEnd_7065216 1209283911945444847869223 := by
  unfold tailWord_7065216
  simp only [CollatzResearch.WordTrace]
  refine ⟨128844798785968274836083751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171793065047957699781445001 128844798785968274836083751)
  ·
    refine ⟨193267198178952412254125627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128844798785968274836083751 193267198178952412254125627)
    ·
      refine ⟨289900797268428618381188441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193267198178952412254125627 289900797268428618381188441)
      ·
        refine ⟨217425597951321463785891331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289900797268428618381188441 217425597951321463785891331)
        ·
          refine ⟨326138396926982195678836997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217425597951321463785891331 326138396926982195678836997)
          ·
            refine ⟨61150949423809161689781937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326138396926982195678836997 61150949423809161689781937)
            ·
              refine ⟨45863212067856871267336453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61150949423809161689781937 45863212067856871267336453)
              ·
                refine ⟨8599352262723163362625585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45863212067856871267336453 8599352262723163362625585)
                ·
                  refine ⟨6449514197042372521969189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599352262723163362625585 6449514197042372521969189)
                  ·
                    refine ⟨1209283911945444847869223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6449514197042372521969189 1209283911945444847869223)
                    ·
                      rfl

theorem cell23_7065216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_7065216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065216 prefixEnd_7065216 := by exact prefixLift 7065216
  have htrace : WordTrace (prefixWord ++ tailWord_7065216) baseStart_7065216 baseEnd_7065216 := by
    simpa [prefixWord, tailWord_7065216, baseEnd_7065216] using wordTrace_append hprefix tailTrace_7065216
  have hstable : (prefixWord ++ tailWord_7065216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065216).length < 2 ^ (prefixWord ++ tailWord_7065216).sum := by decide
  have hdescent : baseEnd_7065216 < baseStart_7065216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065217 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_7065217 : Nat := 118140960795 + 7065217 * 2 ^ 59
def prefixEnd_7065217 : Nat := 4983230072969 + 3 ^ 40 * 7065217 * 2
def baseEnd_7065217 : Nat := 3627852249316989039695165

theorem tailTrace_7065217 : CollatzResearch.WordTrace tailWord_7065217 prefixEnd_7065217 3627852249316989039695165 := by
  unfold tailWord_7065217
  simp only [CollatzResearch.WordTrace]
  refine ⟨257689634044932926842953905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171793089363288617895302603 257689634044932926842953905)
  ·
    refine ⟨193267225533699695132215429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257689634044932926842953905 193267225533699695132215429)
    ·
      refine ⟨36237604787568692837290393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193267225533699695132215429 36237604787568692837290393)
      ·
        refine ⟨27178203590676519627967795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36237604787568692837290393 27178203590676519627967795)
        ·
          refine ⟨40767305386014779441951693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27178203590676519627967795 40767305386014779441951693)
          ·
            refine ⟨15287739519755542290731885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40767305386014779441951693 15287739519755542290731885)
            ·
              refine ⟨5732902319908328359024457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15287739519755542290731885 5732902319908328359024457)
              ·
                refine ⟨4299676739931246269268343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5732902319908328359024457 4299676739931246269268343)
                ·
                  refine ⟨6449515109896869403902515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299676739931246269268343 6449515109896869403902515)
                  ·
                    refine ⟨9674272664845304105853773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6449515109896869403902515 9674272664845304105853773)
                    ·
                      refine ⟨3627852249316989039695165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674272664845304105853773 3627852249316989039695165)
                      ·
                        rfl

theorem cell23_7065217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_7065217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065217 prefixEnd_7065217 := by exact prefixLift 7065217
  have htrace : WordTrace (prefixWord ++ tailWord_7065217) baseStart_7065217 baseEnd_7065217 := by
    simpa [prefixWord, tailWord_7065217, baseEnd_7065217] using wordTrace_append hprefix tailTrace_7065217
  have hstable : (prefixWord ++ tailWord_7065217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065217).length < 2 ^ (prefixWord ++ tailWord_7065217).sum := by decide
  have hdescent : baseEnd_7065217 < baseStart_7065217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065226 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7065226 : Nat := 118140960795 + 7065226 * 2 ^ 59
def prefixEnd_7065226 : Nat := 4983230072969 + 3 ^ 40 * 7065226 * 2
def baseEnd_7065226 : Nat := 3627856870642879504482623

theorem tailTrace_7065226 : CollatzResearch.WordTrace tailWord_7065226 prefixEnd_7065226 3627856870642879504482623 := by
  unfold tailWord_7065226
  simp only [CollatzResearch.WordTrace]
  refine ⟨64422490575475080345007883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171793308201266880920021021 64422490575475080345007883)
  ·
    refine ⟨96633735863212620517511825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64422490575475080345007883 96633735863212620517511825)
    ·
      refine ⟨72475301897409465388133869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96633735863212620517511825 72475301897409465388133869)
      ·
        refine ⟨27178238211528549520550201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72475301897409465388133869 27178238211528549520550201)
        ·
          refine ⟨20383678658646412140412651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27178238211528549520550201 20383678658646412140412651)
          ·
            refine ⟨30575517987969618210618977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20383678658646412140412651 30575517987969618210618977)
            ·
              refine ⟨22931638490977213657964233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30575517987969618210618977 22931638490977213657964233)
              ·
                refine ⟨17198728868232910243473175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22931638490977213657964233 17198728868232910243473175)
                ·
                  refine ⟨25798093302349365365209763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17198728868232910243473175 25798093302349365365209763)
                  ·
                    refine ⟨38697139953524048047814645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25798093302349365365209763 38697139953524048047814645)
                    ·
                      refine ⟨3627856870642879504482623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38697139953524048047814645 3627856870642879504482623)
                      ·
                        rfl

theorem cell23_7065226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7065226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065226 prefixEnd_7065226 := by exact prefixLift 7065226
  have htrace : WordTrace (prefixWord ++ tailWord_7065226) baseStart_7065226 baseEnd_7065226 := by
    simpa [prefixWord, tailWord_7065226, baseEnd_7065226] using wordTrace_append hprefix tailTrace_7065226
  have hstable : (prefixWord ++ tailWord_7065226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065226).length < 2 ^ (prefixWord ++ tailWord_7065226).sum := by decide
  have hdescent : baseEnd_7065226 < baseStart_7065226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065246 : List Nat := [4, 3, 1, 1, 1, 2, 2, 9]
def baseStart_7065246 : Nat := 118140960795 + 7065246 * 2 ^ 59
def prefixEnd_7065246 : Nat := 4983230072969 + 3 ^ 40 * 7065246 * 2
def baseEnd_7065246 : Nat := 134365449639109978749353

theorem tailTrace_7065246 : CollatzResearch.WordTrace tailWord_7065246 prefixEnd_7065246 134365449639109978749353 := by
  unfold tailWord_7065246
  simp only [CollatzResearch.WordTrace]
  refine ⟨32211336470228483099469949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171793794507885243197173061 32211336470228483099469949)
  ·
    refine ⟨12079251176335681162301231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32211336470228483099469949 12079251176335681162301231)
    ·
      refine ⟨18118876764503521743451847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12079251176335681162301231 18118876764503521743451847)
      ·
        refine ⟨27178315146755282615177771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18118876764503521743451847 27178315146755282615177771)
        ·
          refine ⟨40767472720132923922766657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27178315146755282615177771 40767472720132923922766657)
          ·
            refine ⟨30575604540099692942074993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40767472720132923922766657 30575604540099692942074993)
            ·
              refine ⟨22931703405074769706556245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30575604540099692942074993 22931703405074769706556245)
              ·
                refine ⟨134365449639109978749353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22931703405074769706556245 134365449639109978749353)
                ·
                  rfl

theorem cell23_7065246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_7065246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065246 prefixEnd_7065246 := by exact prefixLift 7065246
  have htrace : WordTrace (prefixWord ++ tailWord_7065246) baseStart_7065246 baseEnd_7065246 := by
    simpa [prefixWord, tailWord_7065246, baseEnd_7065246] using wordTrace_append hprefix tailTrace_7065246
  have hstable : (prefixWord ++ tailWord_7065246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065246).length < 2 ^ (prefixWord ++ tailWord_7065246).sum := by decide
  have hdescent : baseEnd_7065246 < baseStart_7065246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065273 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 3]
def baseStart_7065273 : Nat := 118140960795 + 7065273 * 2 ^ 59
def prefixEnd_7065273 : Nat := 4983230072969 + 3 ^ 40 * 7065273 * 2
def baseEnd_7065273 : Nat := 3627881004233640820594907

theorem tailTrace_7065273 : CollatzResearch.WordTrace tailWord_7065273 prefixEnd_7065273 3627881004233640820594907 := by
  unfold tailWord_7065273
  simp only [CollatzResearch.WordTrace]
  refine ⟨257691676532730048406992473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171794451021820032271328315 257691676532730048406992473)
  ·
    refine ⟨193268757399547536305244355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257691676532730048406992473 193268757399547536305244355)
    ·
      refine ⟨289903136099321304457866533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193268757399547536305244355 289903136099321304457866533)
      ·
        refine ⟨54356838018622744585849975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289903136099321304457866533 54356838018622744585849975)
        ·
          refine ⟨81535257027934116878774963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54356838018622744585849975 81535257027934116878774963)
          ·
            refine ⟨122302885541901175318162445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81535257027934116878774963 122302885541901175318162445)
            ·
              refine ⟨45863582078212940744310917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122302885541901175318162445 45863582078212940744310917)
              ·
                refine ⟨8599421639664926389558297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45863582078212940744310917 8599421639664926389558297)
                ·
                  refine ⟨6449566229748694792168723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599421639664926389558297 6449566229748694792168723)
                  ·
                    refine ⟨9674349344623042188253085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6449566229748694792168723 9674349344623042188253085)
                    ·
                      refine ⟨3627881004233640820594907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674349344623042188253085 3627881004233640820594907)
                      ·
                        rfl

theorem cell23_7065273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_7065273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065273 prefixEnd_7065273 := by exact prefixLift 7065273
  have htrace : WordTrace (prefixWord ++ tailWord_7065273) baseStart_7065273 baseEnd_7065273 := by
    simpa [prefixWord, tailWord_7065273, baseEnd_7065273] using wordTrace_append hprefix tailTrace_7065273
  have hstable : (prefixWord ++ tailWord_7065273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065273).length < 2 ^ (prefixWord ++ tailWord_7065273).sum := by decide
  have hdescent : baseEnd_7065273 < baseStart_7065273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065274 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2]
def baseStart_7065274 : Nat := 118140960795 + 7065274 * 2 ^ 59
def prefixEnd_7065274 : Nat := 4983230072969 + 3 ^ 40 * 7065274 * 2
def baseEnd_7065274 : Nat := 3627881517714295316682403

theorem tailTrace_7065274 : CollatzResearch.WordTrace tailWord_7065274 prefixEnd_7065274 3627881517714295316682403 := by
  unfold tailWord_7065274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64422928251431606394444719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171794475337150950385185917 64422928251431606394444719)
  ·
    refine ⟨96634392377147409591667079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64422928251431606394444719 96634392377147409591667079)
    ·
      refine ⟨144951588565721114387500619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96634392377147409591667079 144951588565721114387500619)
      ·
        refine ⟨217427382848581671581250929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144951588565721114387500619 217427382848581671581250929)
        ·
          refine ⟨163070537136436253685938197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217427382848581671581250929 163070537136436253685938197)
          ·
            refine ⟨7643931428270449391528353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163070537136436253685938197 7643931428270449391528353)
            ·
              refine ⟨5732948571202837043646265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7643931428270449391528353 5732948571202837043646265)
              ·
                refine ⟨4299711428402127782734699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5732948571202837043646265 4299711428402127782734699)
                ·
                  refine ⟨6449567142603191674102049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299711428402127782734699 6449567142603191674102049)
                  ·
                    refine ⟨4837175356952393755576537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6449567142603191674102049 4837175356952393755576537)
                    ·
                      refine ⟨3627881517714295316682403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837175356952393755576537 3627881517714295316682403)
                      ·
                        rfl

theorem cell23_7065274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_7065274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065274 prefixEnd_7065274 := by exact prefixLift 7065274
  have htrace : WordTrace (prefixWord ++ tailWord_7065274) baseStart_7065274 baseEnd_7065274 := by
    simpa [prefixWord, tailWord_7065274, baseEnd_7065274] using wordTrace_append hprefix tailTrace_7065274
  have hstable : (prefixWord ++ tailWord_7065274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065274).length < 2 ^ (prefixWord ++ tailWord_7065274).sum := by decide
  have hdescent : baseEnd_7065274 < baseStart_7065274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065279 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_7065279 : Nat := 118140960795 + 7065279 * 2 ^ 59
def prefixEnd_7065279 : Nat := 4983230072969 + 3 ^ 40 * 7065279 * 2
def baseEnd_7065279 : Nat := 3627884085117567797119879

theorem tailTrace_7065279 : CollatzResearch.WordTrace tailWord_7065279 prefixEnd_7065279 3627884085117567797119879 := by
  unfold tailWord_7065279
  simp only [CollatzResearch.WordTrace]
  refine ⟨257691895370708311431710891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171794596913805540954473927 257691895370708311431710891)
  ·
    refine ⟨386537843056062467147566337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257691895370708311431710891 386537843056062467147566337)
    ·
      refine ⟨289903382292046850360674753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386537843056062467147566337 289903382292046850360674753)
      ·
        refine ⟨217427536719035137770506065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289903382292046850360674753 217427536719035137770506065)
        ·
          refine ⟨163070652539276353327879549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217427536719035137770506065 163070652539276353327879549)
          ·
            refine ⟨61151494702228632497954831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163070652539276353327879549 61151494702228632497954831)
            ·
              refine ⟨91727242053342948746932247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61151494702228632497954831 91727242053342948746932247)
              ·
                refine ⟨137590863080014423120398371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91727242053342948746932247 137590863080014423120398371)
                ·
                  refine ⟨206386294620021634680597557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137590863080014423120398371 206386294620021634680597557)
                  ·
                    refine ⟨19348715120627028251306021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 206386294620021634680597557 19348715120627028251306021)
                    ·
                      refine ⟨3627884085117567797119879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19348715120627028251306021 3627884085117567797119879)
                      ·
                        rfl

theorem cell23_7065279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_7065279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065279 prefixEnd_7065279 := by exact prefixLift 7065279
  have htrace : WordTrace (prefixWord ++ tailWord_7065279) baseStart_7065279 baseEnd_7065279 := by
    simpa [prefixWord, tailWord_7065279, baseEnd_7065279] using wordTrace_append hprefix tailTrace_7065279
  have hstable : (prefixWord ++ tailWord_7065279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065279).length < 2 ^ (prefixWord ++ tailWord_7065279).sum := by decide
  have hdescent : baseEnd_7065279 < baseStart_7065279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065300 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7065300 : Nat := 118140960795 + 7065300 * 2 ^ 59
def prefixEnd_7065300 : Nat := 4983230072969 + 3 ^ 40 * 7065300 * 2
def baseEnd_7065300 : Nat := 3627894868211312214957283

theorem tailTrace_7065300 : CollatzResearch.WordTrace tailWord_7065300 prefixEnd_7065300 3627894868211312214957283 := by
  unfold tailWord_7065300
  simp only [CollatzResearch.WordTrace]
  refine ⟨128846330651816116009112677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171795107535754821345483569 128846330651816116009112677)
  ·
    refine ⟨24158686997215521751708627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128846330651816116009112677 24158686997215521751708627)
    ·
      refine ⟨36238030495823282627562941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24158686997215521751708627 36238030495823282627562941)
      ·
        refine ⟨13589261435933730985336103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36238030495823282627562941 13589261435933730985336103)
        ·
          refine ⟨20383892153900596478004155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13589261435933730985336103 20383892153900596478004155)
          ·
            refine ⟨30575838230850894717006233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20383892153900596478004155 30575838230850894717006233)
            ·
              refine ⟨22931878673138171037754675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30575838230850894717006233 22931878673138171037754675)
              ·
                refine ⟨34397818009707256556632013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22931878673138171037754675 34397818009707256556632013)
                ·
                  refine ⟨12899181753640221208737005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34397818009707256556632013 12899181753640221208737005)
                  ·
                    refine ⟨4837193157615082953276377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12899181753640221208737005 4837193157615082953276377)
                    ·
                      refine ⟨3627894868211312214957283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837193157615082953276377 3627894868211312214957283)
                      ·
                        rfl

theorem cell23_7065300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7065300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065300 prefixEnd_7065300 := by exact prefixLift 7065300
  have htrace : WordTrace (prefixWord ++ tailWord_7065300) baseStart_7065300 baseEnd_7065300 := by
    simpa [prefixWord, tailWord_7065300, baseEnd_7065300] using wordTrace_append hprefix tailTrace_7065300
  have hstable : (prefixWord ++ tailWord_7065300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065300).length < 2 ^ (prefixWord ++ tailWord_7065300).sum := by decide
  have hdescent : baseEnd_7065300 < baseStart_7065300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065326 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7065326 : Nat := 118140960795 + 7065326 * 2 ^ 59
def prefixEnd_7065326 : Nat := 4983230072969 + 3 ^ 40 * 7065326 * 2
def baseEnd_7065326 : Nat := 3627908218708329113232163

theorem tailTrace_7065326 : CollatzResearch.WordTrace tailWord_7065326 prefixEnd_7065326 3627908218708329113232163 := by
  unfold tailWord_7065326
  simp only [CollatzResearch.WordTrace]
  refine ⟨32211701200192254807333979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171795739734358692305781221 32211701200192254807333979)
  ·
    refine ⟨48317551800288382211000969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32211701200192254807333979 48317551800288382211000969)
    ·
      refine ⟨36238163850216286658250727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48317551800288382211000969 36238163850216286658250727)
      ·
        refine ⟨54357245775324429987376091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36238163850216286658250727 54357245775324429987376091)
        ·
          refine ⟨81535868662986644981064137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54357245775324429987376091 81535868662986644981064137)
          ·
            refine ⟨61151901497239983735798103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81535868662986644981064137 61151901497239983735798103)
            ·
              refine ⟨91727852245859975603697155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61151901497239983735798103 91727852245859975603697155)
              ·
                refine ⟨137591778368789963405545733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91727852245859975603697155 137591778368789963405545733)
                ·
                  refine ⟨25798458444148118138539825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137591778368789963405545733 25798458444148118138539825)
                  ·
                    refine ⟨19348843833111088603904869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25798458444148118138539825 19348843833111088603904869)
                    ·
                      refine ⟨3627908218708329113232163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19348843833111088603904869 3627908218708329113232163)
                      ·
                        rfl

theorem cell23_7065326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7065326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065326 prefixEnd_7065326 := by exact prefixLift 7065326
  have htrace : WordTrace (prefixWord ++ tailWord_7065326) baseStart_7065326 baseEnd_7065326 := by
    simpa [prefixWord, tailWord_7065326, baseEnd_7065326] using wordTrace_append hprefix tailTrace_7065326
  have hstable : (prefixWord ++ tailWord_7065326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065326).length < 2 ^ (prefixWord ++ tailWord_7065326).sum := by decide
  have hdescent : baseEnd_7065326 < baseStart_7065326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065330 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7065330 : Nat := 118140960795 + 7065330 * 2 ^ 59
def prefixEnd_7065330 : Nat := 4983230072969 + 3 ^ 40 * 7065330 * 2
def baseEnd_7065330 : Nat := 3627910272630947097582145

theorem tailTrace_7065330 : CollatzResearch.WordTrace tailWord_7065330 prefixEnd_7065330 3627910272630947097582145 := by
  unfold tailWord_7065330
  simp only [CollatzResearch.WordTrace]
  refine ⟨64423438873380886785454361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171795836995682364761211629 64423438873380886785454361)
  ·
    refine ⟨48317579155035665089090771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64423438873380886785454361 48317579155035665089090771)
    ·
      refine ⟨72476368732553497633636157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48317579155035665089090771 72476368732553497633636157)
      ·
        refine ⟨27178638274707561612613559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72476368732553497633636157 27178638274707561612613559)
        ·
          refine ⟨40767957412061342418920339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27178638274707561612613559 40767957412061342418920339)
          ·
            refine ⟨61151936118092013628380509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40767957412061342418920339 61151936118092013628380509)
            ·
              refine ⟨22931976044284505110642691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61151936118092013628380509 22931976044284505110642691)
              ·
                refine ⟨34397964066426757665964037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22931976044284505110642691 34397964066426757665964037)
                ·
                  refine ⟨6449618262455017062368257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34397964066426757665964037 6449618262455017062368257)
                  ·
                    refine ⟨4837213696841262796776193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6449618262455017062368257 4837213696841262796776193)
                    ·
                      refine ⟨3627910272630947097582145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837213696841262796776193 3627910272630947097582145)
                      ·
                        rfl

theorem cell23_7065330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7065330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065330 prefixEnd_7065330 := by exact prefixLift 7065330
  have htrace : WordTrace (prefixWord ++ tailWord_7065330) baseStart_7065330 baseEnd_7065330 := by
    simpa [prefixWord, tailWord_7065330, baseEnd_7065330] using wordTrace_append hprefix tailTrace_7065330
  have hstable : (prefixWord ++ tailWord_7065330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065330).length < 2 ^ (prefixWord ++ tailWord_7065330).sum := by decide
  have hdescent : baseEnd_7065330 < baseStart_7065330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065359 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_7065359 : Nat := 118140960795 + 7065359 * 2 ^ 59
def prefixEnd_7065359 : Nat := 4983230072969 + 3 ^ 40 * 7065359 * 2
def baseEnd_7065359 : Nat := 3627925163569927484119511

theorem tailTrace_7065359 : CollatzResearch.WordTrace tailWord_7065359 prefixEnd_7065359 3627925163569927484119511 := by
  unfold tailWord_7065359
  simp only [CollatzResearch.WordTrace]
  refine ⟨257694813210418485094623131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171796542140278990063082087 257694813210418485094623131)
  ·
    refine ⟨386542219815627727641934697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257694813210418485094623131 386542219815627727641934697)
    ·
      refine ⟨289906664861720795731451023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386542219815627727641934697 289906664861720795731451023)
      ·
        refine ⟨434859997292581193597176535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289906664861720795731451023 434859997292581193597176535)
        ·
          refine ⟨652289995938871790395764803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434859997292581193597176535 652289995938871790395764803)
          ·
            refine ⟨978434993908307685593647205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652289995938871790395764803 978434993908307685593647205)
            ·
              refine ⟨183456561357807691048808851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 978434993908307685593647205 183456561357807691048808851)
              ·
                refine ⟨275184842036711536573213277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183456561357807691048808851 275184842036711536573213277)
                ·
                  refine ⟨103194315763766826214954979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275184842036711536573213277 103194315763766826214954979)
                  ·
                    refine ⟨154791473645650239322432469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103194315763766826214954979 154791473645650239322432469)
                    ·
                      refine ⟨3627925163569927484119511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154791473645650239322432469 3627925163569927484119511)
                      ·
                        rfl

theorem cell23_7065359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_7065359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065359 prefixEnd_7065359 := by exact prefixLift 7065359
  have htrace : WordTrace (prefixWord ++ tailWord_7065359) baseStart_7065359 baseEnd_7065359 := by
    simpa [prefixWord, tailWord_7065359, baseEnd_7065359] using wordTrace_append hprefix tailTrace_7065359
  have hstable : (prefixWord ++ tailWord_7065359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065359).length < 2 ^ (prefixWord ++ tailWord_7065359).sum := by decide
  have hdescent : baseEnd_7065359 < baseStart_7065359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065369 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_7065369 : Nat := 118140960795 + 7065369 * 2 ^ 59
def prefixEnd_7065369 : Nat := 4983230072969 + 3 ^ 40 * 7065369 * 2
def baseEnd_7065369 : Nat := 3627930298376472444994465

theorem tailTrace_7065369 : CollatzResearch.WordTrace tailWord_7065369 prefixEnd_7065369 3627930298376472444994465 := by
  unfold tailWord_7065369
  simp only [CollatzResearch.WordTrace]
  refine ⟨257695177940382256802487161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171796785293588171201658107 257695177940382256802487161)
  ·
    refine ⟨193271383455286692601865371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257695177940382256802487161 193271383455286692601865371)
    ·
      refine ⟨289907075182930038902798057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193271383455286692601865371 289907075182930038902798057)
      ·
        refine ⟨217430306387197529177098543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289907075182930038902798057 217430306387197529177098543)
        ·
          refine ⟨326145459580796293765647815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217430306387197529177098543 326145459580796293765647815)
          ·
            refine ⟨489218189371194440648471723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326145459580796293765647815 489218189371194440648471723)
            ·
              refine ⟨733827284056791660972707585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489218189371194440648471723 733827284056791660972707585)
              ·
                refine ⟨550370463042593745729530689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733827284056791660972707585 550370463042593745729530689)
                ·
                  refine ⟨412777847281945309297148017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550370463042593745729530689 412777847281945309297148017)
                  ·
                    refine ⟨309583385461458981972861013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 412777847281945309297148017 309583385461458981972861013)
                    ·
                      refine ⟨3627930298376472444994465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 309583385461458981972861013 3627930298376472444994465)
                      ·
                        rfl

theorem cell23_7065369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_7065369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065369 prefixEnd_7065369 := by exact prefixLift 7065369
  have htrace : WordTrace (prefixWord ++ tailWord_7065369) baseStart_7065369 baseEnd_7065369 := by
    simpa [prefixWord, tailWord_7065369, baseEnd_7065369] using wordTrace_append hprefix tailTrace_7065369
  have hstable : (prefixWord ++ tailWord_7065369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065369).length < 2 ^ (prefixWord ++ tailWord_7065369).sum := by decide
  have hdescent : baseEnd_7065369 < baseStart_7065369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065370 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_7065370 : Nat := 118140960795 + 7065370 * 2 ^ 59
def prefixEnd_7065370 : Nat := 4983230072969 + 3 ^ 40 * 7065370 * 2
def baseEnd_7065370 : Nat := 403103423539680771231329

theorem tailTrace_7065370 : CollatzResearch.WordTrace tailWord_7065370 prefixEnd_7065370 403103423539680771231329 := by
  unfold tailWord_7065370
  simp only [CollatzResearch.WordTrace]
  refine ⟨64423803603344658493318391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171796809608919089315515709 64423803603344658493318391)
  ·
    refine ⟨96635705405016987739977587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64423803603344658493318391 96635705405016987739977587)
    ·
      refine ⟨144953558107525481609966381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96635705405016987739977587 144953558107525481609966381)
      ·
        refine ⟨54357584290322055603737393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144953558107525481609966381 54357584290322055603737393)
        ·
          refine ⟨40768188217741541702803045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54357584290322055603737393 40768188217741541702803045)
          ·
            refine ⟨7644035290826539069275571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40768188217741541702803045 7644035290826539069275571)
            ·
              refine ⟨11466052936239808603913357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644035290826539069275571 11466052936239808603913357)
              ·
                refine ⟨4299769851089928226467509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11466052936239808603913357 4299769851089928226467509)
                ·
                  refine ⟨403103423539680771231329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4299769851089928226467509 403103423539680771231329)
                  ·
                    rfl

theorem cell23_7065370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_7065370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065370 prefixEnd_7065370 := by exact prefixLift 7065370
  have htrace : WordTrace (prefixWord ++ tailWord_7065370) baseStart_7065370 baseEnd_7065370 := by
    simpa [prefixWord, tailWord_7065370, baseEnd_7065370] using wordTrace_append hprefix tailTrace_7065370
  have hstable : (prefixWord ++ tailWord_7065370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065370).length < 2 ^ (prefixWord ++ tailWord_7065370).sum := by decide
  have hdescent : baseEnd_7065370 < baseStart_7065370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065376 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7065376 : Nat := 118140960795 + 7065376 * 2 ^ 59
def prefixEnd_7065376 : Nat := 4983230072969 + 3 ^ 40 * 7065376 * 2
def baseEnd_7065376 : Nat := 3627933892741053917606933

theorem tailTrace_7065376 : CollatzResearch.WordTrace tailWord_7065376 prefixEnd_7065376 3627933892741053917606933 := by
  unfold tailWord_7065376
  simp only [CollatzResearch.WordTrace]
  refine ⟨128847716625678448498995991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171796955500904597998661321 128847716625678448498995991)
  ·
    refine ⟨193271574938517672748493987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128847716625678448498995991 193271574938517672748493987)
    ·
      refine ⟨289907362407776509122740981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193271574938517672748493987 289907362407776509122740981)
      ·
        refine ⟨27178815225729047730256967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289907362407776509122740981 27178815225729047730256967)
        ·
          refine ⟨40768222838593571595385451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27178815225729047730256967 40768222838593571595385451)
          ·
            refine ⟨61152334257890357393078177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40768222838593571595385451 61152334257890357393078177)
            ·
              refine ⟨45864250693417768044808633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61152334257890357393078177 45864250693417768044808633)
              ·
                refine ⟨34398188020063326033606475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45864250693417768044808633 34398188020063326033606475)
                ·
                  refine ⟨51597282030094989050409713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34398188020063326033606475 51597282030094989050409713)
                  ·
                    refine ⟨38697961522571241787807285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51597282030094989050409713 38697961522571241787807285)
                    ·
                      refine ⟨3627933892741053917606933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38697961522571241787807285 3627933892741053917606933)
                      ·
                        rfl

theorem cell23_7065376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7065376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065376 prefixEnd_7065376 := by exact prefixLift 7065376
  have htrace : WordTrace (prefixWord ++ tailWord_7065376) baseStart_7065376 baseEnd_7065376 := by
    simpa [prefixWord, tailWord_7065376, baseEnd_7065376] using wordTrace_append hprefix tailTrace_7065376
  have hstable : (prefixWord ++ tailWord_7065376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065376).length < 2 ^ (prefixWord ++ tailWord_7065376).sum := by decide
  have hdescent : baseEnd_7065376 < baseStart_7065376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065420 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7065420 : Nat := 118140960795 + 7065420 * 2 ^ 59
def prefixEnd_7065420 : Nat := 4983230072969 + 3 ^ 40 * 7065420 * 2
def baseEnd_7065420 : Nat := 3627956485889851745456731

theorem tailTrace_7065420 : CollatzResearch.WordTrace tailWord_7065420 prefixEnd_7065420 3627956485889851745456731 := by
  unfold tailWord_7065420
  simp only [CollatzResearch.WordTrace]
  refine ⟨128848519031598746256296857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171798025375464995008395809 128848519031598746256296857)
  ·
    refine ⟨96636389273699059692222643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128848519031598746256296857 96636389273699059692222643)
    ·
      refine ⟨144954583910548589538333965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96636389273699059692222643 144954583910548589538333965)
      ·
        refine ⟨54357968966455721076875237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144954583910548589538333965 54357968966455721076875237)
        ·
          refine ⟨10192119181210447701914107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54357968966455721076875237 10192119181210447701914107)
          ·
            refine ⟨15288178771815671552871161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192119181210447701914107 15288178771815671552871161)
            ·
              refine ⟨11466134078861753664653371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15288178771815671552871161 11466134078861753664653371)
              ·
                refine ⟨17199201118292630496980057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11466134078861753664653371 17199201118292630496980057)
                ·
                  refine ⟨12899400838719472872735043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17199201118292630496980057 12899400838719472872735043)
                  ·
                    refine ⟨19349101258079209309102565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12899400838719472872735043 19349101258079209309102565)
                    ·
                      refine ⟨3627956485889851745456731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19349101258079209309102565 3627956485889851745456731)
                      ·
                        rfl

theorem cell23_7065420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7065420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065420 prefixEnd_7065420 := by exact prefixLift 7065420
  have htrace : WordTrace (prefixWord ++ tailWord_7065420) baseStart_7065420 baseEnd_7065420 := by
    simpa [prefixWord, tailWord_7065420, baseEnd_7065420] using wordTrace_append hprefix tailTrace_7065420
  have hstable : (prefixWord ++ tailWord_7065420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065420).length < 2 ^ (prefixWord ++ tailWord_7065420).sum := by decide
  have hdescent : baseEnd_7065420 < baseStart_7065420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065513 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_7065513 : Nat := 118140960795 + 7065513 * 2 ^ 59
def prefixEnd_7065513 : Nat := 4983230072969 + 3 ^ 40 * 7065513 * 2
def baseEnd_7065513 : Nat := 3628004239590719881593803

theorem tailTrace_7065513 : CollatzResearch.WordTrace tailWord_7065513 prefixEnd_7065513 3628004239590719881593803 := by
  unfold tailWord_7065513
  simp only [CollatzResearch.WordTrace]
  refine ⟨257700430051860569395729193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171800286701240379597152795 257700430051860569395729193)
  ·
    refine ⟨193275322538895427046796895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257700430051860569395729193 193275322538895427046796895)
    ·
      refine ⟨289912983808343140570195343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193275322538895427046796895 289912983808343140570195343)
      ·
        refine ⟨434869475712514710855293015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289912983808343140570195343 434869475712514710855293015)
        ·
          refine ⟨652304213568772066282939523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434869475712514710855293015 652304213568772066282939523)
          ·
            refine ⟨978456320353158099424409285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652304213568772066282939523 978456320353158099424409285)
            ·
              refine ⟨183460560066217143642076741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 978456320353158099424409285 183460560066217143642076741)
              ·
                refine ⟨34398855012415714432889389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183460560066217143642076741 34398855012415714432889389)
                ·
                  refine ⟨12899570629655892912333521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34398855012415714432889389 12899570629655892912333521)
                  ·
                    refine ⟨9674677972241919684250141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12899570629655892912333521 9674677972241919684250141)
                    ·
                      refine ⟨3628004239590719881593803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674677972241919684250141 3628004239590719881593803)
                      ·
                        rfl

theorem cell23_7065513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_7065513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065513 prefixEnd_7065513 := by exact prefixLift 7065513
  have htrace : WordTrace (prefixWord ++ tailWord_7065513) baseStart_7065513 baseEnd_7065513 := by
    simpa [prefixWord, tailWord_7065513, baseEnd_7065513] using wordTrace_append hprefix tailTrace_7065513
  have hstable : (prefixWord ++ tailWord_7065513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065513).length < 2 ^ (prefixWord ++ tailWord_7065513).sum := by decide
  have hdescent : baseEnd_7065513 < baseStart_7065513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065524 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7065524 : Nat := 118140960795 + 7065524 * 2 ^ 59
def prefixEnd_7065524 : Nat := 4983230072969 + 3 ^ 40 * 7065524 * 2
def baseEnd_7065524 : Nat := 1209336629292639779518751

theorem tailTrace_7065524 : CollatzResearch.WordTrace tailWord_7065524 prefixEnd_7065524 1209336629292639779518751 := by
  unfold tailWord_7065524
  simp only [CollatzResearch.WordTrace]
  refine ⟨128850415627410359137189813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171800554169880478849586417 128850415627410359137189813)
  ·
    refine ⟨12079726465069721169111545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128850415627410359137189813 12079726465069721169111545)
    ·
      refine ⟨9059794848802290876833659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12079726465069721169111545 9059794848802290876833659)
      ·
        refine ⟨13589692273203436315250489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9059794848802290876833659 13589692273203436315250489)
        ·
          refine ⟨10192269204902577236437867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13589692273203436315250489 10192269204902577236437867)
          ·
            refine ⟨15288403807353865854656801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192269204902577236437867 15288403807353865854656801)
            ·
              refine ⟨11466302855515399390992601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15288403807353865854656801 11466302855515399390992601)
              ·
                refine ⟨8599727141636549543244451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11466302855515399390992601 8599727141636549543244451)
                ·
                  refine ⟨12899590712454824314866677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8599727141636549543244451 12899590712454824314866677)
                  ·
                    refine ⟨1209336629292639779518751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12899590712454824314866677 1209336629292639779518751)
                    ·
                      rfl

theorem cell23_7065524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7065524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065524 prefixEnd_7065524 := by exact prefixLift 7065524
  have htrace : WordTrace (prefixWord ++ tailWord_7065524) baseStart_7065524 baseEnd_7065524 := by
    simpa [prefixWord, tailWord_7065524, baseEnd_7065524] using wordTrace_append hprefix tailTrace_7065524
  have hstable : (prefixWord ++ tailWord_7065524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065524).length < 2 ^ (prefixWord ++ tailWord_7065524).sum := by decide
  have hdescent : baseEnd_7065524 < baseStart_7065524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065533 : List Nat := [1, 4, 1, 2, 3, 2, 1, 9]
def baseStart_7065533 : Nat := 118140960795 + 7065533 * 2 ^ 59
def prefixEnd_7065533 : Nat := 4983230072969 + 3 ^ 40 * 7065533 * 2
def baseEnd_7065533 : Nat := 134370907748289251975693

theorem tailTrace_7065533 : CollatzResearch.WordTrace tailWord_7065533 prefixEnd_7065533 134370907748289251975693 := by
  unfold tailWord_7065533
  simp only [CollatzResearch.WordTrace]
  refine ⟨257701159511788112811457253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171800773007858741874304835 257701159511788112811457253)
  ·
    refine ⟨48318967408460271152148235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257701159511788112811457253 48318967408460271152148235)
    ·
      refine ⟨72478451112690406728222353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48318967408460271152148235 72478451112690406728222353)
      ·
        refine ⟨54358838334517805046166765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72478451112690406728222353 54358838334517805046166765)
        ·
          refine ⟨20384564375444176892312537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54358838334517805046166765 20384564375444176892312537)
          ·
            refine ⟨15288423281583132669234403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20384564375444176892312537 15288423281583132669234403)
            ·
              refine ⟨22932634922374699003851605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15288423281583132669234403 22932634922374699003851605)
              ·
                refine ⟨134370907748289251975693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22932634922374699003851605 134370907748289251975693)
                ·
                  rfl

theorem cell23_7065533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 9].length) (baseStart_7065533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065533 prefixEnd_7065533 := by exact prefixLift 7065533
  have htrace : WordTrace (prefixWord ++ tailWord_7065533) baseStart_7065533 baseEnd_7065533 := by
    simpa [prefixWord, tailWord_7065533, baseEnd_7065533] using wordTrace_append hprefix tailTrace_7065533
  have hstable : (prefixWord ++ tailWord_7065533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065533).length < 2 ^ (prefixWord ++ tailWord_7065533).sum := by decide
  have hdescent : baseEnd_7065533 < baseStart_7065533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065543 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_7065543 : Nat := 118140960795 + 7065543 * 2 ^ 59
def prefixEnd_7065543 : Nat := 4983230072969 + 3 ^ 40 * 7065543 * 2
def baseEnd_7065543 : Nat := 3628019644010354764218665

theorem tailTrace_7065543 : CollatzResearch.WordTrace tailWord_7065543 prefixEnd_7065543 3628019644010354764218665 := by
  unfold tailWord_7065543
  simp only [CollatzResearch.WordTrace]
  refine ⟨257701524241751884519321283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171801016161167923012880855 257701524241751884519321283)
  ·
    refine ⟨386552286362627826778981925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257701524241751884519321283 386552286362627826778981925)
    ·
      refine ⟨72478553692992717521059111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386552286362627826778981925 72478553692992717521059111)
      ·
        refine ⟨108717830539489076281588667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72478553692992717521059111 108717830539489076281588667)
        ·
          refine ⟨163076745809233614422383001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108717830539489076281588667 163076745809233614422383001)
          ·
            refine ⟨122307559356925210816787251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163076745809233614422383001 122307559356925210816787251)
            ·
              refine ⟨183461339035387816225180877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122307559356925210816787251 183461339035387816225180877)
              ·
                refine ⟨68798002138270431084442829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183461339035387816225180877 68798002138270431084442829)
                ·
                  refine ⟨25799250801851411656666061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68798002138270431084442829 25799250801851411656666061)
                  ·
                    refine ⟨9674719050694279371249773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25799250801851411656666061 9674719050694279371249773)
                    ·
                      refine ⟨3628019644010354764218665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674719050694279371249773 3628019644010354764218665)
                      ·
                        rfl

theorem cell23_7065543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_7065543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065543 prefixEnd_7065543 := by exact prefixLift 7065543
  have htrace : WordTrace (prefixWord ++ tailWord_7065543) baseStart_7065543 baseEnd_7065543 := by
    simpa [prefixWord, tailWord_7065543, baseEnd_7065543] using wordTrace_append hprefix tailTrace_7065543
  have hstable : (prefixWord ++ tailWord_7065543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065543).length < 2 ^ (prefixWord ++ tailWord_7065543).sum := by decide
  have hdescent : baseEnd_7065543 < baseStart_7065543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065560 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_7065560 : Nat := 118140960795 + 7065560 * 2 ^ 59
def prefixEnd_7065560 : Nat := 4983230072969 + 3 ^ 40 * 7065560 * 2
def baseEnd_7065560 : Nat := 3628028373181481197706087

theorem tailTrace_7065560 : CollatzResearch.WordTrace tailWord_7065560 prefixEnd_7065560 3628028373181481197706087 := by
  unfold tailWord_7065560
  simp only [CollatzResearch.WordTrace]
  refine ⟨128851072141345148211345067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171801429521793530948460089 128851072141345148211345067)
  ·
    refine ⟨193276608212017722317017601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128851072141345148211345067 193276608212017722317017601)
    ·
      refine ⟨144957456159013291737763201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193276608212017722317017601 144957456159013291737763201)
      ·
        refine ⟨108718092119259968803322401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144957456159013291737763201 108718092119259968803322401)
        ·
          refine ⟨81538569089444976602491801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108718092119259968803322401 81538569089444976602491801)
          ·
            refine ⟨61153926817083732451868851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81538569089444976602491801 61153926817083732451868851)
            ·
              refine ⟨91730890225625598677803277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61153926817083732451868851 91730890225625598677803277)
              ·
                refine ⟨34399083834609599504176229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91730890225625598677803277 34399083834609599504176229)
                ·
                  refine ⟨6449828218989299907033043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34399083834609599504176229 6449828218989299907033043)
                  ·
                    refine ⟨9674742328483949860549565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6449828218989299907033043 9674742328483949860549565)
                    ·
                      refine ⟨3628028373181481197706087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674742328483949860549565 3628028373181481197706087)
                      ·
                        rfl

theorem cell23_7065560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_7065560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065560 prefixEnd_7065560 := by exact prefixLift 7065560
  have htrace : WordTrace (prefixWord ++ tailWord_7065560) baseStart_7065560 baseEnd_7065560 := by
    simpa [prefixWord, tailWord_7065560, baseEnd_7065560] using wordTrace_append hprefix tailTrace_7065560
  have hstable : (prefixWord ++ tailWord_7065560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065560).length < 2 ^ (prefixWord ++ tailWord_7065560).sum := by decide
  have hdescent : baseEnd_7065560 < baseStart_7065560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065561 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 3, 2, 2]
def baseStart_7065561 : Nat := 118140960795 + 7065561 * 2 ^ 59
def prefixEnd_7065561 : Nat := 4983230072969 + 3 ^ 40 * 7065561 * 2
def baseEnd_7065561 : Nat := 3628028886662135693793583

theorem tailTrace_7065561 : CollatzResearch.WordTrace tailWord_7065561 prefixEnd_7065561 3628028886662135693793583 := by
  unfold tailWord_7065561
  simp only [CollatzResearch.WordTrace]
  refine ⟨257702180755686673593476537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171801453837124449062317691 257702180755686673593476537)
  ·
    refine ⟨193276635566765005195107403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257702180755686673593476537 193276635566765005195107403)
    ·
      refine ⟨289914953350147507792661105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193276635566765005195107403 289914953350147507792661105)
      ·
        refine ⟨217436215012610630844495829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289914953350147507792661105 217436215012610630844495829)
        ·
          refine ⟨5096161289358061660417871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 217436215012610630844495829 5096161289358061660417871)
          ·
            refine ⟨7644241934037092490626807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096161289358061660417871 7644241934037092490626807)
            ·
              refine ⟨11466362901055638735940211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644241934037092490626807 11466362901055638735940211)
              ·
                refine ⟨17199544351583458103910317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11466362901055638735940211 17199544351583458103910317)
                ·
                  refine ⟨6449829131843796788966369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17199544351583458103910317 6449829131843796788966369)
                  ·
                    refine ⟨4837371848882847591724777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6449829131843796788966369 4837371848882847591724777)
                    ·
                      refine ⟨3628028886662135693793583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837371848882847591724777 3628028886662135693793583)
                      ·
                        rfl

theorem cell23_7065561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_7065561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065561 prefixEnd_7065561 := by exact prefixLift 7065561
  have htrace : WordTrace (prefixWord ++ tailWord_7065561) baseStart_7065561 baseEnd_7065561 := by
    simpa [prefixWord, tailWord_7065561, baseEnd_7065561] using wordTrace_append hprefix tailTrace_7065561
  have hstable : (prefixWord ++ tailWord_7065561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065561).length < 2 ^ (prefixWord ++ tailWord_7065561).sum := by decide
  have hdescent : baseEnd_7065561 < baseStart_7065561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065581 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7065581 : Nat := 118140960795 + 7065581 * 2 ^ 59
def prefixEnd_7065581 : Nat := 4983230072969 + 3 ^ 40 * 7065581 * 2
def baseEnd_7065581 : Nat := 3628039156275225615543491

theorem tailTrace_7065581 : CollatzResearch.WordTrace tailWord_7065581 prefixEnd_7065581 3628039156275225615543491 := by
  unfold tailWord_7065581
  simp only [CollatzResearch.WordTrace]
  refine ⟨257702910215614217009204597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171801940143742811339469731 257702910215614217009204597)
  ·
    refine ⟨24159647832713832844612931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257702910215614217009204597 24159647832713832844612931)
    ·
      refine ⟨36239471749070749266919397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24159647832713832844612931 36239471749070749266919397)
      ·
        refine ⟨6794900952950765487547387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36239471749070749266919397 6794900952950765487547387)
        ·
          refine ⟨10192351429426148231321081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794900952950765487547387 10192351429426148231321081)
          ·
            refine ⟨7644263572069611173490811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10192351429426148231321081 7644263572069611173490811)
            ·
              refine ⟨11466395358104416760236217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644263572069611173490811 11466395358104416760236217)
              ·
                refine ⟨8599796518578312570177163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11466395358104416760236217 8599796518578312570177163)
                ·
                  refine ⟨12899694777867468855265745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8599796518578312570177163 12899694777867468855265745)
                  ·
                    refine ⟨9674771083400601641449309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12899694777867468855265745 9674771083400601641449309)
                    ·
                      refine ⟨3628039156275225615543491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674771083400601641449309 3628039156275225615543491)
                      ·
                        rfl

theorem cell23_7065581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7065581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065581 prefixEnd_7065581 := by exact prefixLift 7065581
  have htrace : WordTrace (prefixWord ++ tailWord_7065581) baseStart_7065581 baseEnd_7065581 := by
    simpa [prefixWord, tailWord_7065581, baseEnd_7065581] using wordTrace_append hprefix tailTrace_7065581
  have hstable : (prefixWord ++ tailWord_7065581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065581).length < 2 ^ (prefixWord ++ tailWord_7065581).sum := by decide
  have hdescent : baseEnd_7065581 < baseStart_7065581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065603 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 3]
def baseStart_7065603 : Nat := 118140960795 + 7065603 * 2 ^ 59
def prefixEnd_7065603 : Nat := 4983230072969 + 3 ^ 40 * 7065603 * 2
def baseEnd_7065603 : Nat := 3628050452849624529468389

theorem tailTrace_7065603 : CollatzResearch.WordTrace tailWord_7065603 prefixEnd_7065603 3628050452849624529468389 := by
  unfold tailWord_7065603
  simp only [CollatzResearch.WordTrace]
  refine ⟨257703712621534514766505463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171802475081023009844336975 257703712621534514766505463)
  ·
    refine ⟨386555568932301772149758195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257703712621534514766505463 386555568932301772149758195)
    ·
      refine ⟨579833353398452658224637293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386555568932301772149758195 579833353398452658224637293)
      ·
        refine ⟨217437507524419746834238985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579833353398452658224637293 217437507524419746834238985)
        ·
          refine ⟨163078130643314810125679239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217437507524419746834238985 163078130643314810125679239)
          ·
            refine ⟨244617195964972215188518859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163078130643314810125679239 244617195964972215188518859)
            ·
              refine ⟨366925793947458322782778289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244617195964972215188518859 366925793947458322782778289)
              ·
                refine ⟨275194345460593742087083717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366925793947458322782778289 275194345460593742087083717)
                ·
                  refine ⟨51598939773861326641328197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275194345460593742087083717 51598939773861326641328197)
                  ·
                    refine ⟨9674801207598998745249037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51598939773861326641328197 9674801207598998745249037)
                    ·
                      refine ⟨3628050452849624529468389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9674801207598998745249037 3628050452849624529468389)
                      ·
                        rfl

theorem cell23_7065603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_7065603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065603 prefixEnd_7065603 := by exact prefixLift 7065603
  have htrace : WordTrace (prefixWord ++ tailWord_7065603) baseStart_7065603 baseEnd_7065603 := by
    simpa [prefixWord, tailWord_7065603, baseEnd_7065603] using wordTrace_append hprefix tailTrace_7065603
  have hstable : (prefixWord ++ tailWord_7065603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065603).length < 2 ^ (prefixWord ++ tailWord_7065603).sum := by decide
  have hdescent : baseEnd_7065603 < baseStart_7065603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065634 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_7065634 : Nat := 118140960795 + 7065634 * 2 ^ 59
def prefixEnd_7065634 : Nat := 4983230072969 + 3 ^ 40 * 7065634 * 2
def baseEnd_7065634 : Nat := 3628066370749913908180747

theorem tailTrace_7065634 : CollatzResearch.WordTrace tailWord_7065634 prefixEnd_7065634 3628066370749913908180747 := by
  unfold tailWord_7065634
  simp only [CollatzResearch.WordTrace]
  refine ⟨64426210821105551765220989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171803228856281471373922637 64426210821105551765220989)
  ·
    refine ⟨24159829057914581911957871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64426210821105551765220989 24159829057914581911957871)
    ·
      refine ⟨36239743586871872867936807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24159829057914581911957871 36239743586871872867936807)
      ·
        refine ⟨54359615380307809301905211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36239743586871872867936807 54359615380307809301905211)
        ·
          refine ⟨81539423070461713952857817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54359615380307809301905211 81539423070461713952857817)
          ·
            refine ⟨61154567302846285464643363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81539423070461713952857817 61154567302846285464643363)
            ·
              refine ⟨91731850954269428196965045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61154567302846285464643363 91731850954269428196965045)
              ·
                refine ⟨8599861026962758893465473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91731850954269428196965045 8599861026962758893465473)
                ·
                  refine ⟨6449895770222069170099105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599861026962758893465473 6449895770222069170099105)
                  ·
                    refine ⟨4837421827666551877574329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6449895770222069170099105 4837421827666551877574329)
                    ·
                      refine ⟨3628066370749913908180747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837421827666551877574329 3628066370749913908180747)
                      ·
                        rfl

theorem cell23_7065634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_7065634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065634 prefixEnd_7065634 := by exact prefixLift 7065634
  have htrace : WordTrace (prefixWord ++ tailWord_7065634) baseStart_7065634 baseEnd_7065634 := by
    simpa [prefixWord, tailWord_7065634, baseEnd_7065634] using wordTrace_append hprefix tailTrace_7065634
  have hstable : (prefixWord ++ tailWord_7065634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065634).length < 2 ^ (prefixWord ++ tailWord_7065634).sum := by decide
  have hdescent : baseEnd_7065634 < baseStart_7065634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065663 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_7065663 : Nat := 118140960795 + 7065663 * 2 ^ 59
def prefixEnd_7065663 : Nat := 4983230072969 + 3 ^ 40 * 7065663 * 2
def baseEnd_7065663 : Nat := 3628081261688894294718113

theorem tailTrace_7065663 : CollatzResearch.WordTrace tailWord_7065663 prefixEnd_7065663 3628081261688894294718113 := by
  unfold tailWord_7065663
  simp only [CollatzResearch.WordTrace]
  refine ⟨257705901001317145013689643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171803934000878096675793095 257705901001317145013689643)
  ·
    refine ⟨386558851501975717520534465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257705901001317145013689643 386558851501975717520534465)
    ·
      refine ⟨289919138626481788140400849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386558851501975717520534465 289919138626481788140400849)
      ·
        refine ⟨217439353969861341105300637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289919138626481788140400849 217439353969861341105300637)
        ·
          refine ⟨81539757738698002914487739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217439353969861341105300637 81539757738698002914487739)
          ·
            refine ⟨122309636608047004371731609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81539757738698002914487739 122309636608047004371731609)
            ·
              refine ⟨91732227456035253278798707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122309636608047004371731609 91732227456035253278798707)
              ·
                refine ⟨137598341184052879918198061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91732227456035253278798707 137598341184052879918198061)
                ·
                  refine ⟨51599377944019829969324273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137598341184052879918198061 51599377944019829969324273)
                  ·
                    refine ⟨38699533458014872476993205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51599377944019829969324273 38699533458014872476993205)
                    ·
                      refine ⟨3628081261688894294718113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38699533458014872476993205 3628081261688894294718113)
                      ·
                        rfl

theorem cell23_7065663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_7065663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065663 prefixEnd_7065663 := by exact prefixLift 7065663
  have htrace : WordTrace (prefixWord ++ tailWord_7065663) baseStart_7065663 baseEnd_7065663 := by
    simpa [prefixWord, tailWord_7065663, baseEnd_7065663] using wordTrace_append hprefix tailTrace_7065663
  have hstable : (prefixWord ++ tailWord_7065663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065663).length < 2 ^ (prefixWord ++ tailWord_7065663).sum := by decide
  have hdescent : baseEnd_7065663 < baseStart_7065663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065713 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 10]
def baseStart_7065713 : Nat := 118140960795 + 7065713 * 2 ^ 59
def prefixEnd_7065713 : Nat := 4983230072969 + 3 ^ 40 * 7065713 * 2
def baseEnd_7065713 : Nat := 403122992857957677676987

theorem tailTrace_7065713 : CollatzResearch.WordTrace tailWord_7065713 prefixEnd_7065713 403122992857957677676987 := by
  unfold tailWord_7065713
  simp only [CollatzResearch.WordTrace]
  refine ⟨257707724651136003553009793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171805149767424002368673195 257707724651136003553009793)
  ·
    refine ⟨193280793488352002664757345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257707724651136003553009793 193280793488352002664757345)
    ·
      refine ⟨144960595116264001998568009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193280793488352002664757345 144960595116264001998568009)
      ·
        refine ⟨108720446337198001498926007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144960595116264001998568009 108720446337198001498926007)
        ·
          refine ⟨163080669505797002248389011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108720446337198001498926007 163080669505797002248389011)
          ·
            refine ⟨244621004258695503372583517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163080669505797002248389011 244621004258695503372583517)
            ·
              refine ⟨91732876597010813764718819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244621004258695503372583517 91732876597010813764718819)
              ·
                refine ⟨137599314895516220647078229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91732876597010813764718819 137599314895516220647078229)
                ·
                  refine ⟨403122992857957677676987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 137599314895516220647078229 403122992857957677676987)
                  ·
                    rfl

theorem cell23_7065713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_7065713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065713 prefixEnd_7065713 := by exact prefixLift 7065713
  have htrace : WordTrace (prefixWord ++ tailWord_7065713) baseStart_7065713 baseEnd_7065713 := by
    simpa [prefixWord, tailWord_7065713, baseEnd_7065713] using wordTrace_append hprefix tailTrace_7065713
  have hstable : (prefixWord ++ tailWord_7065713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065713).length < 2 ^ (prefixWord ++ tailWord_7065713).sum := by decide
  have hdescent : baseEnd_7065713 < baseStart_7065713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065800 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_7065800 : Nat := 118140960795 + 7065800 * 2 ^ 59
def prefixEnd_7065800 : Nat := 4983230072969 + 3 ^ 40 * 7065800 * 2
def baseEnd_7065800 : Nat := 3628151608538560258704983

theorem tailTrace_7065800 : CollatzResearch.WordTrace tailWord_7065800 prefixEnd_7065800 3628151608538560258704983 := by
  unfold tailWord_7065800
  simp only [CollatzResearch.WordTrace]
  refine ⟨128855448900910408705713427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171807265201213878274284569 128855448900910408705713427)
  ·
    refine ⟨193283173351365613058570141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128855448900910408705713427 193283173351365613058570141)
    ·
      refine ⟨72481190006762104896963803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193283173351365613058570141 72481190006762104896963803)
      ·
        refine ⟨108721785010143157345445705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72481190006762104896963803 108721785010143157345445705)
        ·
          refine ⟨81541338757607368009084279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108721785010143157345445705 81541338757607368009084279)
          ·
            refine ⟨122312008136411052013626419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81541338757607368009084279 122312008136411052013626419)
            ·
              refine ⟨183468012204616578020439629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122312008136411052013626419 183468012204616578020439629)
              ·
                refine ⟨68800504576731216757664861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183468012204616578020439629 68800504576731216757664861)
                ·
                  refine ⟨25800189216274206284124323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68800504576731216757664861 25800189216274206284124323)
                  ·
                    refine ⟨38700283824411309426186485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25800189216274206284124323 38700283824411309426186485)
                    ·
                      refine ⟨3628151608538560258704983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38700283824411309426186485 3628151608538560258704983)
                      ·
                        rfl

theorem cell23_7065800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_7065800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065800 prefixEnd_7065800 := by exact prefixLift 7065800
  have htrace : WordTrace (prefixWord ++ tailWord_7065800) baseStart_7065800 baseEnd_7065800 := by
    simpa [prefixWord, tailWord_7065800, baseEnd_7065800] using wordTrace_append hprefix tailTrace_7065800
  have hstable : (prefixWord ++ tailWord_7065800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065800).length < 2 ^ (prefixWord ++ tailWord_7065800).sum := by decide
  have hdescent : baseEnd_7065800 < baseStart_7065800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065807 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 2, 4]
def baseStart_7065807 : Nat := 118140960795 + 7065807 * 2 ^ 59
def prefixEnd_7065807 : Nat := 4983230072969 + 3 ^ 40 * 7065807 * 2
def baseEnd_7065807 : Nat := 1209385067634380577105817

theorem tailTrace_7065807 : CollatzResearch.WordTrace tailWord_7065807 prefixEnd_7065807 1209385067634380577105817 := by
  unfold tailWord_7065807
  simp only [CollatzResearch.WordTrace]
  refine ⟨257711153112795457606931675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171807435408530305071287783 257711153112795457606931675)
  ·
    refine ⟨386566729669193186410397513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257711153112795457606931675 386566729669193186410397513)
    ·
      refine ⟨289925047251894889807798135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386566729669193186410397513 289925047251894889807798135)
      ·
        refine ⟨434887570877842334711697203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289925047251894889807798135 434887570877842334711697203)
        ·
          refine ⟨652331356316763502067545805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434887570877842334711697203 652331356316763502067545805)
          ·
            refine ⟨244624258618786313275329677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 652331356316763502067545805 244624258618786313275329677)
            ·
              refine ⟨91734096982044867478248629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244624258618786313275329677 91734096982044867478248629)
              ·
                refine ⟨8600071592066706326085809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91734096982044867478248629 8600071592066706326085809)
                ·
                  refine ⟨6450053694050029744564357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600071592066706326085809 6450053694050029744564357)
                  ·
                    refine ⟨1209385067634380577105817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6450053694050029744564357 1209385067634380577105817)
                    ·
                      rfl

theorem cell23_7065807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_7065807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065807 prefixEnd_7065807 := by exact prefixLift 7065807
  have htrace : WordTrace (prefixWord ++ tailWord_7065807) baseStart_7065807 baseEnd_7065807 := by
    simpa [prefixWord, tailWord_7065807, baseEnd_7065807] using wordTrace_append hprefix tailTrace_7065807
  have hstable : (prefixWord ++ tailWord_7065807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065807).length < 2 ^ (prefixWord ++ tailWord_7065807).sum := by decide
  have hdescent : baseEnd_7065807 < baseStart_7065807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065817 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_7065817 : Nat := 118140960795 + 7065817 * 2 ^ 59
def prefixEnd_7065817 : Nat := 4983230072969 + 3 ^ 40 * 7065817 * 2
def baseEnd_7065817 : Nat := 3628160337709686692192405

theorem tailTrace_7065817 : CollatzResearch.WordTrace tailWord_7065817 prefixEnd_7065817 3628160337709686692192405 := by
  unfold tailWord_7065817
  simp only [CollatzResearch.WordTrace]
  refine ⟨257711517842759229314795705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171807678561839486209863803 257711517842759229314795705)
  ·
    refine ⟨193283638382069421986096779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257711517842759229314795705 193283638382069421986096779)
    ·
      refine ⟨289925457573104132979145169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193283638382069421986096779 289925457573104132979145169)
      ·
        refine ⟨217444093179828099734358877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289925457573104132979145169 217444093179828099734358877)
        ·
          refine ⟨81541534942435537400384579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217444093179828099734358877 81541534942435537400384579)
          ·
            refine ⟨122312302413653306100576869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81541534942435537400384579 122312302413653306100576869)
            ·
              refine ⟨22933556702559994893858163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122312302413653306100576869 22933556702559994893858163)
              ·
                refine ⟨34400335053839992340787245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22933556702559994893858163 34400335053839992340787245)
                ·
                  refine ⟨12900125645189997127795217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34400335053839992340787245 12900125645189997127795217)
                  ·
                    refine ⟨9675094233892497845846413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12900125645189997127795217 9675094233892497845846413)
                    ·
                      refine ⟨3628160337709686692192405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675094233892497845846413 3628160337709686692192405)
                      ·
                        rfl

theorem cell23_7065817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_7065817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065817 prefixEnd_7065817 := by exact prefixLift 7065817
  have htrace : WordTrace (prefixWord ++ tailWord_7065817) baseStart_7065817 baseEnd_7065817 := by
    simpa [prefixWord, tailWord_7065817, baseEnd_7065817] using wordTrace_append hprefix tailTrace_7065817
  have hstable : (prefixWord ++ tailWord_7065817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065817).length < 2 ^ (prefixWord ++ tailWord_7065817).sum := by decide
  have hdescent : baseEnd_7065817 < baseStart_7065817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065831 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7065831 : Nat := 118140960795 + 7065831 * 2 ^ 59
def prefixEnd_7065831 : Nat := 4983230072969 + 3 ^ 40 * 7065831 * 2
def baseEnd_7065831 : Nat := 3628167526438849637417341

theorem tailTrace_7065831 : CollatzResearch.WordTrace tailWord_7065831 prefixEnd_7065831 3628167526438849637417341 := by
  unfold tailWord_7065831
  simp only [CollatzResearch.WordTrace]
  refine ⟨257712028464708509705805347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171808018976472339803870231 257712028464708509705805347)
  ·
    refine ⟨386568042697062764558708021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257712028464708509705805347 386568042697062764558708021)
    ·
      refine ⟨36240754002849634177378877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 386568042697062764558708021 36240754002849634177378877)
      ·
        refine ⟨13590282751068612816517079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36240754002849634177378877 13590282751068612816517079)
        ·
          refine ⟨20385424126602919224775619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13590282751068612816517079 20385424126602919224775619)
          ·
            refine ⟨30578136189904378837163429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20385424126602919224775619 30578136189904378837163429)
            ·
              refine ⟨5733400535607071031968143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30578136189904378837163429 5733400535607071031968143)
              ·
                refine ⟨8600100803410606547952215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733400535607071031968143 8600100803410606547952215)
                ·
                  refine ⟨12900151205115909821928323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8600100803410606547952215 12900151205115909821928323)
                  ·
                    refine ⟨19350226807673864732892485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12900151205115909821928323 19350226807673864732892485)
                    ·
                      refine ⟨3628167526438849637417341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19350226807673864732892485 3628167526438849637417341)
                      ·
                        rfl

theorem cell23_7065831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7065831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065831 prefixEnd_7065831 := by exact prefixLift 7065831
  have htrace : WordTrace (prefixWord ++ tailWord_7065831) baseStart_7065831 baseEnd_7065831 := by
    simpa [prefixWord, tailWord_7065831, baseEnd_7065831] using wordTrace_append hprefix tailTrace_7065831
  have hstable : (prefixWord ++ tailWord_7065831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065831).length < 2 ^ (prefixWord ++ tailWord_7065831).sum := by decide
  have hdescent : baseEnd_7065831 < baseStart_7065831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065834 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_7065834 : Nat := 118140960795 + 7065834 * 2 ^ 59
def prefixEnd_7065834 : Nat := 4983230072969 + 3 ^ 40 * 7065834 * 2
def baseEnd_7065834 : Nat := 3628169066880813125679827

theorem tailTrace_7065834 : CollatzResearch.WordTrace tailWord_7065834 prefixEnd_7065834 3628169066880813125679827 := by
  unfold tailWord_7065834
  simp only [CollatzResearch.WordTrace]
  refine ⟨64428034470924410304541139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171808091922465094145443037 64428034470924410304541139)
  ·
    refine ⟨96642051706386615456811709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64428034470924410304541139 96642051706386615456811709)
    ·
      refine ⟨36240769389894980796304391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96642051706386615456811709 36240769389894980796304391)
      ·
        refine ⟨54361154084842471194456587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36240769389894980796304391 54361154084842471194456587)
        ·
          refine ⟨81541731127263706791684881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54361154084842471194456587 81541731127263706791684881)
          ·
            refine ⟨61156298345447780093763661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81541731127263706791684881 61156298345447780093763661)
            ·
              refine ⟨22933611879542917535161373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61156298345447780093763661 22933611879542917535161373)
              ·
                refine ⟨8600104454828594075685515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22933611879542917535161373 8600104454828594075685515)
                ·
                  refine ⟨12900156682242891113528273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8600104454828594075685515 12900156682242891113528273)
                  ·
                    refine ⟨9675117511682168335146205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12900156682242891113528273 9675117511682168335146205)
                    ·
                      refine ⟨3628169066880813125679827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675117511682168335146205 3628169066880813125679827)
                      ·
                        rfl

theorem cell23_7065834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_7065834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065834 prefixEnd_7065834 := by exact prefixLift 7065834
  have htrace : WordTrace (prefixWord ++ tailWord_7065834) baseStart_7065834 baseEnd_7065834 := by
    simpa [prefixWord, tailWord_7065834, baseEnd_7065834] using wordTrace_append hprefix tailTrace_7065834
  have hstable : (prefixWord ++ tailWord_7065834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065834).length < 2 ^ (prefixWord ++ tailWord_7065834).sum := by decide
  have hdescent : baseEnd_7065834 < baseStart_7065834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065837 : List Nat := [1, 5, 1, 2, 3, 1, 10]
def baseStart_7065837 : Nat := 118140960795 + 7065837 * 2 ^ 59
def prefixEnd_7065837 : Nat := 4983230072969 + 3 ^ 40 * 7065837 * 2
def baseEnd_7065837 : Nat := 44792229720034279184473

theorem tailTrace_7065837 : CollatzResearch.WordTrace tailWord_7065837 prefixEnd_7065837 44792229720034279184473 := by
  unfold tailWord_7065837
  simp only [CollatzResearch.WordTrace]
  refine ⟨257712247302686772730523765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171808164868457848487015843 257712247302686772730523765)
  ·
    refine ⟨24160523184626884943486603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257712247302686772730523765 24160523184626884943486603)
    ·
      refine ⟨36240784776940327415229905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24160523184626884943486603 36240784776940327415229905)
      ·
        refine ⟨27180588582705245561422429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36240784776940327415229905 27180588582705245561422429)
        ·
          refine ⟨10192720718514467085533411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27180588582705245561422429 10192720718514467085533411)
          ·
            refine ⟨15289081077771700628300117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192720718514467085533411 15289081077771700628300117)
            ·
              refine ⟨44792229720034279184473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15289081077771700628300117 44792229720034279184473)
              ·
                rfl

theorem cell23_7065837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 10].length) (baseStart_7065837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065837 prefixEnd_7065837 := by exact prefixLift 7065837
  have htrace : WordTrace (prefixWord ++ tailWord_7065837) baseStart_7065837 baseEnd_7065837 := by
    simpa [prefixWord, tailWord_7065837, baseEnd_7065837] using wordTrace_append hprefix tailTrace_7065837
  have hstable : (prefixWord ++ tailWord_7065837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065837).length < 2 ^ (prefixWord ++ tailWord_7065837).sum := by decide
  have hdescent : baseEnd_7065837 < baseStart_7065837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065858 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_7065858 : Nat := 118140960795 + 7065858 * 2 ^ 59
def prefixEnd_7065858 : Nat := 4983230072969 + 3 ^ 40 * 7065858 * 2
def baseEnd_7065858 : Nat := 1209393796805507010593239

theorem tailTrace_7065858 : CollatzResearch.WordTrace tailWord_7065858 prefixEnd_7065858 1209393796805507010593239 := by
  unfold tailWord_7065858
  simp only [CollatzResearch.WordTrace]
  refine ⟨64428253308902673329259557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171808675490407128878025485 64428253308902673329259557)
  ·
    refine ⟨12080297495419251249236167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64428253308902673329259557 12080297495419251249236167)
    ·
      refine ⟨18120446243128876873854251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12080297495419251249236167 18120446243128876873854251)
      ·
        refine ⟨27180669364693315310781377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18120446243128876873854251 27180669364693315310781377)
        ·
          refine ⟨20385502023519986483086033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27180669364693315310781377 20385502023519986483086033)
          ·
            refine ⟨15289126517639989862314525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20385502023519986483086033 15289126517639989862314525)
            ·
              refine ⟨5733422444114996198367947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15289126517639989862314525 5733422444114996198367947)
              ·
                refine ⟨8600133666172494297551921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733422444114996198367947 8600133666172494297551921)
                ·
                  refine ⟨6450100249629370723163941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600133666172494297551921 6450100249629370723163941)
                  ·
                    refine ⟨1209393796805507010593239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6450100249629370723163941 1209393796805507010593239)
                    ·
                      rfl

theorem cell23_7065858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_7065858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065858 prefixEnd_7065858 := by exact prefixLift 7065858
  have htrace : WordTrace (prefixWord ++ tailWord_7065858) baseStart_7065858 baseEnd_7065858 := by
    simpa [prefixWord, tailWord_7065858, baseEnd_7065858] using wordTrace_append hprefix tailTrace_7065858
  have hstable : (prefixWord ++ tailWord_7065858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065858).length < 2 ^ (prefixWord ++ tailWord_7065858).sum := by decide
  have hdescent : baseEnd_7065858 < baseStart_7065858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065864 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_7065864 : Nat := 118140960795 + 7065864 * 2 ^ 59
def prefixEnd_7065864 : Nat := 4983230072969 + 3 ^ 40 * 7065864 * 2
def baseEnd_7065864 : Nat := 3628184471300448008304689

theorem tailTrace_7065864 : CollatzResearch.WordTrace tailWord_7065864 prefixEnd_7065864 3628184471300448008304689 := by
  unfold tailWord_7065864
  simp only [CollatzResearch.WordTrace]
  refine ⟨128856616036794478170878323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171808821382392637561171097 128856616036794478170878323)
  ·
    refine ⟨193284924055191717256317485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128856616036794478170878323 193284924055191717256317485)
    ·
      refine ⟨72481846520696893971119057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193284924055191717256317485 72481846520696893971119057)
      ·
        refine ⟨54361384890522670478339293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72481846520696893971119057 54361384890522670478339293)
        ·
          refine ⟨20385519333946001429377235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54361384890522670478339293 20385519333946001429377235)
          ·
            refine ⟨30578279000919002144065853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20385519333946001429377235 30578279000919002144065853)
            ·
              refine ⟨11466854625344625804024695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30578279000919002144065853 11466854625344625804024695)
              ·
                refine ⟨17200281938016938706037043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11466854625344625804024695 17200281938016938706037043)
                ·
                  refine ⟨25800422907025408059055565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17200281938016938706037043 25800422907025408059055565)
                  ·
                    refine ⟨9675158590134528022145837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25800422907025408059055565 9675158590134528022145837)
                    ·
                      refine ⟨3628184471300448008304689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675158590134528022145837 3628184471300448008304689)
                      ·
                        rfl

theorem cell23_7065864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_7065864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065864 prefixEnd_7065864 := by exact prefixLift 7065864
  have htrace : WordTrace (prefixWord ++ tailWord_7065864) baseStart_7065864 baseEnd_7065864 := by
    simpa [prefixWord, tailWord_7065864, baseEnd_7065864] using wordTrace_append hprefix tailTrace_7065864
  have hstable : (prefixWord ++ tailWord_7065864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065864).length < 2 ^ (prefixWord ++ tailWord_7065864).sum := by decide
  have hdescent : baseEnd_7065864 < baseStart_7065864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065882 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2]
def baseStart_7065882 : Nat := 118140960795 + 7065882 * 2 ^ 59
def prefixEnd_7065882 : Nat := 4983230072969 + 3 ^ 40 * 7065882 * 2
def baseEnd_7065882 : Nat := 3628193713952228937879607

theorem tailTrace_7065882 : CollatzResearch.WordTrace tailWord_7065882 prefixEnd_7065882 3628193713952228937879607 := by
  unfold tailWord_7065882
  simp only [CollatzResearch.WordTrace]
  refine ⟨64428472146880936353977975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171809259058349163610607933 64428472146880936353977975)
  ·
    refine ⟨96642708220321404530966963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64428472146880936353977975 96642708220321404530966963)
    ·
      refine ⟨144964062330482106796450445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96642708220321404530966963 144964062330482106796450445)
      ·
        refine ⟨54361523373930790048668917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144964062330482106796450445 54361523373930790048668917)
        ·
          refine ⟨5096392816306011567062711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54361523373930790048668917 5096392816306011567062711)
          ·
            refine ⟨7644589224459017350594067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096392816306011567062711 7644589224459017350594067)
            ·
              refine ⟨11466883836688526025891101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644589224459017350594067 11466883836688526025891101)
              ·
                refine ⟨4300081438758197259709163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11466883836688526025891101 4300081438758197259709163)
                ·
                  refine ⟨6450122158137295889563745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300081438758197259709163 6450122158137295889563745)
                  ·
                    refine ⟨4837591618602971917172809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450122158137295889563745 4837591618602971917172809)
                    ·
                      refine ⟨3628193713952228937879607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837591618602971917172809 3628193713952228937879607)
                      ·
                        rfl

theorem cell23_7065882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_7065882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065882 prefixEnd_7065882 := by exact prefixLift 7065882
  have htrace : WordTrace (prefixWord ++ tailWord_7065882) baseStart_7065882 baseEnd_7065882 := by
    simpa [prefixWord, tailWord_7065882, baseEnd_7065882] using wordTrace_append hprefix tailTrace_7065882
  have hstable : (prefixWord ++ tailWord_7065882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065882).length < 2 ^ (prefixWord ++ tailWord_7065882).sum := by decide
  have hdescent : baseEnd_7065882 < baseStart_7065882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065907 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 3]
def baseStart_7065907 : Nat := 118140960795 + 7065907 * 2 ^ 59
def prefixEnd_7065907 : Nat := 4983230072969 + 3 ^ 40 * 7065907 * 2
def baseEnd_7065907 : Nat := 3628206550968591340066991

theorem tailTrace_7065907 : CollatzResearch.WordTrace tailWord_7065907 prefixEnd_7065907 3628206550968591340066991 := by
  unfold tailWord_7065907
  simp only [CollatzResearch.WordTrace]
  refine ⟨257714800412433174685571975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171809866941622116457047983 257714800412433174685571975)
  ·
    refine ⟨386572200618649762028357963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257714800412433174685571975 386572200618649762028357963)
    ·
      refine ⟨579858300927974643042536945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386572200618649762028357963 579858300927974643042536945)
      ·
        refine ⟨434893725695980982281902709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579858300927974643042536945 434893725695980982281902709)
        ·
          refine ⟨40771286783998217088928379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 434893725695980982281902709 40771286783998217088928379)
          ·
            refine ⟨61156930175997325633392569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40771286783998217088928379 61156930175997325633392569)
            ·
              refine ⟨45867697631997994225044427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61156930175997325633392569 45867697631997994225044427)
              ·
                refine ⟨68801546447996991337566641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45867697631997994225044427 68801546447996991337566641)
                ·
                  refine ⟨51601159835997743503174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68801546447996991337566641 51601159835997743503174981)
                  ·
                    refine ⟨9675217469249576906845309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51601159835997743503174981 9675217469249576906845309)
                    ·
                      refine ⟨3628206550968591340066991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675217469249576906845309 3628206550968591340066991)
                      ·
                        rfl

theorem cell23_7065907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_7065907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065907 prefixEnd_7065907 := by exact prefixLift 7065907
  have htrace : WordTrace (prefixWord ++ tailWord_7065907) baseStart_7065907 baseEnd_7065907 := by
    simpa [prefixWord, tailWord_7065907, baseEnd_7065907] using wordTrace_append hprefix tailTrace_7065907
  have hstable : (prefixWord ++ tailWord_7065907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065907).length < 2 ^ (prefixWord ++ tailWord_7065907).sum := by decide
  have hdescent : baseEnd_7065907 < baseStart_7065907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065950 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7065950 : Nat := 118140960795 + 7065950 * 2 ^ 59
def prefixEnd_7065950 : Nat := 4983230072969 + 3 ^ 40 * 7065950 * 2
def baseEnd_7065950 : Nat := 3628228630636734671829295

theorem tailTrace_7065950 : CollatzResearch.WordTrace tailWord_7065950 prefixEnd_7065950 3628228630636734671829295 := by
  unfold tailWord_7065950
  simp only [CollatzResearch.WordTrace]
  refine ⟨32214546093909674128673413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171810912500851595352924869 32214546093909674128673413)
  ·
    refine ⟨6040227392608063899126265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32214546093909674128673413 6040227392608063899126265)
    ·
      refine ⟨4530170544456047924344699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6040227392608063899126265 4530170544456047924344699)
      ·
        refine ⟨6795255816684071886517049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530170544456047924344699 6795255816684071886517049)
        ·
          refine ⟨5096441862513053914887787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6795255816684071886517049 5096441862513053914887787)
          ·
            refine ⟨7644662793769580872331681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096441862513053914887787 7644662793769580872331681)
            ·
              refine ⟨5733497095327185654248761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644662793769580872331681 5733497095327185654248761)
              ·
                refine ⟨4300122821495389240686571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5733497095327185654248761 4300122821495389240686571)
                ·
                  refine ⟨6450184232243083861029857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300122821495389240686571 6450184232243083861029857)
                  ·
                    refine ⟨4837638174182312895772393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450184232243083861029857 4837638174182312895772393)
                    ·
                      refine ⟨3628228630636734671829295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837638174182312895772393 3628228630636734671829295)
                      ·
                        rfl

theorem cell23_7065950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7065950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065950 prefixEnd_7065950 := by exact prefixLift 7065950
  have htrace : WordTrace (prefixWord ++ tailWord_7065950) baseStart_7065950 baseEnd_7065950 := by
    simpa [prefixWord, tailWord_7065950, baseEnd_7065950] using wordTrace_append hprefix tailTrace_7065950
  have hstable : (prefixWord ++ tailWord_7065950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065950).length < 2 ^ (prefixWord ++ tailWord_7065950).sum := by decide
  have hdescent : baseEnd_7065950 < baseStart_7065950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7065977 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_7065977 : Nat := 118140960795 + 7065977 * 2 ^ 59
def prefixEnd_7065977 : Nat := 4983230072969 + 3 ^ 40 * 7065977 * 2
def baseEnd_7065977 : Nat := 3628242494614406066191669

theorem tailTrace_7065977 : CollatzResearch.WordTrace tailWord_7065977 prefixEnd_7065977 3628242494614406066191669 := by
  unfold tailWord_7065977
  simp only [CollatzResearch.WordTrace]
  refine ⟨257717353522179576640620185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171811569014786384427080123 257717353522179576640620185)
  ·
    refine ⟨193288015141634682480465139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257717353522179576640620185 193288015141634682480465139)
    ·
      refine ⟨289932022712452023720697709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193288015141634682480465139 289932022712452023720697709)
      ·
        refine ⟨108724508517169508895261641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289932022712452023720697709 108724508517169508895261641)
        ·
          refine ⟨81543381387877131671446231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108724508517169508895261641 81543381387877131671446231)
          ·
            refine ⟨122315072081815697507169347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81543381387877131671446231 122315072081815697507169347)
            ·
              refine ⟨183472608122723546260754021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122315072081815697507169347 183472608122723546260754021)
              ·
                refine ⟨34401114023010664923891379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183472608122723546260754021 34401114023010664923891379)
                ·
                  refine ⟨51601671034515997385837069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34401114023010664923891379 51601671034515997385837069)
                  ·
                    refine ⟨19350626637943499019688901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51601671034515997385837069 19350626637943499019688901)
                    ·
                      refine ⟨3628242494614406066191669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19350626637943499019688901 3628242494614406066191669)
                      ·
                        rfl

theorem cell23_7065977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_7065977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7065977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7065977 prefixEnd_7065977 := by exact prefixLift 7065977
  have htrace : WordTrace (prefixWord ++ tailWord_7065977) baseStart_7065977 baseEnd_7065977 := by
    simpa [prefixWord, tailWord_7065977, baseEnd_7065977] using wordTrace_append hprefix tailTrace_7065977
  have hstable : (prefixWord ++ tailWord_7065977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7065977).length < 2 ^ (prefixWord ++ tailWord_7065977).sum := by decide
  have hdescent : baseEnd_7065977 < baseStart_7065977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7065977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066006 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7066006 : Nat := 118140960795 + 7066006 * 2 ^ 59
def prefixEnd_7066006 : Nat := 4983230072969 + 3 ^ 40 * 7066006 * 2
def baseEnd_7066006 : Nat := 3628257385553386452729037

theorem tailTrace_7066006 : CollatzResearch.WordTrace tailWord_7066006 prefixEnd_7066006 3628257385553386452729037 := by
  unfold tailWord_7066006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107400702442157162089117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171812274159383009728950581 16107400702442157162089117)
  ·
    refine ⟨6040275263415808935783419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16107400702442157162089117 6040275263415808935783419)
    ·
      refine ⟨9060412895123713403675129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6040275263415808935783419 9060412895123713403675129)
      ·
        refine ⟨6795309671342785052756347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9060412895123713403675129 6795309671342785052756347)
        ·
          refine ⟨10192964507014177579134521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795309671342785052756347 10192964507014177579134521)
          ·
            refine ⟨7644723380260633184350891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10192964507014177579134521 7644723380260633184350891)
            ·
              refine ⟨11467085070390949776526337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644723380260633184350891 11467085070390949776526337)
              ·
                refine ⟨8600313802793212332394753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11467085070390949776526337 8600313802793212332394753)
                ·
                  refine ⟨6450235352094909249296065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600313802793212332394753 6450235352094909249296065)
                  ·
                    refine ⟨4837676514071181936972049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450235352094909249296065 4837676514071181936972049)
                    ·
                      refine ⟨3628257385553386452729037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837676514071181936972049 3628257385553386452729037)
                      ·
                        rfl

theorem cell23_7066006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7066006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066006 prefixEnd_7066006 := by exact prefixLift 7066006
  have htrace : WordTrace (prefixWord ++ tailWord_7066006) baseStart_7066006 baseEnd_7066006 := by
    simpa [prefixWord, tailWord_7066006, baseEnd_7066006] using wordTrace_append hprefix tailTrace_7066006
  have hstable : (prefixWord ++ tailWord_7066006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066006).length < 2 ^ (prefixWord ++ tailWord_7066006).sum := by decide
  have hdescent : baseEnd_7066006 < baseStart_7066006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066007 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_7066007 : Nat := 118140960795 + 7066007 * 2 ^ 59
def prefixEnd_7066007 : Nat := 4983230072969 + 3 ^ 40 * 7066007 * 2
def baseEnd_7066007 : Nat := 3628257899034040948816531

theorem tailTrace_7066007 : CollatzResearch.WordTrace tailWord_7066007 prefixEnd_7066007 3628257899034040948816531 := by
  unfold tailWord_7066007
  simp only [CollatzResearch.WordTrace]
  refine ⟨257718447712070891764212275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171812298474713927842808183 257718447712070891764212275)
  ·
    refine ⟨386577671568106337646318413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257718447712070891764212275 386577671568106337646318413)
    ·
      refine ⟨144966626838039876617369405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386577671568106337646318413 144966626838039876617369405)
      ·
        refine ⟨54362485064264953731513527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144966626838039876617369405 54362485064264953731513527)
        ·
          refine ⟨81543727596397430597270291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54362485064264953731513527 81543727596397430597270291)
          ·
            refine ⟨122315591394596145895905437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81543727596397430597270291 122315591394596145895905437)
            ·
              refine ⟨45868346772973554710964539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122315591394596145895905437 45868346772973554710964539)
              ·
                refine ⟨68802520159460332066446809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45868346772973554710964539 68802520159460332066446809)
                ·
                  refine ⟨51601890119595249049835107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68802520159460332066446809 51601890119595249049835107)
                  ·
                    refine ⟨77402835179392873574752661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51601890119595249049835107 77402835179392873574752661)
                    ·
                      refine ⟨3628257899034040948816531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77402835179392873574752661 3628257899034040948816531)
                      ·
                        rfl

theorem cell23_7066007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_7066007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066007 prefixEnd_7066007 := by exact prefixLift 7066007
  have htrace : WordTrace (prefixWord ++ tailWord_7066007) baseStart_7066007 baseEnd_7066007 := by
    simpa [prefixWord, tailWord_7066007, baseEnd_7066007] using wordTrace_append hprefix tailTrace_7066007
  have hstable : (prefixWord ++ tailWord_7066007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066007).length < 2 ^ (prefixWord ++ tailWord_7066007).sum := by decide
  have hdescent : baseEnd_7066007 < baseStart_7066007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066021 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_7066021 : Nat := 118140960795 + 7066021 * 2 ^ 59
def prefixEnd_7066021 : Nat := 4983230072969 + 3 ^ 40 * 7066021 * 2
def baseEnd_7066021 : Nat := 1209421695921067964680489

theorem tailTrace_7066021 : CollatzResearch.WordTrace tailWord_7066021 prefixEnd_7066021 1209421695921067964680489 := by
  unfold tailWord_7066021
  simp only [CollatzResearch.WordTrace]
  refine ⟨257718958334020172155221917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171812638889346781436814611 257718958334020172155221917)
  ·
    refine ⟨96644609375257564558208219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257718958334020172155221917 96644609375257564558208219)
    ·
      refine ⟨144966914062886346837312329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96644609375257564558208219 144966914062886346837312329)
      ·
        refine ⟨108725185547164760127984247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144966914062886346837312329 108725185547164760127984247)
        ·
          refine ⟨163087778320747140191976371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108725185547164760127984247 163087778320747140191976371)
          ·
            refine ⟨244631667481120710287964557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163087778320747140191976371 244631667481120710287964557)
            ·
              refine ⟨91736875305420266357986709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244631667481120710287964557 91736875305420266357986709)
              ·
                refine ⟨4300166029941574985530627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91736875305420266357986709 4300166029941574985530627)
                ·
                  refine ⟨6450249044912362478295941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300166029941574985530627 6450249044912362478295941)
                  ·
                    refine ⟨1209421695921067964680489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6450249044912362478295941 1209421695921067964680489)
                    ·
                      rfl

theorem cell23_7066021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_7066021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066021 prefixEnd_7066021 := by exact prefixLift 7066021
  have htrace : WordTrace (prefixWord ++ tailWord_7066021) baseStart_7066021 baseEnd_7066021 := by
    simpa [prefixWord, tailWord_7066021, baseEnd_7066021] using wordTrace_append hprefix tailTrace_7066021
  have hstable : (prefixWord ++ tailWord_7066021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066021).length < 2 ^ (prefixWord ++ tailWord_7066021).sum := by decide
  have hdescent : baseEnd_7066021 < baseStart_7066021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066067 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4]
def baseStart_7066067 : Nat := 118140960795 + 7066067 * 2 ^ 59
def prefixEnd_7066067 : Nat := 4983230072969 + 3 ^ 40 * 7066067 * 2
def baseEnd_7066067 : Nat := 3628288707873310714066255

theorem tailTrace_7066067 : CollatzResearch.WordTrace tailWord_7066067 prefixEnd_7066067 3628288707873310714066255 := by
  unfold tailWord_7066067
  simp only [CollatzResearch.WordTrace]
  refine ⟨257720636091853522011396455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171813757394569014674264303 257720636091853522011396455)
  ·
    refine ⟨386580954137780283017094683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257720636091853522011396455 386580954137780283017094683)
    ·
      refine ⟨579871431206670424525642025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386580954137780283017094683 579871431206670424525642025)
      ·
        refine ⟨434903573405002818394231519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579871431206670424525642025 434903573405002818394231519)
        ·
          refine ⟨652355360107504227591347279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434903573405002818394231519 652355360107504227591347279)
          ·
            refine ⟨978533040161256341387020919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652355360107504227591347279 978533040161256341387020919)
            ·
              refine ⟨1467799560241884512080531379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978533040161256341387020919 1467799560241884512080531379)
              ·
                refine ⟨2201699340362826768120797069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467799560241884512080531379 2201699340362826768120797069)
                ·
                  refine ⟨825637252636060038045298901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2201699340362826768120797069 825637252636060038045298901)
                  ·
                    refine ⟨19350873108657657141686693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 825637252636060038045298901 19350873108657657141686693)
                    ·
                      refine ⟨3628288707873310714066255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19350873108657657141686693 3628288707873310714066255)
                      ·
                        rfl

theorem cell23_7066067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_7066067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066067 prefixEnd_7066067 := by exact prefixLift 7066067
  have htrace : WordTrace (prefixWord ++ tailWord_7066067) baseStart_7066067 baseEnd_7066067 := by
    simpa [prefixWord, tailWord_7066067, baseEnd_7066067] using wordTrace_append hprefix tailTrace_7066067
  have hstable : (prefixWord ++ tailWord_7066067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066067).length < 2 ^ (prefixWord ++ tailWord_7066067).sum := by decide
  have hdescent : baseEnd_7066067 < baseStart_7066067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066085 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 6]
def baseStart_7066085 : Nat := 118140960795 + 7066085 * 2 ^ 59
def prefixEnd_7066085 : Nat := 4983230072969 + 3 ^ 40 * 7066085 * 2
def baseEnd_7066085 : Nat := 403144216725010182626797

theorem tailTrace_7066085 : CollatzResearch.WordTrace tailWord_7066085 prefixEnd_7066085 403144216725010182626797 := by
  unfold tailWord_7066085
  simp only [CollatzResearch.WordTrace]
  refine ⟨257721292605788311085551709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171814195070525540723701139 257721292605788311085551709)
  ·
    refine ⟨96645484727170616657081891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257721292605788311085551709 96645484727170616657081891)
    ·
      refine ⟨144968227090755924985622837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96645484727170616657081891 144968227090755924985622837)
      ·
        refine ⟨13590771289758367967402141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144968227090755924985622837 13590771289758367967402141)
        ·
          refine ⟨5096539233659387987775803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13590771289758367967402141 5096539233659387987775803)
          ·
            refine ⟨7644808850489081981663705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096539233659387987775803 7644808850489081981663705)
            ·
              refine ⟨5733606637866811486247779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644808850489081981663705 5733606637866811486247779)
              ·
                refine ⟨8600409956800217229371669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733606637866811486247779 8600409956800217229371669)
                ·
                  refine ⟨403144216725010182626797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8600409956800217229371669 403144216725010182626797)
                  ·
                    rfl

theorem cell23_7066085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_7066085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066085 prefixEnd_7066085 := by exact prefixLift 7066085
  have htrace : WordTrace (prefixWord ++ tailWord_7066085) baseStart_7066085 baseEnd_7066085 := by
    simpa [prefixWord, tailWord_7066085, baseEnd_7066085] using wordTrace_append hprefix tailTrace_7066085
  have hstable : (prefixWord ++ tailWord_7066085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066085).length < 2 ^ (prefixWord ++ tailWord_7066085).sum := by decide
  have hdescent : baseEnd_7066085 < baseStart_7066085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066141 : List Nat := [1, 4, 2, 2, 1, 4, 1, 8]
def baseStart_7066141 : Nat := 118140960795 + 7066141 * 2 ^ 59
def prefixEnd_7066141 : Nat := 4983230072969 + 3 ^ 40 * 7066141 * 2
def baseEnd_7066141 : Nat := 134382470571916423131145

theorem tailTrace_7066141 : CollatzResearch.WordTrace tailWord_7066141 prefixEnd_7066141 134382470571916423131145 := by
  unfold tailWord_7066141
  simp only [CollatzResearch.WordTrace]
  refine ⟨257723335093585432649590277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171815556729056955099726851 257723335093585432649590277)
  ·
    refine ⟨48323125330047268621798177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257723335093585432649590277 48323125330047268621798177)
    ·
      refine ⟨36242343997535451466348633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48323125330047268621798177 36242343997535451466348633)
      ·
        refine ⟨27181757998151588599761475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36242343997535451466348633 27181757998151588599761475)
        ·
          refine ⟨40772636997227382899642213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27181757998151588599761475 40772636997227382899642213)
          ·
            refine ⟨7644869436980134293682915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40772636997227382899642213 7644869436980134293682915)
            ·
              refine ⟨11467304155470201440524373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644869436980134293682915 11467304155470201440524373)
              ·
                refine ⟨134382470571916423131145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11467304155470201440524373 134382470571916423131145)
                ·
                  rfl

theorem cell23_7066141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 8].length) (baseStart_7066141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066141 prefixEnd_7066141 := by exact prefixLift 7066141
  have htrace : WordTrace (prefixWord ++ tailWord_7066141) baseStart_7066141 baseEnd_7066141 := by
    simpa [prefixWord, tailWord_7066141, baseEnd_7066141] using wordTrace_append hprefix tailTrace_7066141
  have hstable : (prefixWord ++ tailWord_7066141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066141).length < 2 ^ (prefixWord ++ tailWord_7066141).sum := by decide
  have hdescent : baseEnd_7066141 < baseStart_7066141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066158 : List Nat := [4, 1, 3, 1, 3, 1, 3, 7]
def baseStart_7066158 : Nat := 118140960795 + 7066158 * 2 ^ 59
def prefixEnd_7066158 : Nat := 4983230072969 + 3 ^ 40 * 7066158 * 2
def baseEnd_7066158 : Nat := 134382793874550735482531

theorem tailTrace_7066158 : CollatzResearch.WordTrace tailWord_7066158 prefixEnd_7066158 134382793874550735482531 := by
  unfold tailWord_7066158
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215494391815480569119891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171815970089682563035306085 32215494391815480569119891)
  ·
    refine ⟨48323241587723220853679837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32215494391815480569119891 48323241587723220853679837)
    ·
      refine ⟨18121215595396207820129939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48323241587723220853679837 18121215595396207820129939)
      ·
        refine ⟨27181823393094311730194909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18121215595396207820129939 27181823393094311730194909)
        ·
          refine ⟨10193183772410366898823091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27181823393094311730194909 10193183772410366898823091)
          ·
            refine ⟨15289775658615550348234637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10193183772410366898823091 15289775658615550348234637)
            ·
              refine ⟨5733665871980831380587989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15289775658615550348234637 5733665871980831380587989)
              ·
                refine ⟨134382793874550735482531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5733665871980831380587989 134382793874550735482531)
                ·
                  rfl

theorem cell23_7066158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_7066158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066158 prefixEnd_7066158 := by exact prefixLift 7066158
  have htrace : WordTrace (prefixWord ++ tailWord_7066158) baseStart_7066158 baseEnd_7066158 := by
    simpa [prefixWord, tailWord_7066158, baseEnd_7066158] using wordTrace_append hprefix tailTrace_7066158
  have hstable : (prefixWord ++ tailWord_7066158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066158).length < 2 ^ (prefixWord ++ tailWord_7066158).sum := by decide
  have hdescent : baseEnd_7066158 < baseStart_7066158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066191 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 3, 4, 2]
def baseStart_7066191 : Nat := 118140960795 + 7066191 * 2 ^ 59
def prefixEnd_7066191 : Nat := 4983230072969 + 3 ^ 40 * 7066191 * 2
def baseEnd_7066191 : Nat := 3628352379474468228915685

theorem tailTrace_7066191 : CollatzResearch.WordTrace tailWord_7066191 prefixEnd_7066191 3628352379474468228915685 := by
  unfold tailWord_7066191
  simp only [CollatzResearch.WordTrace]
  refine ⟨257725158743404291188910427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171816772495602860792606951 257725158743404291188910427)
  ·
    refine ⟨386587738115106436783365641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257725158743404291188910427 386587738115106436783365641)
    ·
      refine ⟨289940803586329827587524231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386587738115106436783365641 289940803586329827587524231)
      ·
        refine ⟨434911205379494741381286347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289940803586329827587524231 434911205379494741381286347)
        ·
          refine ⟨652366808069242112071929521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434911205379494741381286347 652366808069242112071929521)
          ·
            refine ⟨489275106051931584053947141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652366808069242112071929521 489275106051931584053947141)
            ·
              refine ⟨91739082384737172010115089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489275106051931584053947141 91739082384737172010115089)
              ·
                refine ⟨68804311788552879007586317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91739082384737172010115089 68804311788552879007586317)
                ·
                  refine ⟨25801616920707329627844869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68804311788552879007586317 25801616920707329627844869)
                  ·
                    refine ⟨4837803172632624305220913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25801616920707329627844869 4837803172632624305220913)
                    ·
                      refine ⟨3628352379474468228915685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837803172632624305220913 3628352379474468228915685)
                      ·
                        rfl

theorem cell23_7066191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4, 2].length) (baseStart_7066191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066191 prefixEnd_7066191 := by exact prefixLift 7066191
  have htrace : WordTrace (prefixWord ++ tailWord_7066191) baseStart_7066191 baseEnd_7066191 := by
    simpa [prefixWord, tailWord_7066191, baseEnd_7066191] using wordTrace_append hprefix tailTrace_7066191
  have hstable : (prefixWord ++ tailWord_7066191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066191).length < 2 ^ (prefixWord ++ tailWord_7066191).sum := by decide
  have hdescent : baseEnd_7066191 < baseStart_7066191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066208 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 1, 4, 2]
def baseStart_7066208 : Nat := 118140960795 + 7066208 * 2 ^ 59
def prefixEnd_7066208 : Nat := 4983230072969 + 3 ^ 40 * 7066208 * 2
def baseEnd_7066208 : Nat := 3628361108645594662403107

theorem tailTrace_7066208 : CollatzResearch.WordTrace tailWord_7066208 prefixEnd_7066208 3628361108645594662403107 := by
  unfold tailWord_7066208
  simp only [CollatzResearch.WordTrace]
  refine ⟨128862889392171351546139639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171817185856228468728186185 128862889392171351546139639)
  ·
    refine ⟨193294334088257027319209459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128862889392171351546139639 193294334088257027319209459)
    ·
      refine ⟨289941501132385540978814189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193294334088257027319209459 289941501132385540978814189)
      ·
        refine ⟨108728062924644577867055321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289941501132385540978814189 108728062924644577867055321)
        ·
          refine ⟨81546047193483433400291491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108728062924644577867055321 81546047193483433400291491)
          ·
            refine ⟨122319070790225150100437237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81546047193483433400291491 122319070790225150100437237)
            ·
              refine ⟨11467412886583607821915991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122319070790225150100437237 11467412886583607821915991)
              ·
                refine ⟨17201119329875411732873987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467412886583607821915991 17201119329875411732873987)
                ·
                  refine ⟨25801678994813117599310981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17201119329875411732873987 25801678994813117599310981)
                  ·
                    refine ⟨4837814811527459549870809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25801678994813117599310981 4837814811527459549870809)
                    ·
                      refine ⟨3628361108645594662403107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837814811527459549870809 3628361108645594662403107)
                      ·
                        rfl

theorem cell23_7066208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_7066208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066208 prefixEnd_7066208 := by exact prefixLift 7066208
  have htrace : WordTrace (prefixWord ++ tailWord_7066208) baseStart_7066208 baseEnd_7066208 := by
    simpa [prefixWord, tailWord_7066208, baseEnd_7066208] using wordTrace_append hprefix tailTrace_7066208
  have hstable : (prefixWord ++ tailWord_7066208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066208).length < 2 ^ (prefixWord ++ tailWord_7066208).sum := by decide
  have hdescent : baseEnd_7066208 < baseStart_7066208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066281 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_7066281 : Nat := 118140960795 + 7066281 * 2 ^ 59
def prefixEnd_7066281 : Nat := 4983230072969 + 3 ^ 40 * 7066281 * 2
def baseEnd_7066281 : Nat := 3628398592733372876790271

theorem tailTrace_7066281 : CollatzResearch.WordTrace tailWord_7066281 prefixEnd_7066281 3628398592733372876790271 := by
  unfold tailWord_7066281
  simp only [CollatzResearch.WordTrace]
  refine ⟨257728441313078236559686697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171818960875385491039791131 257728441313078236559686697)
  ·
    refine ⟨193296330984808677419765023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257728441313078236559686697 193296330984808677419765023)
    ·
      refine ⟨289944496477213016129647535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193296330984808677419765023 289944496477213016129647535)
      ·
        refine ⟨434916744715819524194471303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289944496477213016129647535 434916744715819524194471303)
        ·
          refine ⟨652375117073729286291706955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434916744715819524194471303 652375117073729286291706955)
          ·
            refine ⟨978562675610593929437560433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652375117073729286291706955 978562675610593929437560433)
            ·
              refine ⟨733922006707945447078170325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978562675610593929437560433 733922006707945447078170325)
              ·
                refine ⟨17201297032217471415894617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 733922006707945447078170325 17201297032217471415894617)
                ·
                  refine ⟨12900972774163103561920963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17201297032217471415894617 12900972774163103561920963)
                  ·
                    refine ⟨19351459161244655342881445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12900972774163103561920963 19351459161244655342881445)
                    ·
                      refine ⟨3628398592733372876790271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19351459161244655342881445 3628398592733372876790271)
                      ·
                        rfl

theorem cell23_7066281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_7066281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066281 prefixEnd_7066281 := by exact prefixLift 7066281
  have htrace : WordTrace (prefixWord ++ tailWord_7066281) baseStart_7066281 baseEnd_7066281 := by
    simpa [prefixWord, tailWord_7066281, baseEnd_7066281] using wordTrace_append hprefix tailTrace_7066281
  have hstable : (prefixWord ++ tailWord_7066281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066281).length < 2 ^ (prefixWord ++ tailWord_7066281).sum := by decide
  have hdescent : baseEnd_7066281 < baseStart_7066281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066284 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7066284 : Nat := 118140960795 + 7066284 * 2 ^ 59
def prefixEnd_7066284 : Nat := 4983230072969 + 3 ^ 40 * 7066284 * 2
def baseEnd_7066284 : Nat := 3628400133175336365052757

theorem tailTrace_7066284 : CollatzResearch.WordTrace tailWord_7066284 prefixEnd_7066284 3628400133175336365052757 := by
  unfold tailWord_7066284
  simp only [CollatzResearch.WordTrace]
  refine ⟨128864275366033684036022953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171819033821378245381363937 128864275366033684036022953)
  ·
    refine ⟨96648206524525263027017215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128864275366033684036022953 96648206524525263027017215)
    ·
      refine ⟨144972309786787894540525823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96648206524525263027017215 144972309786787894540525823)
      ·
        refine ⟨217458464680181841810788735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144972309786787894540525823 217458464680181841810788735)
        ·
          refine ⟨326187697020272762716183103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217458464680181841810788735 326187697020272762716183103)
          ·
            refine ⟨489281545530409144074274655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326187697020272762716183103 489281545530409144074274655)
            ·
              refine ⟨733922318295613716111411983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489281545530409144074274655 733922318295613716111411983)
              ·
                refine ⟨1100883477443420574167117975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733922318295613716111411983 1100883477443420574167117975)
                ·
                  refine ⟨1651325216165130861250676963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100883477443420574167117975 1651325216165130861250676963)
                  ·
                    refine ⟨2476987824247696291876015445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651325216165130861250676963 2476987824247696291876015445)
                    ·
                      refine ⟨3628400133175336365052757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2476987824247696291876015445 3628400133175336365052757)
                      ·
                        rfl

theorem cell23_7066284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7066284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066284 prefixEnd_7066284 := by exact prefixLift 7066284
  have htrace : WordTrace (prefixWord ++ tailWord_7066284) baseStart_7066284 baseEnd_7066284 := by
    simpa [prefixWord, tailWord_7066284, baseEnd_7066284] using wordTrace_append hprefix tailTrace_7066284
  have hstable : (prefixWord ++ tailWord_7066284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066284).length < 2 ^ (prefixWord ++ tailWord_7066284).sum := by decide
  have hdescent : baseEnd_7066284 < baseStart_7066284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066298 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2]
def baseStart_7066298 : Nat := 118140960795 + 7066298 * 2 ^ 59
def prefixEnd_7066298 : Nat := 4983230072969 + 3 ^ 40 * 7066298 * 2
def baseEnd_7066298 : Nat := 3628407321904499310277693

theorem tailTrace_7066298 : CollatzResearch.WordTrace tailWord_7066298 prefixEnd_7066298 3628407321904499310277693 := by
  unfold tailWord_7066298
  simp only [CollatzResearch.WordTrace]
  refine ⟨64432265338504162115763887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171819374236011098975370365 64432265338504162115763887)
  ·
    refine ⟨96648398007756243173645831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64432265338504162115763887 96648398007756243173645831)
    ·
      refine ⟨144972597011634364760468747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96648398007756243173645831 144972597011634364760468747)
      ·
        refine ⟨217458895517451547140703121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144972597011634364760468747 217458895517451547140703121)
        ·
          refine ⟨163094171638088660355527341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217458895517451547140703121 163094171638088660355527341)
          ·
            refine ⟨61160314364283247633322753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163094171638088660355527341 61160314364283247633322753)
            ·
              refine ⟨45870235773212435724992065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61160314364283247633322753 45870235773212435724992065)
              ·
                refine ⟨34402676829909326793744049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45870235773212435724992065 34402676829909326793744049)
                ·
                  refine ⟨25802007622431995095308037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34402676829909326793744049 25802007622431995095308037)
                  ·
                    refine ⟨4837876429205999080370257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25802007622431995095308037 4837876429205999080370257)
                    ·
                      refine ⟨3628407321904499310277693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837876429205999080370257 3628407321904499310277693)
                      ·
                        rfl

theorem cell23_7066298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_7066298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066298 prefixEnd_7066298 := by exact prefixLift 7066298
  have htrace : WordTrace (prefixWord ++ tailWord_7066298) baseStart_7066298 baseEnd_7066298 := by
    simpa [prefixWord, tailWord_7066298, baseEnd_7066298] using wordTrace_append hprefix tailTrace_7066298
  have hstable : (prefixWord ++ tailWord_7066298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066298).length < 2 ^ (prefixWord ++ tailWord_7066298).sum := by decide
  have hdescent : baseEnd_7066298 < baseStart_7066298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066321 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 6]
def baseStart_7066321 : Nat := 118140960795 + 7066321 * 2 ^ 59
def prefixEnd_7066321 : Nat := 4983230072969 + 3 ^ 40 * 7066321 * 2
def baseEnd_7066321 : Nat := 403157681328839191143343

theorem tailTrace_7066321 : CollatzResearch.WordTrace tailWord_7066321 prefixEnd_7066321 403157681328839191143343 := by
  unfold tailWord_7066321
  simp only [CollatzResearch.WordTrace]
  refine ⟨257729900232933323391142817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171819933488622215594095211 257729900232933323391142817)
  ·
    refine ⟨193297425174699992543357113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257729900232933323391142817 193297425174699992543357113)
    ·
      refine ⟨144973068881024994407517835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193297425174699992543357113 144973068881024994407517835)
      ·
        refine ⟨217459603321537491611276753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144973068881024994407517835 217459603321537491611276753)
        ·
          refine ⟨163094702491153118708457565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217459603321537491611276753 163094702491153118708457565)
          ·
            refine ⟨61160513434182419515671587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163094702491153118708457565 61160513434182419515671587)
            ·
              refine ⟨91740770151273629273507381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61160513434182419515671587 91740770151273629273507381)
              ·
                refine ⟨8600697201681902744391317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91740770151273629273507381 8600697201681902744391317)
                ·
                  refine ⟨403157681328839191143343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8600697201681902744391317 403157681328839191143343)
                  ·
                    rfl

theorem cell23_7066321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 6].length) (baseStart_7066321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066321 prefixEnd_7066321 := by exact prefixLift 7066321
  have htrace : WordTrace (prefixWord ++ tailWord_7066321) baseStart_7066321 baseEnd_7066321 := by
    simpa [prefixWord, tailWord_7066321, baseEnd_7066321] using wordTrace_append hprefix tailTrace_7066321
  have hstable : (prefixWord ++ tailWord_7066321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066321).length < 2 ^ (prefixWord ++ tailWord_7066321).sum := by decide
  have hdescent : baseEnd_7066321 < baseStart_7066321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066332 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7066332 : Nat := 118140960795 + 7066332 * 2 ^ 59
def prefixEnd_7066332 : Nat := 4983230072969 + 3 ^ 40 * 7066332 * 2
def baseEnd_7066332 : Nat := 3628424780246752177252537

theorem tailTrace_7066332 : CollatzResearch.WordTrace tailWord_7066332 prefixEnd_7066332 3628424780246752177252537 := by
  unfold tailWord_7066332
  simp only [CollatzResearch.WordTrace]
  refine ⟨128865150717946736134896625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171820200957262314846528833 128865150717946736134896625)
  ·
    refine ⟨96648863038460052101172469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128865150717946736134896625 96648863038460052101172469)
    ·
      refine ⟨9060830909855629884484919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96648863038460052101172469 9060830909855629884484919)
      ·
        refine ⟨13591246364783444826727379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060830909855629884484919 13591246364783444826727379)
        ·
          refine ⟨20386869547175167240091069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591246364783444826727379 20386869547175167240091069)
          ·
            refine ⟨7645076080190687715034151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20386869547175167240091069 7645076080190687715034151)
            ·
              refine ⟨11467614120286031572551227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645076080190687715034151 11467614120286031572551227)
              ·
                refine ⟨17201421180429047358826841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467614120286031572551227 17201421180429047358826841)
                ·
                  refine ⟨12901065885321785519120131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17201421180429047358826841 12901065885321785519120131)
                  ·
                    refine ⟨19351598827982678278680197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12901065885321785519120131 19351598827982678278680197)
                    ·
                      refine ⟨3628424780246752177252537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19351598827982678278680197 3628424780246752177252537)
                      ·
                        rfl

theorem cell23_7066332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7066332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066332 prefixEnd_7066332 := by exact prefixLift 7066332
  have htrace : WordTrace (prefixWord ++ tailWord_7066332) baseStart_7066332 baseEnd_7066332 := by
    simpa [prefixWord, tailWord_7066332, baseEnd_7066332] using wordTrace_append hprefix tailTrace_7066332
  have hstable : (prefixWord ++ tailWord_7066332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066332).length < 2 ^ (prefixWord ++ tailWord_7066332).sum := by decide
  have hdescent : baseEnd_7066332 < baseStart_7066332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066335 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 3]
def baseStart_7066335 : Nat := 118140960795 + 7066335 * 2 ^ 59
def prefixEnd_7066335 : Nat := 4983230072969 + 3 ^ 40 * 7066335 * 2
def baseEnd_7066335 : Nat := 3628426320688715665515023

theorem tailTrace_7066335 : CollatzResearch.WordTrace tailWord_7066335 prefixEnd_7066335 3628426320688715665515023 := by
  unfold tailWord_7066335
  simp only [CollatzResearch.WordTrace]
  refine ⟨257730410854882603782152459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171820273903255069188101639 257730410854882603782152459)
  ·
    refine ⟨386595616282323905673228689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257730410854882603782152459 386595616282323905673228689)
    ·
      refine ⟨289946712211742929254921517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386595616282323905673228689 289946712211742929254921517)
      ·
        refine ⟨108730017079403598470595569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289946712211742929254921517 108730017079403598470595569)
        ·
          refine ⟨81547512809552698852946677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108730017079403598470595569 81547512809552698852946677)
          ·
            refine ⟨7645079325895565517463751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81547512809552698852946677 7645079325895565517463751)
            ·
              refine ⟨11467618988843348276195627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645079325895565517463751 11467618988843348276195627)
              ·
                refine ⟨17201428483265022414293441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467618988843348276195627 17201428483265022414293441)
                ·
                  refine ⟨12901071362448766810720081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17201428483265022414293441 12901071362448766810720081)
                  ·
                    refine ⟨9675803521836575108040061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12901071362448766810720081 9675803521836575108040061)
                    ·
                      refine ⟨3628426320688715665515023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675803521836575108040061 3628426320688715665515023)
                      ·
                        rfl

theorem cell23_7066335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_7066335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066335 prefixEnd_7066335 := by exact prefixLift 7066335
  have htrace : WordTrace (prefixWord ++ tailWord_7066335) baseStart_7066335 baseEnd_7066335 := by
    simpa [prefixWord, tailWord_7066335, baseEnd_7066335] using wordTrace_append hprefix tailTrace_7066335
  have hstable : (prefixWord ++ tailWord_7066335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066335).length < 2 ^ (prefixWord ++ tailWord_7066335).sum := by decide
  have hdescent : baseEnd_7066335 < baseStart_7066335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066348 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_7066348 : Nat := 118140960795 + 7066348 * 2 ^ 59
def prefixEnd_7066348 : Nat := 4983230072969 + 3 ^ 40 * 7066348 * 2
def baseEnd_7066348 : Nat := 3628432995937224114652463

theorem tailTrace_7066348 : CollatzResearch.WordTrace tailWord_7066348 prefixEnd_7066348 3628432995937224114652463 := by
  unfold tailWord_7066348
  simp only [CollatzResearch.WordTrace]
  refine ⟨128865442501917753501187849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171820590002557004668250465 128865442501917753501187849)
  ·
    refine ⟨96649081876438315125890887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128865442501917753501187849 96649081876438315125890887)
    ·
      refine ⟨144973622814657472688836331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96649081876438315125890887 144973622814657472688836331)
      ·
        refine ⟨217460434221986209033254497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144973622814657472688836331 217460434221986209033254497)
        ·
          refine ⟨163095325666489656774940873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217460434221986209033254497 163095325666489656774940873)
          ·
            refine ⟨122321494249867242581205655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163095325666489656774940873 122321494249867242581205655)
            ·
              refine ⟨183482241374800863871808483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122321494249867242581205655 183482241374800863871808483)
              ·
                refine ⟨275223362062201295807712725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183482241374800863871808483 275223362062201295807712725)
                ·
                  refine ⟨6450547548332842870493267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 275223362062201295807712725 6450547548332842870493267)
                  ·
                    refine ⟨9675821322499264305739901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6450547548332842870493267 9675821322499264305739901)
                    ·
                      refine ⟨3628432995937224114652463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675821322499264305739901 3628432995937224114652463)
                      ·
                        rfl

theorem cell23_7066348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_7066348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066348 prefixEnd_7066348 := by exact prefixLift 7066348
  have htrace : WordTrace (prefixWord ++ tailWord_7066348) baseStart_7066348 baseEnd_7066348 := by
    simpa [prefixWord, tailWord_7066348, baseEnd_7066348] using wordTrace_append hprefix tailTrace_7066348
  have hstable : (prefixWord ++ tailWord_7066348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066348).length < 2 ^ (prefixWord ++ tailWord_7066348).sum := by decide
  have hdescent : baseEnd_7066348 < baseStart_7066348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066365 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_7066365 : Nat := 118140960795 + 7066365 * 2 ^ 59
def prefixEnd_7066365 : Nat := 4983230072969 + 3 ^ 40 * 7066365 * 2
def baseEnd_7066365 : Nat := 3628441725108350548139885

theorem tailTrace_7066365 : CollatzResearch.WordTrace tailWord_7066365 prefixEnd_7066365 3628441725108350548139885 := by
  unfold tailWord_7066365
  simp only [CollatzResearch.WordTrace]
  refine ⟨257731505044773918905744549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171821003363182612603829699 257731505044773918905744549)
  ·
    refine ⟨48324657195895109794827103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257731505044773918905744549 48324657195895109794827103)
    ·
      refine ⟨72486985793842664692240655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48324657195895109794827103 72486985793842664692240655)
      ·
        refine ⟨108730478690763997038360983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72486985793842664692240655 108730478690763997038360983)
        ·
          refine ⟨163095718036145995557541475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108730478690763997038360983 163095718036145995557541475)
          ·
            refine ⟨244643577054218993336312213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163095718036145995557541475 244643577054218993336312213)
            ·
              refine ⟨11467667674416515312639635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244643577054218993336312213 11467667674416515312639635)
              ·
                refine ⟨17201501511624772968959453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467667674416515312639635 17201501511624772968959453)
                ·
                  refine ⟨6450563066859289863359795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17201501511624772968959453 6450563066859289863359795)
                  ·
                    refine ⟨9675844600288934795039693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6450563066859289863359795 9675844600288934795039693)
                    ·
                      refine ⟨3628441725108350548139885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675844600288934795039693 3628441725108350548139885)
                      ·
                        rfl

theorem cell23_7066365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_7066365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066365 prefixEnd_7066365 := by exact prefixLift 7066365
  have htrace : WordTrace (prefixWord ++ tailWord_7066365) baseStart_7066365 baseEnd_7066365 := by
    simpa [prefixWord, tailWord_7066365, baseEnd_7066365] using wordTrace_append hprefix tailTrace_7066365
  have hstable : (prefixWord ++ tailWord_7066365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066365).length < 2 ^ (prefixWord ++ tailWord_7066365).sum := by decide
  have hdescent : baseEnd_7066365 < baseStart_7066365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066375 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7066375 : Nat := 118140960795 + 7066375 * 2 ^ 59
def prefixEnd_7066375 : Nat := 4983230072969 + 3 ^ 40 * 7066375 * 2
def baseEnd_7066375 : Nat := 3628446859914895509014839

theorem tailTrace_7066375 : CollatzResearch.WordTrace tailWord_7066375 prefixEnd_7066375 3628446859914895509014839 := by
  unfold tailWord_7066375
  simp only [CollatzResearch.WordTrace]
  refine ⟨257731869774737690613608579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171821246516491793742405719 257731869774737690613608579)
  ·
    refine ⟨386597804662106535920412869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257731869774737690613608579 386597804662106535920412869)
    ·
      refine ⟨72487088374144975485077413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386597804662106535920412869 72487088374144975485077413)
      ·
        refine ⟨13591329070152182903452015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72487088374144975485077413 13591329070152182903452015)
        ·
          refine ⟨20386993605228274355178023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591329070152182903452015 20386993605228274355178023)
          ·
            refine ⟨30580490407842411532767035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20386993605228274355178023 30580490407842411532767035)
            ·
              refine ⟨45870735611763617299150553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30580490407842411532767035 45870735611763617299150553)
              ·
                refine ⟨34403051708822712974362915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45870735611763617299150553 34403051708822712974362915)
                ·
                  refine ⟨51604577563234069461544373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34403051708822712974362915 51604577563234069461544373)
                  ·
                    refine ⟨4837929146553194012019785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51604577563234069461544373 4837929146553194012019785)
                    ·
                      refine ⟨3628446859914895509014839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4837929146553194012019785 3628446859914895509014839)
                      ·
                        rfl

theorem cell23_7066375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7066375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066375 prefixEnd_7066375 := by exact prefixLift 7066375
  have htrace : WordTrace (prefixWord ++ tailWord_7066375) baseStart_7066375 baseEnd_7066375 := by
    simpa [prefixWord, tailWord_7066375, baseEnd_7066375] using wordTrace_append hprefix tailTrace_7066375
  have hstable : (prefixWord ++ tailWord_7066375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066375).length < 2 ^ (prefixWord ++ tailWord_7066375).sum := by decide
  have hdescent : baseEnd_7066375 < baseStart_7066375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066399 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 1, 1, 3]
def baseStart_7066399 : Nat := 118140960795 + 7066399 * 2 ^ 59
def prefixEnd_7066399 : Nat := 4983230072969 + 3 ^ 40 * 7066399 * 2
def baseEnd_7066399 : Nat := 3628459183450603415114729

theorem tailTrace_7066399 : CollatzResearch.WordTrace tailWord_7066399 prefixEnd_7066399 3628459183450603415114729 := by
  unfold tailWord_7066399
  simp only [CollatzResearch.WordTrace]
  refine ⟨257732745126650742712482251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171821830084433828474988167 257732745126650742712482251)
  ·
    refine ⟨386599117689976114068723377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257732745126650742712482251 386599117689976114068723377)
    ·
      refine ⟨289949338267482085551542533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386599117689976114068723377 289949338267482085551542533)
      ·
        refine ⟨54365500925152891040914225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289949338267482085551542533 54365500925152891040914225)
        ·
          refine ⟨40774125693864668280685669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54365500925152891040914225 40774125693864668280685669)
          ·
            refine ⟨7645148567599625302628563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40774125693864668280685669 7645148567599625302628563)
            ·
              refine ⟨11467722851399437953942845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645148567599625302628563 11467722851399437953942845)
              ·
                refine ⟨4300396069274789232728567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11467722851399437953942845 4300396069274789232728567)
                ·
                  refine ⟨6450594103912183849092851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300396069274789232728567 6450594103912183849092851)
                  ·
                    refine ⟨9675891155868275773639277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6450594103912183849092851 9675891155868275773639277)
                    ·
                      refine ⟨3628459183450603415114729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675891155868275773639277 3628459183450603415114729)
                      ·
                        rfl

theorem cell23_7066399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_7066399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066399 prefixEnd_7066399 := by exact prefixLift 7066399
  have htrace : WordTrace (prefixWord ++ tailWord_7066399) baseStart_7066399 baseEnd_7066399 := by
    simpa [prefixWord, tailWord_7066399, baseEnd_7066399] using wordTrace_append hprefix tailTrace_7066399
  have hstable : (prefixWord ++ tailWord_7066399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066399).length < 2 ^ (prefixWord ++ tailWord_7066399).sum := by decide
  have hdescent : baseEnd_7066399 < baseStart_7066399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066436 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7066436 : Nat := 118140960795 + 7066436 * 2 ^ 59
def prefixEnd_7066436 : Nat := 4983230072969 + 3 ^ 40 * 7066436 * 2
def baseEnd_7066436 : Nat := 1209492727411606590117353

theorem tailTrace_7066436 : CollatzResearch.WordTrace tailWord_7066436 prefixEnd_7066436 1209492727411606590117353 := by
  unfold tailWord_7066436
  simp only [CollatzResearch.WordTrace]
  refine ⟨128867047313758349015789581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171822729751677798687719441 128867047313758349015789581)
  ·
    refine ⟨48325142742659380880921093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128867047313758349015789581 48325142742659380880921093)
    ·
      refine ⟨9060964264248633915172705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48325142742659380880921093 9060964264248633915172705)
      ·
        refine ⟨6795723198186475436379529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9060964264248633915172705 6795723198186475436379529)
        ·
          refine ⟨5096792398639856577284647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6795723198186475436379529 5096792398639856577284647)
          ·
            refine ⟨7645188597959784865926971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096792398639856577284647 7645188597959784865926971)
            ·
              refine ⟨11467782896939677298890457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645188597959784865926971 11467782896939677298890457)
              ·
                refine ⟨8600837172704757974167843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11467782896939677298890457 8600837172704757974167843)
                ·
                  refine ⟨12901255759057136961251765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8600837172704757974167843 12901255759057136961251765)
                  ·
                    refine ⟨1209492727411606590117353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12901255759057136961251765 1209492727411606590117353)
                    ·
                      rfl

theorem cell23_7066436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7066436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066436 prefixEnd_7066436 := by exact prefixLift 7066436
  have htrace : WordTrace (prefixWord ++ tailWord_7066436) baseStart_7066436 baseEnd_7066436 := by
    simpa [prefixWord, tailWord_7066436, baseEnd_7066436] using wordTrace_append hprefix tailTrace_7066436
  have hstable : (prefixWord ++ tailWord_7066436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066436).length < 2 ^ (prefixWord ++ tailWord_7066436).sum := by decide
  have hdescent : baseEnd_7066436 < baseStart_7066436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066451 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_7066451 : Nat := 118140960795 + 7066451 * 2 ^ 59
def prefixEnd_7066451 : Nat := 4983230072969 + 3 ^ 40 * 7066451 * 2
def baseEnd_7066451 : Nat := 3628485884444637211664489

theorem tailTrace_7066451 : CollatzResearch.WordTrace tailWord_7066451 prefixEnd_7066451 3628485884444637211664489 := by
  unfold tailWord_7066451
  simp only [CollatzResearch.WordTrace]
  refine ⟨257734641722462355593375207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171823094481641570395583471 257734641722462355593375207)
  ·
    refine ⟨386601962583693533390062811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257734641722462355593375207 386601962583693533390062811)
    ·
      refine ⟨579902943875540300085094217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386601962583693533390062811 579902943875540300085094217)
      ·
        refine ⟨434927207906655225063820663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579902943875540300085094217 434927207906655225063820663)
        ·
          refine ⟨652390811859982837595730995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434927207906655225063820663 652390811859982837595730995)
          ·
            refine ⟨978586217789974256393596493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652390811859982837595730995 978586217789974256393596493)
            ·
              refine ⟨366969831671240346147598685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 978586217789974256393596493 366969831671240346147598685)
              ·
                refine ⟨137613686876715129805349507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366969831671240346147598685 137613686876715129805349507)
                ·
                  refine ⟨206420530315072694708024261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137613686876715129805349507 206420530315072694708024261)
                  ·
                    refine ⟨38703849434076130257754549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206420530315072694708024261 38703849434076130257754549)
                    ·
                      refine ⟨3628485884444637211664489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38703849434076130257754549 3628485884444637211664489)
                      ·
                        rfl

theorem cell23_7066451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_7066451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066451 prefixEnd_7066451 := by exact prefixLift 7066451
  have htrace : WordTrace (prefixWord ++ tailWord_7066451) baseStart_7066451 baseEnd_7066451 := by
    simpa [prefixWord, tailWord_7066451, baseEnd_7066451] using wordTrace_append hprefix tailTrace_7066451
  have hstable : (prefixWord ++ tailWord_7066451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066451).length < 2 ^ (prefixWord ++ tailWord_7066451).sum := by decide
  have hdescent : baseEnd_7066451 < baseStart_7066451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066455 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_7066455 : Nat := 118140960795 + 7066455 * 2 ^ 59
def prefixEnd_7066455 : Nat := 4983230072969 + 3 ^ 40 * 7066455 * 2
def baseEnd_7066455 : Nat := 3628487938367255196014471

theorem tailTrace_7066455 : CollatzResearch.WordTrace tailWord_7066455 prefixEnd_7066455 3628487938367255196014471 := by
  unfold tailWord_7066455
  simp only [CollatzResearch.WordTrace]
  refine ⟨257734787614447864276520819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171823191742965242851013879 257734787614447864276520819)
  ·
    refine ⟨386602181421671796414781229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257734787614447864276520819 386602181421671796414781229)
    ·
      refine ⟨144975818033126923655542961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386602181421671796414781229 144975818033126923655542961)
      ·
        refine ⟨108731863524845192741657221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144975818033126923655542961 108731863524845192741657221)
        ·
          refine ⟨20387224410908473639060729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108731863524845192741657221 20387224410908473639060729)
          ·
            refine ⟨15290418308181355229295547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20387224410908473639060729 15290418308181355229295547)
            ·
              refine ⟨22935627462272032843943321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15290418308181355229295547 22935627462272032843943321)
              ·
                refine ⟨17201720596704024632957491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22935627462272032843943321 17201720596704024632957491)
                ·
                  refine ⟨25802580895056036949436237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17201720596704024632957491 25802580895056036949436237)
                  ·
                    refine ⟨9675967835646013856038589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25802580895056036949436237 9675967835646013856038589)
                    ·
                      refine ⟨3628487938367255196014471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675967835646013856038589 3628487938367255196014471)
                      ·
                        rfl

theorem cell23_7066455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_7066455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066455 prefixEnd_7066455 := by exact prefixLift 7066455
  have htrace : WordTrace (prefixWord ++ tailWord_7066455) baseStart_7066455 baseEnd_7066455 := by
    simpa [prefixWord, tailWord_7066455, baseEnd_7066455] using wordTrace_append hprefix tailTrace_7066455
  have hstable : (prefixWord ++ tailWord_7066455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066455).length < 2 ^ (prefixWord ++ tailWord_7066455).sum := by decide
  have hdescent : baseEnd_7066455 < baseStart_7066455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066472 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7066472 : Nat := 118140960795 + 7066472 * 2 ^ 59
def prefixEnd_7066472 : Nat := 4983230072969 + 3 ^ 40 * 7066472 * 2
def baseEnd_7066472 : Nat := 3628496667538381629501893

theorem tailTrace_7066472 : CollatzResearch.WordTrace tailWord_7066472 prefixEnd_7066472 3628496667538381629501893 := by
  unfold tailWord_7066472
  simp only [CollatzResearch.WordTrace]
  refine ⟨128867703827693138089944835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171823605103590850786593113 128867703827693138089944835)
  ·
    refine ⟨193301555741539707134917253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128867703827693138089944835 193301555741539707134917253)
    ·
      refine ⟨36244041701538695087796985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193301555741539707134917253 36244041701538695087796985)
      ·
        refine ⟨27183031276154021315847739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36244041701538695087796985 27183031276154021315847739)
        ·
          refine ⟨40774546914231031973771609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27183031276154021315847739 40774546914231031973771609)
          ·
            refine ⟨30580910185673273980328707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40774546914231031973771609 30580910185673273980328707)
            ·
              refine ⟨45871365278509910970493061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30580910185673273980328707 45871365278509910970493061)
              ·
                refine ⟨8600880989720608306967449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45871365278509910970493061 8600880989720608306967449)
                ·
                  refine ⟨6450660742290456230225587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600880989720608306967449 6450660742290456230225587)
                  ·
                    refine ⟨9675991113435684345338381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6450660742290456230225587 9675991113435684345338381)
                    ·
                      refine ⟨3628496667538381629501893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9675991113435684345338381 3628496667538381629501893)
                      ·
                        rfl

theorem cell23_7066472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7066472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066472 prefixEnd_7066472 := by exact prefixLift 7066472
  have htrace : WordTrace (prefixWord ++ tailWord_7066472) baseStart_7066472 baseEnd_7066472 := by
    simpa [prefixWord, tailWord_7066472, baseEnd_7066472] using wordTrace_append hprefix tailTrace_7066472
  have hstable : (prefixWord ++ tailWord_7066472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066472).length < 2 ^ (prefixWord ++ tailWord_7066472).sum := by decide
  have hdescent : baseEnd_7066472 < baseStart_7066472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066495 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 1, 4, 2]
def baseStart_7066495 : Nat := 118140960795 + 7066495 * 2 ^ 59
def prefixEnd_7066495 : Nat := 4983230072969 + 3 ^ 40 * 7066495 * 2
def baseEnd_7066495 : Nat := 3628508477593435039514287

theorem tailTrace_7066495 : CollatzResearch.WordTrace tailWord_7066495 prefixEnd_7066495 3628508477593435039514287 := by
  unfold tailWord_7066495
  simp only [CollatzResearch.WordTrace]
  refine ⟨257736246534302951107976939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171824164356201967405317959 257736246534302951107976939)
  ·
    refine ⟨386604369801454426661965409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257736246534302951107976939 386604369801454426661965409)
    ·
      refine ⟨289953277351090819996474057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386604369801454426661965409 289953277351090819996474057)
      ·
        refine ⟨217464958013318114997355543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289953277351090819996474057 217464958013318114997355543)
        ·
          refine ⟨326197437019977172496033315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217464958013318114997355543 326197437019977172496033315)
          ·
            refine ⟨489296155529965758744049973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326197437019977172496033315 489296155529965758744049973)
            ·
              refine ⟨45871514580934289882254685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 489296155529965758744049973 45871514580934289882254685)
              ·
                refine ⟨17201817967850358705845507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45871514580934289882254685 17201817967850358705845507)
                ·
                  refine ⟨25802726951775538058768261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17201817967850358705845507 25802726951775538058768261)
                  ·
                    refine ⟨4838011303457913386019049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25802726951775538058768261 4838011303457913386019049)
                    ·
                      refine ⟨3628508477593435039514287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838011303457913386019049 3628508477593435039514287)
                      ·
                        rfl

theorem cell23_7066495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_7066495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066495 prefixEnd_7066495 := by exact prefixLift 7066495
  have htrace : WordTrace (prefixWord ++ tailWord_7066495) baseStart_7066495 baseEnd_7066495 := by
    simpa [prefixWord, tailWord_7066495, baseEnd_7066495] using wordTrace_append hprefix tailTrace_7066495
  have hstable : (prefixWord ++ tailWord_7066495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066495).length < 2 ^ (prefixWord ++ tailWord_7066495).sum := by decide
  have hdescent : baseEnd_7066495 < baseStart_7066495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066529 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7066529 : Nat := 118140960795 + 7066529 * 2 ^ 59
def prefixEnd_7066529 : Nat := 4983230072969 + 3 ^ 40 * 7066529 * 2
def baseEnd_7066529 : Nat := 3628525935935687906489131

theorem tailTrace_7066529 : CollatzResearch.WordTrace tailWord_7066529 prefixEnd_7066529 3628525935935687906489131 := by
  unfold tailWord_7066529
  simp only [CollatzResearch.WordTrace]
  refine ⟨257737486616179774914714641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171824991077453183276476427 257737486616179774914714641)
  ·
    refine ⟨193303114962134831186035981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257737486616179774914714641 193303114962134831186035981)
    ·
      refine ⟨72488668110800561694763493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193303114962134831186035981 72488668110800561694763493)
      ·
        refine ⟨13591625270775105317768155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72488668110800561694763493 13591625270775105317768155)
        ·
          refine ⟨20387437906162657976652233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591625270775105317768155 20387437906162657976652233)
          ·
            refine ⟨15290578429621993482489175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20387437906162657976652233 15290578429621993482489175)
            ·
              refine ⟨22935867644432990223733763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15290578429621993482489175 22935867644432990223733763)
              ·
                refine ⟨34403801466649485335600645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22935867644432990223733763 34403801466649485335600645)
                ·
                  refine ⟨6450712774996778500425121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34403801466649485335600645 6450712774996778500425121)
                  ·
                    refine ⟨4838034581247583875318841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450712774996778500425121 4838034581247583875318841)
                    ·
                      refine ⟨3628525935935687906489131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838034581247583875318841 3628525935935687906489131)
                      ·
                        rfl

theorem cell23_7066529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7066529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066529 prefixEnd_7066529 := by exact prefixLift 7066529
  have htrace : WordTrace (prefixWord ++ tailWord_7066529) baseStart_7066529 baseEnd_7066529 := by
    simpa [prefixWord, tailWord_7066529, baseEnd_7066529] using wordTrace_append hprefix tailTrace_7066529
  have hstable : (prefixWord ++ tailWord_7066529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066529).length < 2 ^ (prefixWord ++ tailWord_7066529).sum := by decide
  have hdescent : baseEnd_7066529 < baseStart_7066529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066550 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7066550 : Nat := 118140960795 + 7066550 * 2 ^ 59
def prefixEnd_7066550 : Nat := 4983230072969 + 3 ^ 40 * 7066550 * 2
def baseEnd_7066550 : Nat := 3628536719029432324326535

theorem tailTrace_7066550 : CollatzResearch.WordTrace tailWord_7066550 prefixEnd_7066550 3628536719029432324326535 := by
  unfold tailWord_7066550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108640784318980968826819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171825501699402463667486069 16108640784318980968826819)
  ·
    refine ⟨24162961176478471453240229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16108640784318980968826819 24162961176478471453240229)
    ·
      refine ⟨4530555220589713397482543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24162961176478471453240229 4530555220589713397482543)
      ·
        refine ⟨6795832830884570096223815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530555220589713397482543 6795832830884570096223815)
        ·
          refine ⟨10193749246326855144335723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795832830884570096223815 10193749246326855144335723)
          ·
            refine ⟨15290623869490282716503585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10193749246326855144335723 15290623869490282716503585)
            ·
              refine ⟨11467967902117712037377689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15290623869490282716503585 11467967902117712037377689)
              ·
                refine ⟨8600975926588284028033267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11467967902117712037377689 8600975926588284028033267)
                ·
                  refine ⟨12901463889882426042049901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8600975926588284028033267 12901463889882426042049901)
                  ·
                    refine ⟨4838048958705909765768713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12901463889882426042049901 4838048958705909765768713)
                    ·
                      refine ⟨3628536719029432324326535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838048958705909765768713 3628536719029432324326535)
                      ·
                        rfl

theorem cell23_7066550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7066550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066550 prefixEnd_7066550 := by exact prefixLift 7066550
  have htrace : WordTrace (prefixWord ++ tailWord_7066550) baseStart_7066550 baseEnd_7066550 := by
    simpa [prefixWord, tailWord_7066550, baseEnd_7066550] using wordTrace_append hprefix tailTrace_7066550
  have hstable : (prefixWord ++ tailWord_7066550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066550).length < 2 ^ (prefixWord ++ tailWord_7066550).sum := by decide
  have hdescent : baseEnd_7066550 < baseStart_7066550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066582 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7066582 : Nat := 118140960795 + 7066582 * 2 ^ 59
def prefixEnd_7066582 : Nat := 4983230072969 + 3 ^ 40 * 7066582 * 2
def baseEnd_7066582 : Nat := 1209517716803458733042129

theorem tailTrace_7066582 : CollatzResearch.WordTrace tailWord_7066582 prefixEnd_7066582 1209517716803458733042129 := by
  unfold tailWord_7066582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108713730311735310399625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171826279789991843310929333 16108713730311735310399625)
  ·
    refine ⟨12081535297733801482799719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16108713730311735310399625 12081535297733801482799719)
    ·
      refine ⟨18122302946600702224199579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12081535297733801482799719 18122302946600702224199579)
      ·
        refine ⟨27183454419901053336299369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18122302946600702224199579 27183454419901053336299369)
        ·
          refine ⟨20387590814925790002224527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27183454419901053336299369 20387590814925790002224527)
          ·
            refine ⟨30581386222388685003336791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20387590814925790002224527 30581386222388685003336791)
            ·
              refine ⟨45872079333583027505005187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30581386222388685003336791 45872079333583027505005187)
              ·
                refine ⟨68808119000374541257507781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45872079333583027505005187 68808119000374541257507781)
                ·
                  refine ⟨12901522312570226485782709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68808119000374541257507781 12901522312570226485782709)
                  ·
                    refine ⟨1209517716803458733042129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12901522312570226485782709 1209517716803458733042129)
                    ·
                      rfl

theorem cell23_7066582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7066582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066582 prefixEnd_7066582 := by exact prefixLift 7066582
  have htrace : WordTrace (prefixWord ++ tailWord_7066582) baseStart_7066582 baseEnd_7066582 := by
    simpa [prefixWord, tailWord_7066582, baseEnd_7066582] using wordTrace_append hprefix tailTrace_7066582
  have hstable : (prefixWord ++ tailWord_7066582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066582).length < 2 ^ (prefixWord ++ tailWord_7066582).sum := by decide
  have hdescent : baseEnd_7066582 < baseStart_7066582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066585 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_7066585 : Nat := 118140960795 + 7066585 * 2 ^ 59
def prefixEnd_7066585 : Nat := 4983230072969 + 3 ^ 40 * 7066585 * 2
def baseEnd_7066585 : Nat := 3628554690852339687388873

theorem tailTrace_7066585 : CollatzResearch.WordTrace tailWord_7066585 prefixEnd_7066585 3628554690852339687388873 := by
  unfold tailWord_7066585
  simp only [CollatzResearch.WordTrace]
  refine ⟨257739529103976896478753209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171826352735984597652502139 257739529103976896478753209)
  ·
    refine ⟨193304646827982672359064907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257739529103976896478753209 193304646827982672359064907)
    ·
      refine ⟨289956970241974008538597361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193304646827982672359064907 289956970241974008538597361)
      ·
        refine ⟨217467727681480506403948021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289956970241974008538597361 217467727681480506403948021)
        ·
          refine ⟨20387599470138797475370127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217467727681480506403948021 20387599470138797475370127)
          ·
            refine ⟨30581399205208196213055191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20387599470138797475370127 30581399205208196213055191)
            ·
              refine ⟨45872098807812294319582787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30581399205208196213055191 45872098807812294319582787)
              ·
                refine ⟨68808148211718441479374181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45872098807812294319582787 68808148211718441479374181)
                ·
                  refine ⟨12901527789697207777382659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68808148211718441479374181 12901527789697207777382659)
                  ·
                    refine ⟨19352291684545811666073989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12901527789697207777382659 19352291684545811666073989)
                    ·
                      refine ⟨3628554690852339687388873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19352291684545811666073989 3628554690852339687388873)
                      ·
                        rfl

theorem cell23_7066585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_7066585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066585 prefixEnd_7066585 := by exact prefixLift 7066585
  have htrace : WordTrace (prefixWord ++ tailWord_7066585) baseStart_7066585 baseEnd_7066585 := by
    simpa [prefixWord, tailWord_7066585, baseEnd_7066585] using wordTrace_append hprefix tailTrace_7066585
  have hstable : (prefixWord ++ tailWord_7066585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066585).length < 2 ^ (prefixWord ++ tailWord_7066585).sum := by decide
  have hdescent : baseEnd_7066585 < baseStart_7066585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066655 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 3, 5]
def baseStart_7066655 : Nat := 118140960795 + 7066655 * 2 ^ 59
def prefixEnd_7066655 : Nat := 4983230072969 + 3 ^ 40 * 7066655 * 2
def baseEnd_7066655 : Nat := 1209530211499384804504517

theorem tailTrace_7066655 : CollatzResearch.WordTrace tailWord_7066655 prefixEnd_7066655 1209530211499384804504517 := by
  unfold tailWord_7066655
  simp only [CollatzResearch.WordTrace]
  refine ⟨257742082213723298433801419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171828054809148865622534279 257742082213723298433801419)
  ·
    refine ⟨386613123320584947650702129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257742082213723298433801419 386613123320584947650702129)
    ·
      refine ⟨289959842490438710738026597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386613123320584947650702129 289959842490438710738026597)
      ·
        refine ⟨54367470466957258263379987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289959842490438710738026597 54367470466957258263379987)
        ·
          refine ⟨81551205700435887395069981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54367470466957258263379987 81551205700435887395069981)
          ·
            refine ⟨30581702137663457773151243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81551205700435887395069981 30581702137663457773151243)
            ·
              refine ⟨45872553206495186659726865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30581702137663457773151243 45872553206495186659726865)
              ·
                refine ⟨34404414904871389994795149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45872553206495186659726865 34404414904871389994795149)
                ·
                  refine ⟨12901655589326771248048181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34404414904871389994795149 12901655589326771248048181)
                  ·
                    refine ⟨1209530211499384804504517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12901655589326771248048181 1209530211499384804504517)
                    ·
                      rfl

theorem cell23_7066655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_7066655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066655 prefixEnd_7066655 := by exact prefixLift 7066655
  have htrace : WordTrace (prefixWord ++ tailWord_7066655) baseStart_7066655 baseEnd_7066655 := by
    simpa [prefixWord, tailWord_7066655, baseEnd_7066655] using wordTrace_append hprefix tailTrace_7066655
  have hstable : (prefixWord ++ tailWord_7066655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066655).length < 2 ^ (prefixWord ++ tailWord_7066655).sum := by decide
  have hdescent : baseEnd_7066655 < baseStart_7066655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066689 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7066689 : Nat := 118140960795 + 7066689 * 2 ^ 59
def prefixEnd_7066689 : Nat := 4983230072969 + 3 ^ 40 * 7066689 * 2
def baseEnd_7066689 : Nat := 1209536030946802426829465

theorem tailTrace_7066689 : CollatzResearch.WordTrace tailWord_7066689 prefixEnd_7066689 1209536030946802426829465 := by
  unfold tailWord_7066689
  simp only [CollatzResearch.WordTrace]
  refine ⟨257743322295600122240539121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171828881530400081493692747 257743322295600122240539121)
  ·
    refine ⟨193307491721700091680404341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257743322295600122240539121 193307491721700091680404341)
    ·
      refine ⟨18122577348909383595037907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193307491721700091680404341 18122577348909383595037907)
      ·
        refine ⟨27183866023364075392556861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18122577348909383595037907 27183866023364075392556861)
        ·
          refine ⟨10193949758761528272208823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27183866023364075392556861 10193949758761528272208823)
          ·
            refine ⟨15290924638142292408313235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10193949758761528272208823 15290924638142292408313235)
            ·
              refine ⟨22936386957213438612469853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15290924638142292408313235 22936386957213438612469853)
              ·
                refine ⟨8601145108955039479676195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22936386957213438612469853 8601145108955039479676195)
                ·
                  refine ⟨12901717663432559219514293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601145108955039479676195 12901717663432559219514293)
                  ·
                    refine ⟨1209536030946802426829465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12901717663432559219514293 1209536030946802426829465)
                    ·
                      rfl

theorem cell23_7066689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7066689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066689 prefixEnd_7066689 := by exact prefixLift 7066689
  have htrace : WordTrace (prefixWord ++ tailWord_7066689) baseStart_7066689 baseEnd_7066689 := by
    simpa [prefixWord, tailWord_7066689, baseEnd_7066689] using wordTrace_append hprefix tailTrace_7066689
  have hstable : (prefixWord ++ tailWord_7066689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066689).length < 2 ^ (prefixWord ++ tailWord_7066689).sum := by decide
  have hdescent : baseEnd_7066689 < baseStart_7066689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066702 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_7066702 : Nat := 118140960795 + 7066702 * 2 ^ 59
def prefixEnd_7066702 : Nat := 4983230072969 + 3 ^ 40 * 7066702 * 2
def baseEnd_7066702 : Nat := 1209538256029638576541945

theorem tailTrace_7066702 : CollatzResearch.WordTrace tailWord_7066702 prefixEnd_7066702 1209538256029638576541945 := by
  unfold tailWord_7066702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32217974555569128182595295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171829197629702016973841573 32217974555569128182595295)
  ·
    refine ⟨48326961833353692273892943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32217974555569128182595295 48326961833353692273892943)
    ·
      refine ⟨72490442750030538410839415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48326961833353692273892943 72490442750030538410839415)
      ·
        refine ⟨108735664125045807616259123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72490442750030538410839415 108735664125045807616259123)
        ·
          refine ⟨163103496187568711424388685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108735664125045807616259123 163103496187568711424388685)
          ·
            refine ⟨61163811070338266784145757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163103496187568711424388685 61163811070338266784145757)
            ·
              refine ⟨22936429151376850044054659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61163811070338266784145757 22936429151376850044054659)
              ·
                refine ⟨34404643727065275066081989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22936429151376850044054659 34404643727065275066081989)
                ·
                  refine ⟨6450870698824739074890373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34404643727065275066081989 6450870698824739074890373)
                  ·
                    refine ⟨1209538256029638576541945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6450870698824739074890373 1209538256029638576541945)
                    ·
                      rfl

theorem cell23_7066702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_7066702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066702 prefixEnd_7066702 := by exact prefixLift 7066702
  have htrace : WordTrace (prefixWord ++ tailWord_7066702) baseStart_7066702 baseEnd_7066702 := by
    simpa [prefixWord, tailWord_7066702, baseEnd_7066702] using wordTrace_append hprefix tailTrace_7066702
  have hstable : (prefixWord ++ tailWord_7066702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066702).length < 2 ^ (prefixWord ++ tailWord_7066702).sum := by decide
  have hdescent : baseEnd_7066702 < baseStart_7066702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066705 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_7066705 : Nat := 118140960795 + 7066705 * 2 ^ 59
def prefixEnd_7066705 : Nat := 4983230072969 + 3 ^ 40 * 7066705 * 2
def baseEnd_7066705 : Nat := 3628616308530879217888321

theorem tailTrace_7066705 : CollatzResearch.WordTrace tailWord_7066705 prefixEnd_7066705 3628616308530879217888321 := by
  unfold tailWord_7066705
  simp only [CollatzResearch.WordTrace]
  refine ⟨257743905863542156973121569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171829270575694771315414379 257743905863542156973121569)
  ·
    refine ⟨193307929397656617729841177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257743905863542156973121569 193307929397656617729841177)
    ·
      refine ⟨144980947048242463297380883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193307929397656617729841177 144980947048242463297380883)
      ·
        refine ⟨217471420572363694946071325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144980947048242463297380883 217471420572363694946071325)
        ·
          refine ⟨81551782714636385604776747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217471420572363694946071325 81551782714636385604776747)
          ·
            refine ⟨122327674071954578407165121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81551782714636385604776747 122327674071954578407165121)
            ·
              refine ⟨91745755553965933805373841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122327674071954578407165121 91745755553965933805373841)
              ·
                refine ⟨68809316665474450354030381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91745755553965933805373841 68809316665474450354030381)
                ·
                  refine ⟨25803493749552918882761393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68809316665474450354030381 25803493749552918882761393)
                  ·
                    refine ⟨19352620312164689162071045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25803493749552918882761393 19352620312164689162071045)
                    ·
                      refine ⟨3628616308530879217888321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19352620312164689162071045 3628616308530879217888321)
                      ·
                        rfl

theorem cell23_7066705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_7066705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066705 prefixEnd_7066705 := by exact prefixLift 7066705
  have htrace : WordTrace (prefixWord ++ tailWord_7066705) baseStart_7066705 baseEnd_7066705 := by
    simpa [prefixWord, tailWord_7066705, baseEnd_7066705] using wordTrace_append hprefix tailTrace_7066705
  have hstable : (prefixWord ++ tailWord_7066705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066705).length < 2 ^ (prefixWord ++ tailWord_7066705).sum := by decide
  have hdescent : baseEnd_7066705 < baseStart_7066705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066719 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 2, 4]
def baseStart_7066719 : Nat := 118140960795 + 7066719 * 2 ^ 59
def prefixEnd_7066719 : Nat := 4983230072969 + 3 ^ 40 * 7066719 * 2
def baseEnd_7066719 : Nat := 1209541165753347387704419

theorem tailTrace_7066719 : CollatzResearch.WordTrace tailWord_7066719 prefixEnd_7066719 1209541165753347387704419 := by
  unfold tailWord_7066719
  simp only [CollatzResearch.WordTrace]
  refine ⟨257744416485491437364131211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171829610990327624909420807 257744416485491437364131211)
  ·
    refine ⟨386616624728237156046196817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257744416485491437364131211 386616624728237156046196817)
    ·
      refine ⟨289962468546177867034647613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386616624728237156046196817 289962468546177867034647613)
      ·
        refine ⟨108735925704816700137992855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289962468546177867034647613 108735925704816700137992855)
        ·
          refine ⟨163103888557225050206989283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108735925704816700137992855 163103888557225050206989283)
          ·
            refine ⟨244655832835837575310483925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163103888557225050206989283 244655832835837575310483925)
            ·
              refine ⟨5734121082089943171339467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 244655832835837575310483925 5734121082089943171339467)
              ·
                refine ⟨8601181623134914757009201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734121082089943171339467 8601181623134914757009201)
                ·
                  refine ⟨6450886217351186067756901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601181623134914757009201 6450886217351186067756901)
                  ·
                    refine ⟨1209541165753347387704419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6450886217351186067756901 1209541165753347387704419)
                    ·
                      rfl

theorem cell23_7066719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 4].length) (baseStart_7066719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066719 prefixEnd_7066719 := by exact prefixLift 7066719
  have htrace : WordTrace (prefixWord ++ tailWord_7066719) baseStart_7066719 baseEnd_7066719 := by
    simpa [prefixWord, tailWord_7066719, baseEnd_7066719] using wordTrace_append hprefix tailTrace_7066719
  have hstable : (prefixWord ++ tailWord_7066719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066719).length < 2 ^ (prefixWord ++ tailWord_7066719).sum := by decide
  have hdescent : baseEnd_7066719 < baseStart_7066719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066729 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 3]
def baseStart_7066729 : Nat := 118140960795 + 7066729 * 2 ^ 59
def prefixEnd_7066729 : Nat := 4983230072969 + 3 ^ 40 * 7066729 * 2
def baseEnd_7066729 : Nat := 3628628632066587123988211

theorem tailTrace_7066729 : CollatzResearch.WordTrace tailWord_7066729 prefixEnd_7066729 3628628632066587123988211 := by
  unfold tailWord_7066729
  simp only [CollatzResearch.WordTrace]
  refine ⟨257744781215455209071995241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171829854143636806047996827 257744781215455209071995241)
  ·
    refine ⟨193308585911591406803996431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257744781215455209071995241 193308585911591406803996431)
    ·
      refine ⟨289962878867387110205994647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193308585911591406803996431 289962878867387110205994647)
      ·
        refine ⟨434944318301080665308991971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289962878867387110205994647 434944318301080665308991971)
        ·
          refine ⟨652416477451620997963487957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434944318301080665308991971 652416477451620997963487957)
          ·
            refine ⟨15291011190272367139769249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 652416477451620997963487957 15291011190272367139769249)
            ·
              refine ⟨11468258392704275354826937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15291011190272367139769249 11468258392704275354826937)
              ·
                refine ⟨8601193794528206516120203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11468258392704275354826937 8601193794528206516120203)
                ·
                  refine ⟨12901790691792309774180305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601193794528206516120203 12901790691792309774180305)
                  ·
                    refine ⟨9676343018844232330635229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12901790691792309774180305 9676343018844232330635229)
                    ·
                      refine ⟨3628628632066587123988211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676343018844232330635229 3628628632066587123988211)
                      ·
                        rfl

theorem cell23_7066729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_7066729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066729 prefixEnd_7066729 := by exact prefixLift 7066729
  have htrace : WordTrace (prefixWord ++ tailWord_7066729) baseStart_7066729 baseEnd_7066729 := by
    simpa [prefixWord, tailWord_7066729, baseEnd_7066729] using wordTrace_append hprefix tailTrace_7066729
  have hstable : (prefixWord ++ tailWord_7066729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066729).length < 2 ^ (prefixWord ++ tailWord_7066729).sum := by decide
  have hdescent : baseEnd_7066729 < baseStart_7066729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066755 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_7066755 : Nat := 118140960795 + 7066755 * 2 ^ 59
def prefixEnd_7066755 : Nat := 4983230072969 + 3 ^ 40 * 7066755 * 2
def baseEnd_7066755 : Nat := 3628641982563604022263091

theorem tailTrace_7066755 : CollatzResearch.WordTrace tailWord_7066755 prefixEnd_7066755 3628641982563604022263091 := by
  unfold tailWord_7066755
  simp only [CollatzResearch.WordTrace]
  refine ⟨257745729513361015512441719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171830486342240677008294479 257745729513361015512441719)
  ·
    refine ⟨386618594270041523268662579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257745729513361015512441719 386618594270041523268662579)
    ·
      refine ⟨579927891405062284902993869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386618594270041523268662579 579927891405062284902993869)
      ·
        refine ⟨217472959276898356838622701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579927891405062284902993869 217472959276898356838622701)
        ·
          refine ⟨81552359728836883814483513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217472959276898356838622701 81552359728836883814483513)
          ·
            refine ⟨61164269796627662860862635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81552359728836883814483513 61164269796627662860862635)
            ·
              refine ⟨91746404694941494291293953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61164269796627662860862635 91746404694941494291293953)
              ·
                refine ⟨68809803521206120718470465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91746404694941494291293953 68809803521206120718470465)
                ·
                  refine ⟨51607352640904590538852849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68809803521206120718470465 51607352640904590538852849)
                  ·
                    refine ⟨38705514480678442904139637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51607352640904590538852849 38705514480678442904139637)
                    ·
                      refine ⟨3628641982563604022263091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38705514480678442904139637 3628641982563604022263091)
                      ·
                        rfl

theorem cell23_7066755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_7066755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066755 prefixEnd_7066755 := by exact prefixLift 7066755
  have htrace : WordTrace (prefixWord ++ tailWord_7066755) baseStart_7066755 baseEnd_7066755 := by
    simpa [prefixWord, tailWord_7066755, baseEnd_7066755] using wordTrace_append hprefix tailTrace_7066755
  have hstable : (prefixWord ++ tailWord_7066755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066755).length < 2 ^ (prefixWord ++ tailWord_7066755).sum := by decide
  have hdescent : baseEnd_7066755 < baseStart_7066755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066759 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_7066759 : Nat := 118140960795 + 7066759 * 2 ^ 59
def prefixEnd_7066759 : Nat := 4983230072969 + 3 ^ 40 * 7066759 * 2
def baseEnd_7066759 : Nat := 3628644036486222006613073

theorem tailTrace_7066759 : CollatzResearch.WordTrace tailWord_7066759 prefixEnd_7066759 3628644036486222006613073 := by
  unfold tailWord_7066759
  simp only [CollatzResearch.WordTrace]
  refine ⟨257745875405346524195587331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171830583603564349463724887 257745875405346524195587331)
  ·
    refine ⟨386618813108019786293380997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257745875405346524195587331 386618813108019786293380997)
    ·
      refine ⟨72491027457753709930008937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386618813108019786293380997 72491027457753709930008937)
      ·
        refine ⟨54368270593315282447506703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72491027457753709930008937 54368270593315282447506703)
        ·
          refine ⟨81552405889972923671260055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54368270593315282447506703 81552405889972923671260055)
          ·
            refine ⟨122328608834959385506890083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81552405889972923671260055 122328608834959385506890083)
            ·
              refine ⟨183492913252439078260335125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122328608834959385506890083 183492913252439078260335125)
              ·
                refine ⟨8601230308708081793453209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183492913252439078260335125 8601230308708081793453209)
                ·
                  refine ⟨6450922731531061345089907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601230308708081793453209 6450922731531061345089907)
                  ·
                    refine ⟨9676384097296592017634861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6450922731531061345089907 9676384097296592017634861)
                    ·
                      refine ⟨3628644036486222006613073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676384097296592017634861 3628644036486222006613073)
                      ·
                        rfl

theorem cell23_7066759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_7066759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066759 prefixEnd_7066759 := by exact prefixLift 7066759
  have htrace : WordTrace (prefixWord ++ tailWord_7066759) baseStart_7066759 baseEnd_7066759 := by
    simpa [prefixWord, tailWord_7066759, baseEnd_7066759] using wordTrace_append hprefix tailTrace_7066759
  have hstable : (prefixWord ++ tailWord_7066759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066759).length < 2 ^ (prefixWord ++ tailWord_7066759).sum := by decide
  have hdescent : baseEnd_7066759 < baseStart_7066759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066760 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7066760 : Nat := 118140960795 + 7066760 * 2 ^ 59
def prefixEnd_7066760 : Nat := 4983230072969 + 3 ^ 40 * 7066760 * 2
def baseEnd_7066760 : Nat := 3628644549966876502700569

theorem tailTrace_7066760 : CollatzResearch.WordTrace tailWord_7066760 prefixEnd_7066760 3628644549966876502700569 := by
  unfold tailWord_7066760
  simp only [CollatzResearch.WordTrace]
  refine ⟨128872955939171450683186867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171830607918895267577582489 128872955939171450683186867)
  ·
    refine ⟨193309433908757176024780301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128872955939171450683186867 193309433908757176024780301)
    ·
      refine ⟨72491037715783941009292613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193309433908757176024780301 72491037715783941009292613)
      ·
        refine ⟨13592069571709488939242365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72491037715783941009292613 13592069571709488939242365)
        ·
          refine ⟨5097026089391058352215887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13592069571709488939242365 5097026089391058352215887)
          ·
            refine ⟨7645539134086587528323831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097026089391058352215887 7645539134086587528323831)
            ·
              refine ⟨11468308701129881292485747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645539134086587528323831 11468308701129881292485747)
              ·
                refine ⟨17202463051694821938728621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11468308701129881292485747 17202463051694821938728621)
                ·
                  refine ⟨6450923644385558227023233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17202463051694821938728621 6450923644385558227023233)
                  ·
                    refine ⟨4838192733289168670267425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450923644385558227023233 4838192733289168670267425)
                    ·
                      refine ⟨3628644549966876502700569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838192733289168670267425 3628644549966876502700569)
                      ·
                        rfl

theorem cell23_7066760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7066760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066760 prefixEnd_7066760 := by exact prefixLift 7066760
  have htrace : WordTrace (prefixWord ++ tailWord_7066760) baseStart_7066760 baseEnd_7066760 := by
    simpa [prefixWord, tailWord_7066760, baseEnd_7066760] using wordTrace_append hprefix tailTrace_7066760
  have hstable : (prefixWord ++ tailWord_7066760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066760).length < 2 ^ (prefixWord ++ tailWord_7066760).sum := by decide
  have hdescent : baseEnd_7066760 < baseStart_7066760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066776 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7066776 : Nat := 118140960795 + 7066776 * 2 ^ 59
def prefixEnd_7066776 : Nat := 4983230072969 + 3 ^ 40 * 7066776 * 2
def baseEnd_7066776 : Nat := 3628652765657348440100495

theorem tailTrace_7066776 : CollatzResearch.WordTrace tailWord_7066776 prefixEnd_7066776 3628652765657348440100495 := by
  unfold tailWord_7066776
  simp only [CollatzResearch.WordTrace]
  refine ⟨128873247723142468049478091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171830996964189957399304121 128873247723142468049478091)
  ·
    refine ⟨193309871584713702074217137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128873247723142468049478091 193309871584713702074217137)
    ·
      refine ⟨144982403688535276555662853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193309871584713702074217137 144982403688535276555662853)
      ·
        refine ⟨27184200691600364354186785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144982403688535276555662853 27184200691600364354186785)
        ·
          refine ⟨20388150518700273265640089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27184200691600364354186785 20388150518700273265640089)
          ·
            refine ⟨15291112889025204949230067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20388150518700273265640089 15291112889025204949230067)
            ·
              refine ⟨22936669333537807423845101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15291112889025204949230067 22936669333537807423845101)
              ·
                refine ⟨8601251000076677783941913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22936669333537807423845101 8601251000076677783941913)
                ·
                  refine ⟨6450938250057508337956435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601251000076677783941913 6450938250057508337956435)
                  ·
                    refine ⟨9676407375086262506934653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6450938250057508337956435 9676407375086262506934653)
                    ·
                      refine ⟨3628652765657348440100495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676407375086262506934653 3628652765657348440100495)
                      ·
                        rfl

theorem cell23_7066776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7066776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066776 prefixEnd_7066776 := by exact prefixLift 7066776
  have htrace : WordTrace (prefixWord ++ tailWord_7066776) baseStart_7066776 baseEnd_7066776 := by
    simpa [prefixWord, tailWord_7066776, baseEnd_7066776] using wordTrace_append hprefix tailTrace_7066776
  have hstable : (prefixWord ++ tailWord_7066776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066776).length < 2 ^ (prefixWord ++ tailWord_7066776).sum := by decide
  have hdescent : baseEnd_7066776 < baseStart_7066776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066799 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 6, 2, 2]
def baseStart_7066799 : Nat := 118140960795 + 7066799 * 2 ^ 59
def prefixEnd_7066799 : Nat := 4983230072969 + 3 ^ 40 * 7066799 * 2
def baseEnd_7066799 : Nat := 3628664575712401850112889

theorem tailTrace_7066799 : CollatzResearch.WordTrace tailWord_7066799 prefixEnd_7066799 3628664575712401850112889 := by
  unfold tailWord_7066799
  simp only [CollatzResearch.WordTrace]
  refine ⟨257747334325201611027043451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171831556216801074018028967 257747334325201611027043451)
  ·
    refine ⟨386621001487802416540565177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257747334325201611027043451 386621001487802416540565177)
    ·
      refine ⟨289965751115851812405423883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386621001487802416540565177 289965751115851812405423883)
      ·
        refine ⟨434948626673777718608135825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289965751115851812405423883 434948626673777718608135825)
        ·
          refine ⟨326211470005333288956101869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434948626673777718608135825 326211470005333288956101869)
          ·
            refine ⟨122329301251999983358538201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326211470005333288956101869 122329301251999983358538201)
            ·
              refine ⟨91746975938999987518903651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122329301251999983358538201 91746975938999987518903651)
              ·
                refine ⟨137620463908499981278355477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91746975938999987518903651 137620463908499981278355477)
                ·
                  refine ⟨6450959245710936622422913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137620463908499981278355477 6450959245710936622422913)
                  ·
                    refine ⟨4838219434283202466817185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450959245710936622422913 4838219434283202466817185)
                    ·
                      refine ⟨3628664575712401850112889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838219434283202466817185 3628664575712401850112889)
                      ·
                        rfl

theorem cell23_7066799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 2, 2].length) (baseStart_7066799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066799 prefixEnd_7066799 := by exact prefixLift 7066799
  have htrace : WordTrace (prefixWord ++ tailWord_7066799) baseStart_7066799 baseEnd_7066799 := by
    simpa [prefixWord, tailWord_7066799, baseEnd_7066799] using wordTrace_append hprefix tailTrace_7066799
  have hstable : (prefixWord ++ tailWord_7066799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066799).length < 2 ^ (prefixWord ++ tailWord_7066799).sum := by decide
  have hdescent : baseEnd_7066799 < baseStart_7066799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066802 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_7066802 : Nat := 118140960795 + 7066802 * 2 ^ 59
def prefixEnd_7066802 : Nat := 4983230072969 + 3 ^ 40 * 7066802 * 2
def baseEnd_7066802 : Nat := 3628666116154365338375375

theorem tailTrace_7066802 : CollatzResearch.WordTrace tailWord_7066802 prefixEnd_7066802 3628666116154365338375375 := by
  unfold tailWord_7066802
  simp only [CollatzResearch.WordTrace]
  refine ⟨64436860936047685634850665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171831629162793828359601773 64436860936047685634850665)
  ·
    refine ⟨48327645702035764226137999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64436860936047685634850665 48327645702035764226137999)
    ·
      refine ⟨72491468553053646339206999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48327645702035764226137999 72491468553053646339206999)
      ·
        refine ⟨108737202829580469508810499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72491468553053646339206999 108737202829580469508810499)
        ·
          refine ⟨163105804244370704263215749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108737202829580469508810499 163105804244370704263215749)
          ·
            refine ⟨30582338295819507049352953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163105804244370704263215749 30582338295819507049352953)
            ·
              refine ⟨22936753721864630287014715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30582338295819507049352953 22936753721864630287014715)
              ·
                refine ⟨34405130582796945430522073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22936753721864630287014715 34405130582796945430522073)
                ·
                  refine ⟨25803847937097709072891555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34405130582796945430522073 25803847937097709072891555)
                  ·
                    refine ⟨38705771905646563609337333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25803847937097709072891555 38705771905646563609337333)
                    ·
                      refine ⟨3628666116154365338375375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38705771905646563609337333 3628666116154365338375375)
                      ·
                        rfl

theorem cell23_7066802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_7066802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066802 prefixEnd_7066802 := by exact prefixLift 7066802
  have htrace : WordTrace (prefixWord ++ tailWord_7066802) baseStart_7066802 baseEnd_7066802 := by
    simpa [prefixWord, tailWord_7066802, baseEnd_7066802] using wordTrace_append hprefix tailTrace_7066802
  have hstable : (prefixWord ++ tailWord_7066802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066802).length < 2 ^ (prefixWord ++ tailWord_7066802).sum := by decide
  have hdescent : baseEnd_7066802 < baseStart_7066802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066815 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_7066815 : Nat := 118140960795 + 7066815 * 2 ^ 59
def prefixEnd_7066815 : Nat := 4983230072969 + 3 ^ 40 * 7066815 * 2
def baseEnd_7066815 : Nat := 3628672791402873787512815

theorem tailTrace_7066815 : CollatzResearch.WordTrace tailWord_7066815 prefixEnd_7066815 3628672791402873787512815 := by
  unfold tailWord_7066815
  simp only [CollatzResearch.WordTrace]
  refine ⟨257747917893143645759625899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171831945262095763839750599 257747917893143645759625899)
  ·
    refine ⟨386621876839715468639438849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257747917893143645759625899 386621876839715468639438849)
    ·
      refine ⟨289966407629786601479579137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386621876839715468639438849 289966407629786601479579137)
      ·
        refine ⟨217474805722339951109684353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289966407629786601479579137 217474805722339951109684353)
        ·
          refine ⟨163106104291754963332263265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217474805722339951109684353 163106104291754963332263265)
          ·
            refine ⟨122329578218816222499197449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163106104291754963332263265 122329578218816222499197449)
            ·
              refine ⟨91747183664112166874398087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122329578218816222499197449 91747183664112166874398087)
              ·
                refine ⟨137620775496168250311597131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91747183664112166874398087 137620775496168250311597131)
                ·
                  refine ⟨206431163244252375467395697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137620775496168250311597131 206431163244252375467395697)
                  ·
                    refine ⟨154823372433189281600546773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206431163244252375467395697 154823372433189281600546773)
                    ·
                      refine ⟨3628672791402873787512815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154823372433189281600546773 3628672791402873787512815)
                      ·
                        rfl

theorem cell23_7066815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_7066815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066815 prefixEnd_7066815 := by exact prefixLift 7066815
  have htrace : WordTrace (prefixWord ++ tailWord_7066815) baseStart_7066815 baseEnd_7066815 := by
    simpa [prefixWord, tailWord_7066815, baseEnd_7066815] using wordTrace_append hprefix tailTrace_7066815
  have hstable : (prefixWord ++ tailWord_7066815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066815).length < 2 ^ (prefixWord ++ tailWord_7066815).sum := by decide
  have hdescent : baseEnd_7066815 < baseStart_7066815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066835 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 3, 7]
def baseStart_7066835 : Nat := 118140960795 + 7066835 * 2 ^ 59
def prefixEnd_7066835 : Nat := 4983230072969 + 3 ^ 40 * 7066835 * 2
def baseEnd_7066835 : Nat := 1209561020338654569754241

theorem tailTrace_7066835 : CollatzResearch.WordTrace tailWord_7066835 prefixEnd_7066835 1209561020338654569754241 := by
  unfold tailWord_7066835
  simp only [CollatzResearch.WordTrace]
  refine ⟨257748647353071189175353959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171832431568714126116902639 257748647353071189175353959)
  ·
    refine ⟨386622971029606783763030939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257748647353071189175353959 386622971029606783763030939)
    ·
      refine ⟨579934456544410175644546409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386622971029606783763030939 579934456544410175644546409)
      ·
        refine ⟨434950842408307631733409807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579934456544410175644546409 434950842408307631733409807)
        ·
          refine ⟨652426263612461447600114711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434950842408307631733409807 652426263612461447600114711)
          ·
            refine ⟨978639395418692171400172067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652426263612461447600114711 978639395418692171400172067)
            ·
              refine ⟨1467959093128038257100258101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978639395418692171400172067 1467959093128038257100258101)
              ·
                refine ⟨137621164980753586603149197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467959093128038257100258101 137621164980753586603149197)
                ·
                  refine ⟨51607936867782594976180949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137621164980753586603149197 51607936867782594976180949)
                  ·
                    refine ⟨1209561020338654569754241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51607936867782594976180949 1209561020338654569754241)
                    ·
                      rfl

theorem cell23_7066835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_7066835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066835 prefixEnd_7066835 := by exact prefixLift 7066835
  have htrace : WordTrace (prefixWord ++ tailWord_7066835) baseStart_7066835 baseEnd_7066835 := by
    simpa [prefixWord, tailWord_7066835, baseEnd_7066835] using wordTrace_append hprefix tailTrace_7066835
  have hstable : (prefixWord ++ tailWord_7066835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066835).length < 2 ^ (prefixWord ++ tailWord_7066835).sum := by decide
  have hdescent : baseEnd_7066835 < baseStart_7066835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066862 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7066862 : Nat := 118140960795 + 7066862 * 2 ^ 59
def prefixEnd_7066862 : Nat := 4983230072969 + 3 ^ 40 * 7066862 * 2
def baseEnd_7066862 : Nat := 3628696924993635103625099

theorem tailTrace_7066862 : CollatzResearch.WordTrace tailWord_7066862 prefixEnd_7066862 3628696924993635103625099 := by
  unfold tailWord_7066862
  simp only [CollatzResearch.WordTrace]
  refine ⟨32218704015496671598323355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171833088082648915191057893 32218704015496671598323355)
  ·
    refine ⟨48328056023245007397485033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32218704015496671598323355 48328056023245007397485033)
    ·
      refine ⟨36246042017433755548113775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48328056023245007397485033 36246042017433755548113775)
      ·
        refine ⟨54369063026150633322170663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36246042017433755548113775 54369063026150633322170663)
        ·
          refine ⟨81553594539225949983255995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54369063026150633322170663 81553594539225949983255995)
          ·
            refine ⟨122330391808838924974883993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81553594539225949983255995 122330391808838924974883993)
            ·
              refine ⟨91747793856629193731162995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122330391808838924974883993 91747793856629193731162995)
              ·
                refine ⟨137621690784943790596744493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91747793856629193731162995 137621690784943790596744493)
                ·
                  refine ⟨51608134044353921473779185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137621690784943790596744493 51608134044353921473779185)
                  ·
                    refine ⟨38706100533265441105334389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51608134044353921473779185 38706100533265441105334389)
                    ·
                      refine ⟨3628696924993635103625099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38706100533265441105334389 3628696924993635103625099)
                      ·
                        rfl

theorem cell23_7066862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7066862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066862 prefixEnd_7066862 := by exact prefixLift 7066862
  have htrace : WordTrace (prefixWord ++ tailWord_7066862) baseStart_7066862 baseEnd_7066862 := by
    simpa [prefixWord, tailWord_7066862, baseEnd_7066862] using wordTrace_append hprefix tailTrace_7066862
  have hstable : (prefixWord ++ tailWord_7066862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066862).length < 2 ^ (prefixWord ++ tailWord_7066862).sum := by decide
  have hdescent : baseEnd_7066862 < baseStart_7066862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066889 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 2, 4, 2]
def baseStart_7066889 : Nat := 118140960795 + 7066889 * 2 ^ 59
def prefixEnd_7066889 : Nat := 4983230072969 + 3 ^ 40 * 7066889 * 2
def baseEnd_7066889 : Nat := 3628710788971306497987475

theorem tailTrace_7066889 : CollatzResearch.WordTrace tailWord_7066889 prefixEnd_7066889 3628710788971306497987475 := by
  unfold tailWord_7066889
  simp only [CollatzResearch.WordTrace]
  refine ⟨257750616894875556397819721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171833744596583704265213147 257750616894875556397819721)
  ·
    refine ⟨193312962671156667298364791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257750616894875556397819721 193312962671156667298364791)
    ·
      refine ⟨289969444006735000947547187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193312962671156667298364791 289969444006735000947547187)
      ·
        refine ⟨434954166010102501421320781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289969444006735000947547187 434954166010102501421320781)
        ·
          refine ⟨163107812253788438032995293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434954166010102501421320781 163107812253788438032995293)
          ·
            refine ⟨61165429595170664262373235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163107812253788438032995293 61165429595170664262373235)
            ·
              refine ⟨91748144392755996393559853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61165429595170664262373235 91748144392755996393559853)
              ·
                refine ⟨34405554147283498647584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91748144392755996393559853 34405554147283498647584945)
                ·
                  refine ⟨25804165610462623985688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34405554147283498647584945 25804165610462623985688709)
                  ·
                    refine ⟨4838281051961741997316633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25804165610462623985688709 4838281051961741997316633)
                    ·
                      refine ⟨3628710788971306497987475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838281051961741997316633 3628710788971306497987475)
                      ·
                        rfl

theorem cell23_7066889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 4, 2].length) (baseStart_7066889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066889 prefixEnd_7066889 := by exact prefixLift 7066889
  have htrace : WordTrace (prefixWord ++ tailWord_7066889) baseStart_7066889 baseEnd_7066889 := by
    simpa [prefixWord, tailWord_7066889, baseEnd_7066889] using wordTrace_append hprefix tailTrace_7066889
  have hstable : (prefixWord ++ tailWord_7066889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066889).length < 2 ^ (prefixWord ++ tailWord_7066889).sum := by decide
  have hdescent : baseEnd_7066889 < baseStart_7066889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066949 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 3, 5, 2]
def baseStart_7066949 : Nat := 118140960795 + 7066949 * 2 ^ 59
def prefixEnd_7066949 : Nat := 4983230072969 + 3 ^ 40 * 7066949 * 2
def baseEnd_7066949 : Nat := 3628741597810576263237199

theorem tailTrace_7066949 : CollatzResearch.WordTrace tailWord_7066949 prefixEnd_7066949 3628741597810576263237199 := by
  unfold tailWord_7066949
  simp only [CollatzResearch.WordTrace]
  refine ⟨257752805274658186645003901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171835203516438791096669267 257752805274658186645003901)
  ·
    refine ⟨96657301977996819991876463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257752805274658186645003901 96657301977996819991876463)
    ·
      refine ⟨144985952966995229987814695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96657301977996819991876463 144985952966995229987814695)
      ·
        refine ⟨217478929450492844981722043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144985952966995229987814695 217478929450492844981722043)
        ·
          refine ⟨326218394175739267472583065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217478929450492844981722043 326218394175739267472583065)
          ·
            refine ⟨244663795631804450604437299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326218394175739267472583065 244663795631804450604437299)
            ·
              refine ⟨366995693447706675906655949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244663795631804450604437299 366995693447706675906655949)
              ·
                refine ⟨137623385042890003464995981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366995693447706675906655949 137623385042890003464995981)
                ·
                  refine ⟨51608769391083751299373493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137623385042890003464995981 51608769391083751299373493)
                  ·
                    refine ⟨4838322130414101684316265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51608769391083751299373493 4838322130414101684316265)
                    ·
                      refine ⟨3628741597810576263237199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838322130414101684316265 3628741597810576263237199)
                      ·
                        rfl

theorem cell23_7066949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_7066949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066949 prefixEnd_7066949 := by exact prefixLift 7066949
  have htrace : WordTrace (prefixWord ++ tailWord_7066949) baseStart_7066949 baseEnd_7066949 := by
    simpa [prefixWord, tailWord_7066949, baseEnd_7066949] using wordTrace_append hprefix tailTrace_7066949
  have hstable : (prefixWord ++ tailWord_7066949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066949).length < 2 ^ (prefixWord ++ tailWord_7066949).sum := by decide
  have hdescent : baseEnd_7066949 < baseStart_7066949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7066999 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_7066999 : Nat := 118140960795 + 7066999 * 2 ^ 59
def prefixEnd_7066999 : Nat := 4983230072969 + 3 ^ 40 * 7066999 * 2
def baseEnd_7066999 : Nat := 3628767271843301067611969

theorem tailTrace_7066999 : CollatzResearch.WordTrace tailWord_7066999 prefixEnd_7066999 3628767271843301067611969 := by
  unfold tailWord_7066999
  simp only [CollatzResearch.WordTrace]
  refine ⟨257754628924477045184324051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171836419282984696789549367 257754628924477045184324051)
  ·
    refine ⟨386631943386715567776486077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257754628924477045184324051 386631943386715567776486077)
    ·
      refine ⟨144986978770018337916182279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386631943386715567776486077 144986978770018337916182279)
      ·
        refine ⟨217480468155027506874273419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144986978770018337916182279 217480468155027506874273419)
        ·
          refine ⟨326220702232541260311410129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217480468155027506874273419 326220702232541260311410129)
          ·
            refine ⟨244665526674405945233557597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326220702232541260311410129 244665526674405945233557597)
            ·
              refine ⟨91749572502902229462584099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244665526674405945233557597 91749572502902229462584099)
              ·
                refine ⟨137624358754353344193876149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91749572502902229462584099 137624358754353344193876149)
                ·
                  refine ⟨12902283633220626018175889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137624358754353344193876149 12902283633220626018175889)
                  ·
                    refine ⟨9676712724915469513631917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12902283633220626018175889 9676712724915469513631917)
                    ·
                      refine ⟨3628767271843301067611969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676712724915469513631917 3628767271843301067611969)
                      ·
                        rfl

theorem cell23_7066999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_7066999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7066999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7066999 prefixEnd_7066999 := by exact prefixLift 7066999
  have htrace : WordTrace (prefixWord ++ tailWord_7066999) baseStart_7066999 baseEnd_7066999 := by
    simpa [prefixWord, tailWord_7066999, baseEnd_7066999] using wordTrace_append hprefix tailTrace_7066999
  have hstable : (prefixWord ++ tailWord_7066999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7066999).length < 2 ^ (prefixWord ++ tailWord_7066999).sum := by decide
  have hdescent : baseEnd_7066999 < baseStart_7066999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7066999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067016 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_7067016 : Nat := 118140960795 + 7067016 * 2 ^ 59
def prefixEnd_7067016 : Nat := 4983230072969 + 3 ^ 40 * 7067016 * 2
def baseEnd_7067016 : Nat := 3628776001014427501099391

theorem tailTrace_7067016 : CollatzResearch.WordTrace tailWord_7067016 prefixEnd_7067016 3628776001014427501099391 := by
  unfold tailWord_7067016
  simp only [CollatzResearch.WordTrace]
  refine ⟨128877624482707728543846451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171836832643610304725128601 128877624482707728543846451)
  ·
    refine ⟨193316436724061592815769677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128877624482707728543846451 193316436724061592815769677)
    ·
      refine ⟨72493663771523097305913629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193316436724061592815769677 72493663771523097305913629)
      ·
        refine ⟨27185123914321161489717611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72493663771523097305913629 27185123914321161489717611)
        ·
          refine ⟨40777685871481742234576417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27185123914321161489717611 40777685871481742234576417)
          ·
            refine ⟨30583264403611306675932313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40777685871481742234576417 30583264403611306675932313)
            ·
              refine ⟨22937448302708480006949235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30583264403611306675932313 22937448302708480006949235)
              ·
                refine ⟨34406172454062720010423853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22937448302708480006949235 34406172454062720010423853)
                ·
                  refine ⟨12902314670273520003908945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34406172454062720010423853 12902314670273520003908945)
                  ·
                    refine ⟨9676736002705140002931709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12902314670273520003908945 9676736002705140002931709)
                    ·
                      refine ⟨3628776001014427501099391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676736002705140002931709 3628776001014427501099391)
                      ·
                        rfl

theorem cell23_7067016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_7067016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067016 prefixEnd_7067016 := by exact prefixLift 7067016
  have htrace : WordTrace (prefixWord ++ tailWord_7067016) baseStart_7067016 baseEnd_7067016 := by
    simpa [prefixWord, tailWord_7067016, baseEnd_7067016] using wordTrace_append hprefix tailTrace_7067016
  have hstable : (prefixWord ++ tailWord_7067016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067016).length < 2 ^ (prefixWord ++ tailWord_7067016).sum := by decide
  have hdescent : baseEnd_7067016 < baseStart_7067016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067019 : List Nat := [1, 1, 1, 1, 4, 3, 5, 7]
def baseStart_7067019 : Nat := 118140960795 + 7067019 * 2 ^ 59
def prefixEnd_7067019 : Nat := 4983230072969 + 3 ^ 40 * 7067019 * 2
def baseEnd_7067019 : Nat := 134399168202088555161551

theorem tailTrace_7067019 : CollatzResearch.WordTrace tailWord_7067019 prefixEnd_7067019 134399168202088555161551 := by
  unfold tailWord_7067019
  simp only [CollatzResearch.WordTrace]
  refine ⟨257755358384404588600052111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171836905589603059066701407 257755358384404588600052111)
  ·
    refine ⟨386633037576606882900078167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257755358384404588600052111 386633037576606882900078167)
    ·
      refine ⟨579949556364910324350117251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386633037576606882900078167 579949556364910324350117251)
      ·
        refine ⟨869924334547365486525175877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579949556364910324350117251 869924334547365486525175877)
        ·
          refine ⟨163110812727631028723470477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 869924334547365486525175877 163110812727631028723470477)
          ·
            refine ⟨61166554772861635771301429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163110812727631028723470477 61166554772861635771301429)
            ·
              refine ⟨5734364509955778353559509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61166554772861635771301429 5734364509955778353559509)
              ·
                refine ⟨134399168202088555161551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5734364509955778353559509 134399168202088555161551)
                ·
                  rfl

theorem cell23_7067019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 7].length) (baseStart_7067019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067019 prefixEnd_7067019 := by exact prefixLift 7067019
  have htrace : WordTrace (prefixWord ++ tailWord_7067019) baseStart_7067019 baseEnd_7067019 := by
    simpa [prefixWord, tailWord_7067019, baseEnd_7067019] using wordTrace_append hprefix tailTrace_7067019
  have hstable : (prefixWord ++ tailWord_7067019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067019).length < 2 ^ (prefixWord ++ tailWord_7067019).sum := by decide
  have hdescent : baseEnd_7067019 < baseStart_7067019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067033 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 1, 2, 3]
def baseStart_7067033 : Nat := 118140960795 + 7067033 * 2 ^ 59
def prefixEnd_7067033 : Nat := 4983230072969 + 3 ^ 40 * 7067033 * 2
def baseEnd_7067033 : Nat := 3628784730185553934586813

theorem tailTrace_7067033 : CollatzResearch.WordTrace tailWord_7067033 prefixEnd_7067033 3628784730185553934586813 := by
  unfold tailWord_7067033
  simp only [CollatzResearch.WordTrace]
  refine ⟨257755869006353868991061753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171837246004235912660707835 257755869006353868991061753)
  ·
    refine ⟨193316901754765401743296315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257755869006353868991061753 193316901754765401743296315)
    ·
      refine ⟨289975352632148102614944473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193316901754765401743296315 289975352632148102614944473)
      ·
        refine ⟨217481514474111076961208355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289975352632148102614944473 217481514474111076961208355)
        ·
          refine ⟨326222271711166615441812533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217481514474111076961208355 326222271711166615441812533)
          ·
            refine ⟨30583337972921870197669925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326222271711166615441812533 30583337972921870197669925)
            ·
              refine ⟨5734375869922850662063111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30583337972921870197669925 5734375869922850662063111)
              ·
                refine ⟨8601563804884275993094667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734375869922850662063111 8601563804884275993094667)
                ·
                  refine ⟨12902345707326413989642001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601563804884275993094667 12902345707326413989642001)
                  ·
                    refine ⟨9676759280494810492231501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12902345707326413989642001 9676759280494810492231501)
                    ·
                      refine ⟨3628784730185553934586813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676759280494810492231501 3628784730185553934586813)
                      ·
                        rfl

theorem cell23_7067033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_7067033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067033 prefixEnd_7067033 := by exact prefixLift 7067033
  have htrace : WordTrace (prefixWord ++ tailWord_7067033) baseStart_7067033 baseEnd_7067033 := by
    simpa [prefixWord, tailWord_7067033, baseEnd_7067033] using wordTrace_append hprefix tailTrace_7067033
  have hstable : (prefixWord ++ tailWord_7067033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067033).length < 2 ^ (prefixWord ++ tailWord_7067033).sum := by decide
  have hdescent : baseEnd_7067033 < baseStart_7067033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067036 : List Nat := [2, 2, 3, 4, 1, 1, 10]
def baseStart_7067036 : Nat := 118140960795 + 7067036 * 2 ^ 59
def prefixEnd_7067036 : Nat := 4983230072969 + 3 ^ 40 * 7067036 * 2
def baseEnd_7067036 : Nat := 44799830501574289170979

theorem tailTrace_7067036 : CollatzResearch.WordTrace tailWord_7067036 prefixEnd_7067036 44799830501574289170979 := by
  unfold tailWord_7067036
  simp only [CollatzResearch.WordTrace]
  refine ⟨128877989212671500251710481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171837318950228667002280641 128877989212671500251710481)
  ·
    refine ⟨96658491909503625188782861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128877989212671500251710481 96658491909503625188782861)
    ·
      refine ⟨36246934466063859445793573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96658491909503625188782861 36246934466063859445793573)
      ·
        refine ⟨6796300212386973646086295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36246934466063859445793573 6796300212386973646086295)
        ·
          refine ⟨10194450318580460469129443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796300212386973646086295 10194450318580460469129443)
          ·
            refine ⟨15291675477870690703694165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194450318580460469129443 15291675477870690703694165)
            ·
              refine ⟨44799830501574289170979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15291675477870690703694165 44799830501574289170979)
              ·
                rfl

theorem cell23_7067036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 10].length) (baseStart_7067036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067036 prefixEnd_7067036 := by exact prefixLift 7067036
  have htrace : WordTrace (prefixWord ++ tailWord_7067036) baseStart_7067036 baseEnd_7067036 := by
    simpa [prefixWord, tailWord_7067036, baseEnd_7067036] using wordTrace_append hprefix tailTrace_7067036
  have hstable : (prefixWord ++ tailWord_7067036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067036).length < 2 ^ (prefixWord ++ tailWord_7067036).sum := by decide
  have hdescent : baseEnd_7067036 < baseStart_7067036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067056 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 3, 3, 2]
def baseStart_7067056 : Nat := 118140960795 + 7067056 * 2 ^ 59
def prefixEnd_7067056 : Nat := 4983230072969 + 3 ^ 40 * 7067056 * 2
def baseEnd_7067056 : Nat := 3628796540240607344599207

theorem tailTrace_7067056 : CollatzResearch.WordTrace tailWord_7067056 prefixEnd_7067056 3628796540240607344599207 := by
  unfold tailWord_7067056
  simp only [CollatzResearch.WordTrace]
  refine ⟨128878353942635271959574511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171837805256847029279432681 128878353942635271959574511)
  ·
    refine ⟨193317530913952907939361767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128878353942635271959574511 193317530913952907939361767)
    ·
      refine ⟨289976296370929361909042651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193317530913952907939361767 289976296370929361909042651)
      ·
        refine ⟨434964444556394042863563977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289976296370929361909042651 434964444556394042863563977)
        ·
          refine ⟨326223333417295532147672983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434964444556394042863563977 326223333417295532147672983)
          ·
            refine ⟨489335000125943298221509475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326223333417295532147672983 489335000125943298221509475)
            ·
              refine ⟨734002500188914947332264213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489335000125943298221509475 734002500188914947332264213)
              ·
                refine ⟨34406367196355388156199885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 734002500188914947332264213 34406367196355388156199885)
                ·
                  refine ⟨12902387698633270558574957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34406367196355388156199885 12902387698633270558574957)
                  ·
                    refine ⟨4838395386987476459465609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12902387698633270558574957 4838395386987476459465609)
                    ·
                      refine ⟨3628796540240607344599207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838395386987476459465609 3628796540240607344599207)
                      ·
                        rfl

theorem cell23_7067056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 3, 2].length) (baseStart_7067056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067056 prefixEnd_7067056 := by exact prefixLift 7067056
  have htrace : WordTrace (prefixWord ++ tailWord_7067056) baseStart_7067056 baseEnd_7067056 := by
    simpa [prefixWord, tailWord_7067056, baseEnd_7067056] using wordTrace_append hprefix tailTrace_7067056
  have hstable : (prefixWord ++ tailWord_7067056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067056).length < 2 ^ (prefixWord ++ tailWord_7067056).sum := by decide
  have hdescent : baseEnd_7067056 < baseStart_7067056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067076 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7067076 : Nat := 118140960795 + 7067076 * 2 ^ 59
def prefixEnd_7067076 : Nat := 4983230072969 + 3 ^ 40 * 7067076 * 2
def baseEnd_7067076 : Nat := 3628806809853697266349115

theorem tailTrace_7067076 : CollatzResearch.WordTrace tailWord_7067076 prefixEnd_7067076 3628806809853697266349115 := by
  unfold tailWord_7067076
  simp only [CollatzResearch.WordTrace]
  refine ⟨128878718672599043667438541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171838291563465391556584721 128878718672599043667438541)
  ·
    refine ⟨48329519502224641375289453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128878718672599043667438541 48329519502224641375289453)
    ·
      refine ⟨18123569813334240515733545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48329519502224641375289453 18123569813334240515733545)
      ·
        refine ⟨13592677360000680386800159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18123569813334240515733545 13592677360000680386800159)
        ·
          refine ⟨20389016040001020580200239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13592677360000680386800159 20389016040001020580200239)
          ·
            refine ⟨30583524060001530870300359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20389016040001020580200239 30583524060001530870300359)
            ·
              refine ⟨45875286090002296305450539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30583524060001530870300359 45875286090002296305450539)
              ·
                refine ⟨68812929135003444458175809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45875286090002296305450539 68812929135003444458175809)
                ·
                  refine ⟨51609696851252583343631857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68812929135003444458175809 51609696851252583343631857)
                  ·
                    refine ⟨38707272638439437507723893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51609696851252583343631857 38707272638439437507723893)
                    ·
                      refine ⟨3628806809853697266349115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38707272638439437507723893 3628806809853697266349115)
                      ·
                        rfl

theorem cell23_7067076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7067076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067076 prefixEnd_7067076 := by exact prefixLift 7067076
  have htrace : WordTrace (prefixWord ++ tailWord_7067076) baseStart_7067076 baseEnd_7067076 := by
    simpa [prefixWord, tailWord_7067076, baseEnd_7067076] using wordTrace_append hprefix tailTrace_7067076
  have hstable : (prefixWord ++ tailWord_7067076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067076).length < 2 ^ (prefixWord ++ tailWord_7067076).sum := by decide
  have hdescent : baseEnd_7067076 < baseStart_7067076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067089 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_7067089 : Nat := 118140960795 + 7067089 * 2 ^ 59
def prefixEnd_7067089 : Nat := 4983230072969 + 3 ^ 40 * 7067089 * 2
def baseEnd_7067089 : Nat := 3628813485102205715486555

theorem tailTrace_7067089 : CollatzResearch.WordTrace tailWord_7067089 prefixEnd_7067089 3628813485102205715486555 := by
  unfold tailWord_7067089
  simp only [CollatzResearch.WordTrace]
  refine ⟨257757911494150990555100321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171838607662767327036733547 257757911494150990555100321)
  ·
    refine ⟨193318433620613242916325241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257757911494150990555100321 193318433620613242916325241)
    ·
      refine ⟨144988825215459932187243931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193318433620613242916325241 144988825215459932187243931)
      ·
        refine ⟨217483237823189898280865897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144988825215459932187243931 217483237823189898280865897)
        ·
          refine ⟨163112428367392423710649423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217483237823189898280865897 163112428367392423710649423)
          ·
            refine ⟨244668642551088635565974135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163112428367392423710649423 244668642551088635565974135)
            ·
              refine ⟨367002963826632953348961203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244668642551088635565974135 367002963826632953348961203)
              ·
                refine ⟨550504445739949430023441805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367002963826632953348961203 550504445739949430023441805)
                ·
                  refine ⟨206439167152481036258790677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550504445739949430023441805 206439167152481036258790677)
                  ·
                    refine ⟨9676835960272548574630813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 206439167152481036258790677 9676835960272548574630813)
                    ·
                      refine ⟨3628813485102205715486555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676835960272548574630813 3628813485102205715486555)
                      ·
                        rfl

theorem cell23_7067089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_7067089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067089 prefixEnd_7067089 := by exact prefixLift 7067089
  have htrace : WordTrace (prefixWord ++ tailWord_7067089) baseStart_7067089 baseEnd_7067089 := by
    simpa [prefixWord, tailWord_7067089, baseEnd_7067089] using wordTrace_append hprefix tailTrace_7067089
  have hstable : (prefixWord ++ tailWord_7067089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067089).length < 2 ^ (prefixWord ++ tailWord_7067089).sum := by decide
  have hdescent : baseEnd_7067089 < baseStart_7067089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067103 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 4, 2, 2]
def baseStart_7067103 : Nat := 118140960795 + 7067103 * 2 ^ 59
def prefixEnd_7067103 : Nat := 4983230072969 + 3 ^ 40 * 7067103 * 2
def baseEnd_7067103 : Nat := 3628820673831368660711491

theorem tailTrace_7067103 : CollatzResearch.WordTrace tailWord_7067103 prefixEnd_7067103 3628820673831368660711491 := by
  unfold tailWord_7067103
  simp only [CollatzResearch.WordTrace]
  refine ⟨257758422116100270946109963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171838948077400180630739975 257758422116100270946109963)
  ·
    refine ⟨386637633174150406419164945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257758422116100270946109963 386637633174150406419164945)
    ·
      refine ⟨289978224880612804814373709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386637633174150406419164945 289978224880612804814373709)
      ·
        refine ⟨108741834330229801805390141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289978224880612804814373709 108741834330229801805390141)
        ·
          refine ⟨40778187873836175677021303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108741834330229801805390141 40778187873836175677021303)
          ·
            refine ⟨61167281810754263515531955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40778187873836175677021303 61167281810754263515531955)
            ·
              refine ⟨91750922716131395273297933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61167281810754263515531955 91750922716131395273297933)
              ·
                refine ⟨34406596018549273227486725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91750922716131395273297933 34406596018549273227486725)
                ·
                  refine ⟨6451236753477988730153761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34406596018549273227486725 6451236753477988730153761)
                  ·
                    refine ⟨4838427565108491547615321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6451236753477988730153761 4838427565108491547615321)
                    ·
                      refine ⟨3628820673831368660711491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838427565108491547615321 3628820673831368660711491)
                      ·
                        rfl

theorem cell23_7067103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_7067103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067103 prefixEnd_7067103 := by exact prefixLift 7067103
  have htrace : WordTrace (prefixWord ++ tailWord_7067103) baseStart_7067103 baseEnd_7067103 := by
    simpa [prefixWord, tailWord_7067103, baseEnd_7067103] using wordTrace_append hprefix tailTrace_7067103
  have hstable : (prefixWord ++ tailWord_7067103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067103).length < 2 ^ (prefixWord ++ tailWord_7067103).sum := by decide
  have hdescent : baseEnd_7067103 < baseStart_7067103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067114 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_7067114 : Nat := 118140960795 + 7067114 * 2 ^ 59
def prefixEnd_7067114 : Nat := 4983230072969 + 3 ^ 40 * 7067114 * 2
def baseEnd_7067114 : Nat := 3628826322118568117673941

theorem tailTrace_7067114 : CollatzResearch.WordTrace tailWord_7067114 prefixEnd_7067114 3628826322118568117673941 := by
  unfold tailWord_7067114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64439705829765104956190099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171839215546040279883173597 64439705829765104956190099)
  ·
    refine ⟨96659558744647657434285149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64439705829765104956190099 96659558744647657434285149)
    ·
      refine ⟨36247334529242871537856931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96659558744647657434285149 36247334529242871537856931)
      ·
        refine ⟨54371001793864307306785397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36247334529242871537856931 54371001793864307306785397)
        ·
          refine ⟨5097281418174778810011131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54371001793864307306785397 5097281418174778810011131)
          ·
            refine ⟨7645922127262168215016697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097281418174778810011131 7645922127262168215016697)
            ·
              refine ⟨5734441595446626161262523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7645922127262168215016697 5734441595446626161262523)
              ·
                refine ⟨8601662393169939241893785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734441595446626161262523 8601662393169939241893785)
                ·
                  refine ⟨6451246794877454431420339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601662393169939241893785 6451246794877454431420339)
                  ·
                    refine ⟨9676870192316181647130509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6451246794877454431420339 9676870192316181647130509)
                    ·
                      refine ⟨3628826322118568117673941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9676870192316181647130509 3628826322118568117673941)
                      ·
                        rfl

theorem cell23_7067114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_7067114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067114 prefixEnd_7067114 := by exact prefixLift 7067114
  have htrace : WordTrace (prefixWord ++ tailWord_7067114) baseStart_7067114 baseEnd_7067114 := by
    simpa [prefixWord, tailWord_7067114, baseEnd_7067114] using wordTrace_append hprefix tailTrace_7067114
  have hstable : (prefixWord ++ tailWord_7067114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067114).length < 2 ^ (prefixWord ++ tailWord_7067114).sum := by decide
  have hdescent : baseEnd_7067114 < baseStart_7067114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067120 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 2, 2, 2]
def baseStart_7067120 : Nat := 118140960795 + 7067120 * 2 ^ 59
def prefixEnd_7067120 : Nat := 4983230072969 + 3 ^ 40 * 7067120 * 2
def baseEnd_7067120 : Nat := 3628829403002495094198913

theorem tailTrace_7067120 : CollatzResearch.WordTrace tailWord_7067120 prefixEnd_7067120 3628829403002495094198913 := by
  unfold tailWord_7067120
  simp only [CollatzResearch.WordTrace]
  refine ⟨128879521078519341424739407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171839361438025788566319209 128879521078519341424739407)
  ·
    refine ⟨193319281617779012137109111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128879521078519341424739407 193319281617779012137109111)
    ·
      refine ⟨289978922426668518205663667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193319281617779012137109111 289978922426668518205663667)
      ·
        refine ⟨434968383640002777308495501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289978922426668518205663667 434968383640002777308495501)
        ·
          refine ⟨163113143865001041490685813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434968383640002777308495501 163113143865001041490685813)
          ·
            refine ⟨15291857237343847639751795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163113143865001041490685813 15291857237343847639751795)
            ·
              refine ⟨22937785856015771459627693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15291857237343847639751795 22937785856015771459627693)
              ·
                refine ⟨8601669696005914297360385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22937785856015771459627693 8601669696005914297360385)
                ·
                  refine ⟨6451252272004435723020289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601669696005914297360385 6451252272004435723020289)
                  ·
                    refine ⟨4838439204003326792265217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6451252272004435723020289 4838439204003326792265217)
                    ·
                      refine ⟨3628829403002495094198913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838439204003326792265217 3628829403002495094198913)
                      ·
                        rfl

theorem cell23_7067120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 2, 2].length) (baseStart_7067120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067120 prefixEnd_7067120 := by exact prefixLift 7067120
  have htrace : WordTrace (prefixWord ++ tailWord_7067120) baseStart_7067120 baseEnd_7067120 := by
    simpa [prefixWord, tailWord_7067120, baseEnd_7067120] using wordTrace_append hprefix tailTrace_7067120
  have hstable : (prefixWord ++ tailWord_7067120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067120).length < 2 ^ (prefixWord ++ tailWord_7067120).sum := by decide
  have hdescent : baseEnd_7067120 < baseStart_7067120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067193 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7067193 : Nat := 118140960795 + 7067193 * 2 ^ 59
def prefixEnd_7067193 : Nat := 4983230072969 + 3 ^ 40 * 7067193 * 2
def baseEnd_7067193 : Nat := 3628866887090273308586077

theorem tailTrace_7067193 : CollatzResearch.WordTrace tailWord_7067193 prefixEnd_7067193 3628866887090273308586077 := by
  unfold tailWord_7067193
  simp only [CollatzResearch.WordTrace]
  refine ⟨257761704685774216316886233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171841136457182810877924155 257761704685774216316886233)
  ·
    refine ⟨193321278514330662237664675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257761704685774216316886233 193321278514330662237664675)
    ·
      refine ⟨289981917771495993356497013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193321278514330662237664675 289981917771495993356497013)
      ·
        refine ⟨27185804791077749377171595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289981917771495993356497013 27185804791077749377171595)
        ·
          refine ⟨40778707186616624065757393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27185804791077749377171595 40778707186616624065757393)
          ·
            refine ⟨30584030389962468049318045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40778707186616624065757393 30584030389962468049318045)
            ·
              refine ⟨11469011396235925518494267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30584030389962468049318045 11469011396235925518494267)
              ·
                refine ⟨17203517094353888277741401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11469011396235925518494267 17203517094353888277741401)
                ·
                  refine ⟨12902637820765416208306051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17203517094353888277741401 12902637820765416208306051)
                  ·
                    refine ⟨19353956731148124312459077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12902637820765416208306051 19353956731148124312459077)
                    ·
                      refine ⟨3628866887090273308586077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19353956731148124312459077 3628866887090273308586077)
                      ·
                        rfl

theorem cell23_7067193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7067193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067193 prefixEnd_7067193 := by exact prefixLift 7067193
  have htrace : WordTrace (prefixWord ++ tailWord_7067193) baseStart_7067193 baseEnd_7067193 := by
    simpa [prefixWord, tailWord_7067193, baseEnd_7067193] using wordTrace_append hprefix tailTrace_7067193
  have hstable : (prefixWord ++ tailWord_7067193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067193).length < 2 ^ (prefixWord ++ tailWord_7067193).sum := by decide
  have hdescent : baseEnd_7067193 < baseStart_7067193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067220 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_7067220 : Nat := 118140960795 + 7067220 * 2 ^ 59
def prefixEnd_7067220 : Nat := 4983230072969 + 3 ^ 40 * 7067220 * 2
def baseEnd_7067220 : Nat := 1209626917022648234316151

theorem tailTrace_7067220 : CollatzResearch.WordTrace tailWord_7067220 prefixEnd_7067220 1209626917022648234316151 := by
  unfold tailWord_7067220
  simp only [CollatzResearch.WordTrace]
  refine ⟨128881344728338199964059557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171841792971117599952079409 128881344728338199964059557)
  ·
    refine ⟨24165252136563412493261167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128881344728338199964059557 24165252136563412493261167)
    ·
      refine ⟨36247878204845118739891751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24165252136563412493261167 36247878204845118739891751)
      ·
        refine ⟨54371817307267678109837627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36247878204845118739891751 54371817307267678109837627)
        ·
          refine ⟨81557725960901517164756441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54371817307267678109837627 81557725960901517164756441)
          ·
            refine ⟨61168294470676137873567331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81557725960901517164756441 61168294470676137873567331)
            ·
              refine ⟨91752441706014206810350997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61168294470676137873567331 91752441706014206810350997)
              ·
                refine ⟨4300895704969415944235203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91752441706014206810350997 4300895704969415944235203)
                ·
                  refine ⟨6451343557454123916352805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300895704969415944235203 6451343557454123916352805)
                  ·
                    refine ⟨1209626917022648234316151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6451343557454123916352805 1209626917022648234316151)
                    ·
                      rfl

theorem cell23_7067220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_7067220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067220 prefixEnd_7067220 := by exact prefixLift 7067220
  have htrace : WordTrace (prefixWord ++ tailWord_7067220) baseStart_7067220 baseEnd_7067220 := by
    simpa [prefixWord, tailWord_7067220, baseEnd_7067220] using wordTrace_append hprefix tailTrace_7067220
  have hstable : (prefixWord ++ tailWord_7067220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067220).length < 2 ^ (prefixWord ++ tailWord_7067220).sum := by decide
  have hdescent : baseEnd_7067220 < baseStart_7067220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067233 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 6]
def baseStart_7067233 : Nat := 118140960795 + 7067233 * 2 ^ 59
def prefixEnd_7067233 : Nat := 4983230072969 + 3 ^ 40 * 7067233 * 2
def baseEnd_7067233 : Nat := 403209714035161461342877

theorem tailTrace_7067233 : CollatzResearch.WordTrace tailWord_7067233 prefixEnd_7067233 403209714035161461342877 := by
  unfold tailWord_7067233
  simp only [CollatzResearch.WordTrace]
  refine ⟨257763163605629303148342353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171842109070419535432228235 257763163605629303148342353)
  ·
    refine ⟨193322372704221977361256765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257763163605629303148342353 193322372704221977361256765)
    ·
      refine ⟨72495889764083241510471287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193322372704221977361256765 72495889764083241510471287)
      ·
        refine ⟨108743834646124862265706931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72495889764083241510471287 108743834646124862265706931)
        ·
          refine ⟨163115751969187293398560397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108743834646124862265706931 163115751969187293398560397)
          ·
            refine ⟨61168406988445235024460149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163115751969187293398560397 61168406988445235024460149)
            ·
              refine ⟨5734538155166740783543139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61168406988445235024460149 5734538155166740783543139)
              ·
                refine ⟨8601807232750111175314709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734538155166740783543139 8601807232750111175314709)
                ·
                  refine ⟨403209714035161461342877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8601807232750111175314709 403209714035161461342877)
                  ·
                    rfl

theorem cell23_7067233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 6].length) (baseStart_7067233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067233 prefixEnd_7067233 := by exact prefixLift 7067233
  have htrace : WordTrace (prefixWord ++ tailWord_7067233) baseStart_7067233 baseEnd_7067233 := by
    simpa [prefixWord, tailWord_7067233, baseEnd_7067233] using wordTrace_append hprefix tailTrace_7067233
  have hstable : (prefixWord ++ tailWord_7067233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067233).length < 2 ^ (prefixWord ++ tailWord_7067233).sum := by decide
  have hdescent : baseEnd_7067233 < baseStart_7067233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067254 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_7067254 : Nat := 118140960795 + 7067254 * 2 ^ 59
def prefixEnd_7067254 : Nat := 4983230072969 + 3 ^ 40 * 7067254 * 2
def baseEnd_7067254 : Nat := 1209632736470065856641099

theorem tailTrace_7067254 : CollatzResearch.WordTrace tailWord_7067254 prefixEnd_7067254 1209632736470065856641099 := by
  unfold tailWord_7067254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110245596159576483428551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171842619692368815823237877 16110245596159576483428551)
  ·
    refine ⟨24165368394239364725142827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16110245596159576483428551 24165368394239364725142827)
    ·
      refine ⟨36248052591359047087714241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24165368394239364725142827 36248052591359047087714241)
      ·
        refine ⟨27186039443519285315785681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36248052591359047087714241 27186039443519285315785681)
        ·
          refine ⟨20389529582639463986839261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27186039443519285315785681 20389529582639463986839261)
          ·
            refine ⟨7646073593489798995064723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20389529582639463986839261 7646073593489798995064723)
            ·
              refine ⟨11469110390234698492597085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646073593489798995064723 11469110390234698492597085)
              ·
                refine ⟨4300916396338011934723907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11469110390234698492597085 4300916396338011934723907)
                ·
                  refine ⟨6451374594507017902085861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4300916396338011934723907 6451374594507017902085861)
                  ·
                    refine ⟨1209632736470065856641099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6451374594507017902085861 1209632736470065856641099)
                    ·
                      rfl

theorem cell23_7067254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_7067254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067254 prefixEnd_7067254 := by exact prefixLift 7067254
  have htrace : WordTrace (prefixWord ++ tailWord_7067254) baseStart_7067254 baseEnd_7067254 := by
    simpa [prefixWord, tailWord_7067254, baseEnd_7067254] using wordTrace_append hprefix tailTrace_7067254
  have hstable : (prefixWord ++ tailWord_7067254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067254).length < 2 ^ (prefixWord ++ tailWord_7067254).sum := by decide
  have hdescent : baseEnd_7067254 < baseStart_7067254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067284 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 6]
def baseStart_7067284 : Nat := 118140960795 + 7067284 * 2 ^ 59
def prefixEnd_7067284 : Nat := 4983230072969 + 3 ^ 40 * 7067284 * 2
def baseEnd_7067284 : Nat := 403212623758870272505351

theorem tailTrace_7067284 : CollatzResearch.WordTrace tailWord_7067284 prefixEnd_7067284 403212623758870272505351 := by
  unfold tailWord_7067284
  simp only [CollatzResearch.WordTrace]
  refine ⟨128882511864222269429224453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171843349152296359238965937 128882511864222269429224453)
  ·
    refine ⟨24165470974541675517979585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128882511864222269429224453 24165470974541675517979585)
    ·
      refine ⟨18124103230906256638484689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24165470974541675517979585 18124103230906256638484689)
      ·
        refine ⟨13593077423179692478863517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18124103230906256638484689 13593077423179692478863517)
        ·
          refine ⟨5097404033692384679573819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13593077423179692478863517 5097404033692384679573819)
          ·
            refine ⟨7646106050538577019360729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097404033692384679573819 7646106050538577019360729)
            ·
              refine ⟨5734579537903932764520547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646106050538577019360729 5734579537903932764520547)
              ·
                refine ⟨8601869306855899146780821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734579537903932764520547 8601869306855899146780821)
                ·
                  refine ⟨403212623758870272505351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8601869306855899146780821 403212623758870272505351)
                  ·
                    rfl

theorem cell23_7067284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_7067284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067284 prefixEnd_7067284 := by exact prefixLift 7067284
  have htrace : WordTrace (prefixWord ++ tailWord_7067284) baseStart_7067284 baseEnd_7067284 := by
    simpa [prefixWord, tailWord_7067284, baseEnd_7067284] using wordTrace_append hprefix tailTrace_7067284
  have hstable : (prefixWord ++ tailWord_7067284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067284).length < 2 ^ (prefixWord ++ tailWord_7067284).sum := by decide
  have hdescent : baseEnd_7067284 < baseStart_7067284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067300 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_7067300 : Nat := 118140960795 + 7067300 * 2 ^ 59
def prefixEnd_7067300 : Nat := 4983230072969 + 3 ^ 40 * 7067300 * 2
def baseEnd_7067300 : Nat := 3628921829520304389948085

theorem tailTrace_7067300 : CollatzResearch.WordTrace tailWord_7067300 prefixEnd_7067300 3628921829520304389948085 := by
  unfold tailWord_7067300
  simp only [CollatzResearch.WordTrace]
  refine ⟨128882803648193286795515677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171843738197591049060687569 128882803648193286795515677)
  ·
    refine ⟨48331051368072482548318379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128882803648193286795515677 48331051368072482548318379)
    ·
      refine ⟨72496577052108723822477569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48331051368072482548318379 72496577052108723822477569)
      ·
        refine ⟨54372432789081542866858177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72496577052108723822477569 54372432789081542866858177)
        ·
          refine ⟨40779324591811157150143633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54372432789081542866858177 40779324591811157150143633)
          ·
            refine ⟨30584493443858367862607725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40779324591811157150143633 30584493443858367862607725)
            ·
              refine ⟨11469185041446887948477897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30584493443858367862607725 11469185041446887948477897)
              ·
                refine ⟨8601888781085165961358423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11469185041446887948477897 8601888781085165961358423)
                ·
                  refine ⟨12902833171627748942037635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601888781085165961358423 12902833171627748942037635)
                  ·
                    refine ⟨19354249757441623413056453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12902833171627748942037635 19354249757441623413056453)
                    ·
                      refine ⟨3628921829520304389948085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19354249757441623413056453 3628921829520304389948085)
                      ·
                        rfl

theorem cell23_7067300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_7067300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067300 prefixEnd_7067300 := by exact prefixLift 7067300
  have htrace : WordTrace (prefixWord ++ tailWord_7067300) baseStart_7067300 baseEnd_7067300 := by
    simpa [prefixWord, tailWord_7067300, baseEnd_7067300] using wordTrace_append hprefix tailTrace_7067300
  have hstable : (prefixWord ++ tailWord_7067300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067300).length < 2 ^ (prefixWord ++ tailWord_7067300).sum := by decide
  have hdescent : baseEnd_7067300 < baseStart_7067300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067336 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_7067336 : Nat := 118140960795 + 7067336 * 2 ^ 59
def prefixEnd_7067336 : Nat := 4983230072969 + 3 ^ 40 * 7067336 * 2
def baseEnd_7067336 : Nat := 1209646771607955416365973

theorem tailTrace_7067336 : CollatzResearch.WordTrace tailWord_7067336 prefixEnd_7067336 1209646771607955416365973 := by
  unfold tailWord_7067336
  simp only [CollatzResearch.WordTrace]
  refine ⟨128883460162128075869670931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171844613549504101159561241 128883460162128075869670931)
  ·
    refine ⟨193325190243192113804506397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128883460162128075869670931 193325190243192113804506397)
    ·
      refine ⟨72496946341197042676689899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193325190243192113804506397 72496946341197042676689899)
      ·
        refine ⟨108745419511795564015034849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72496946341197042676689899 108745419511795564015034849)
        ·
          refine ⟨81559064633846673011276137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108745419511795564015034849 81559064633846673011276137)
          ·
            refine ⟨61169298475385004758457103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81559064633846673011276137 61169298475385004758457103)
            ·
              refine ⟨91753947713077507137685655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61169298475385004758457103 91753947713077507137685655)
              ·
                refine ⟨137630921569616260706528483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91753947713077507137685655 137630921569616260706528483)
                ·
                  refine ⟨206446382354424391059792725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137630921569616260706528483 206446382354424391059792725)
                  ·
                    refine ⟨1209646771607955416365973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 206446382354424391059792725 1209646771607955416365973)
                    ·
                      rfl

theorem cell23_7067336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_7067336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067336 prefixEnd_7067336 := by exact prefixLift 7067336
  have htrace : WordTrace (prefixWord ++ tailWord_7067336) baseStart_7067336 baseEnd_7067336 := by
    simpa [prefixWord, tailWord_7067336, baseEnd_7067336] using wordTrace_append hprefix tailTrace_7067336
  have hstable : (prefixWord ++ tailWord_7067336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067336).length < 2 ^ (prefixWord ++ tailWord_7067336).sum := by decide
  have hdescent : baseEnd_7067336 < baseStart_7067336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067340 : List Nat := [2, 2, 1, 5, 2, 2, 1, 8]
def baseStart_7067340 : Nat := 118140960795 + 7067340 * 2 ^ 59
def prefixEnd_7067340 : Nat := 4983230072969 + 3 ^ 40 * 7067340 * 2
def baseEnd_7067340 : Nat := 134405272916536453090663

theorem tailTrace_7067340 : CollatzResearch.WordTrace tailWord_7067340 prefixEnd_7067340 134405272916536453090663 := by
  unfold tailWord_7067340
  simp only [CollatzResearch.WordTrace]
  refine ⟨128883533108120830211243737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171844710810827773614991649 128883533108120830211243737)
  ·
    refine ⟨96662649831090622658432803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128883533108120830211243737 96662649831090622658432803)
    ·
      refine ⟨144993974746635933987649205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96662649831090622658432803 144993974746635933987649205)
      ·
        refine ⟨13593185132497118811342113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144993974746635933987649205 13593185132497118811342113)
        ·
          refine ⟨10194888849372839108506585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13593185132497118811342113 10194888849372839108506585)
          ·
            refine ⟨7646166637029629331379939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10194888849372839108506585 7646166637029629331379939)
            ·
              refine ⟨11469249955544443997069909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646166637029629331379939 11469249955544443997069909)
              ·
                refine ⟨134405272916536453090663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11469249955544443997069909 134405272916536453090663)
                ·
                  rfl

theorem cell23_7067340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 8].length) (baseStart_7067340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067340 prefixEnd_7067340 := by exact prefixLift 7067340
  have htrace : WordTrace (prefixWord ++ tailWord_7067340) baseStart_7067340 baseEnd_7067340 := by
    simpa [prefixWord, tailWord_7067340, baseEnd_7067340] using wordTrace_append hprefix tailTrace_7067340
  have hstable : (prefixWord ++ tailWord_7067340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067340).length < 2 ^ (prefixWord ++ tailWord_7067340).sum := by decide
  have hdescent : baseEnd_7067340 < baseStart_7067340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067357 : List Nat := [1, 4, 3, 3, 1, 1, 3, 7]
def baseStart_7067357 : Nat := 118140960795 + 7067357 * 2 ^ 59
def prefixEnd_7067357 : Nat := 4983230072969 + 3 ^ 40 * 7067357 * 2
def baseEnd_7067357 : Nat := 134405596219170765442049

theorem tailTrace_7067357 : CollatzResearch.WordTrace tailWord_7067357 prefixEnd_7067357 134405596219170765442049 := by
  unfold tailWord_7067357
  simp only [CollatzResearch.WordTrace]
  refine ⟨257767686257180072325856325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171845124171453381550570883 257767686257180072325856325)
  ·
    refine ⟨48331441173221263561098061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257767686257180072325856325 48331441173221263561098061)
    ·
      refine ⟨18124290439957973835411773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48331441173221263561098061 18124290439957973835411773)
      ·
        refine ⟨6796608914984240188279415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18124290439957973835411773 6796608914984240188279415)
        ·
          refine ⟨10194913372476360282419123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796608914984240188279415 10194913372476360282419123)
          ·
            refine ⟨15292370058714540423628685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194913372476360282419123 15292370058714540423628685)
            ·
              refine ⟨5734638772017952658860757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15292370058714540423628685 5734638772017952658860757)
              ·
                refine ⟨134405596219170765442049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5734638772017952658860757 134405596219170765442049)
                ·
                  rfl

theorem cell23_7067357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 7].length) (baseStart_7067357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067357 prefixEnd_7067357 := by exact prefixLift 7067357
  have htrace : WordTrace (prefixWord ++ tailWord_7067357) baseStart_7067357 baseEnd_7067357 := by
    simpa [prefixWord, tailWord_7067357, baseEnd_7067357] using wordTrace_append hprefix tailTrace_7067357
  have hstable : (prefixWord ++ tailWord_7067357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067357).length < 2 ^ (prefixWord ++ tailWord_7067357).sum := by decide
  have hdescent : baseEnd_7067357 < baseStart_7067357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067360 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 3, 3, 2]
def baseStart_7067360 : Nat := 118140960795 + 7067360 * 2 ^ 59
def prefixEnd_7067360 : Nat := 4983230072969 + 3 ^ 40 * 7067360 * 2
def baseEnd_7067360 : Nat := 3628952638359574155197809

theorem tailTrace_7067360 : CollatzResearch.WordTrace tailWord_7067360 prefixEnd_7067360 3628952638359574155197809 := by
  unfold tailWord_7067360
  simp only [CollatzResearch.WordTrace]
  refine ⟨128883897838084601919107767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171845197117446135892143689 128883897838084601919107767)
  ·
    refine ⟨193325846757126902878661651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128883897838084601919107767 193325846757126902878661651)
    ·
      refine ⟨289988770135690354317992477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193325846757126902878661651 289988770135690354317992477)
      ·
        refine ⟨108745788800883882869247179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289988770135690354317992477 108745788800883882869247179)
        ·
          refine ⟨163118683201325824303870769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108745788800883882869247179 163118683201325824303870769)
          ·
            refine ⟨122339012400994368227903077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163118683201325824303870769 122339012400994368227903077)
            ·
              refine ⟨22938564825186444042731827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122339012400994368227903077 22938564825186444042731827)
              ·
                refine ⟨34407847237779666064097741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22938564825186444042731827 34407847237779666064097741)
                ·
                  refine ⟨12902942714167374774036653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34407847237779666064097741 12902942714167374774036653)
                  ·
                    refine ⟨4838603517812765540263745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12902942714167374774036653 4838603517812765540263745)
                    ·
                      refine ⟨3628952638359574155197809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838603517812765540263745 3628952638359574155197809)
                      ·
                        rfl

theorem cell23_7067360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_7067360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067360 prefixEnd_7067360 := by exact prefixLift 7067360
  have htrace : WordTrace (prefixWord ++ tailWord_7067360) baseStart_7067360 baseEnd_7067360 := by
    simpa [prefixWord, tailWord_7067360, baseEnd_7067360] using wordTrace_append hprefix tailTrace_7067360
  have hstable : (prefixWord ++ tailWord_7067360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067360).length < 2 ^ (prefixWord ++ tailWord_7067360).sum := by decide
  have hdescent : baseEnd_7067360 < baseStart_7067360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067377 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 1, 3, 2]
def baseStart_7067377 : Nat := 118140960795 + 7067377 * 2 ^ 59
def prefixEnd_7067377 : Nat := 4983230072969 + 3 ^ 40 * 7067377 * 2
def baseEnd_7067377 : Nat := 3628961367530700588685231

theorem tailTrace_7067377 : CollatzResearch.WordTrace tailWord_7067377 prefixEnd_7067377 3628961367530700588685231 := by
  unfold tailWord_7067377
  simp only [CollatzResearch.WordTrace]
  refine ⟨257768415717107615741584385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171845610478071743827722923 257768415717107615741584385)
  ·
    refine ⟨193326311787830711806188289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257768415717107615741584385 193326311787830711806188289)
    ·
      refine ⟨144994733840873033854641217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193326311787830711806188289 144994733840873033854641217)
      ·
        refine ⟨108746050380654775390980913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144994733840873033854641217 108746050380654775390980913)
        ·
          refine ⟨81559537785491081543235685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108746050380654775390980913 81559537785491081543235685)
          ·
            refine ⟨15292413334779577789356691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81559537785491081543235685 15292413334779577789356691)
            ·
              refine ⟨22938620002169366684035037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15292413334779577789356691 22938620002169366684035037)
              ·
                refine ⟨8601982500813512506513139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22938620002169366684035037 8601982500813512506513139)
                ·
                  refine ⟨12902973751220268759769709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601982500813512506513139 12902973751220268759769709)
                  ·
                    refine ⟨4838615156707600784913641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12902973751220268759769709 4838615156707600784913641)
                    ·
                      refine ⟨3628961367530700588685231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838615156707600784913641 3628961367530700588685231)
                      ·
                        rfl

theorem cell23_7067377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_7067377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067377 prefixEnd_7067377 := by exact prefixLift 7067377
  have htrace : WordTrace (prefixWord ++ tailWord_7067377) baseStart_7067377 baseEnd_7067377 := by
    simpa [prefixWord, tailWord_7067377, baseEnd_7067377] using wordTrace_append hprefix tailTrace_7067377
  have hstable : (prefixWord ++ tailWord_7067377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067377).length < 2 ^ (prefixWord ++ tailWord_7067377).sum := by decide
  have hdescent : baseEnd_7067377 < baseStart_7067377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067393 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_7067393 : Nat := 118140960795 + 7067393 * 2 ^ 59
def prefixEnd_7067393 : Nat := 4983230072969 + 3 ^ 40 * 7067393 * 2
def baseEnd_7067393 : Nat := 3628969583221172526085157

theorem tailTrace_7067393 : CollatzResearch.WordTrace tailWord_7067393 prefixEnd_7067393 3628969583221172526085157 := by
  unfold tailWord_7067393
  simp only [CollatzResearch.WordTrace]
  refine ⟨257768999285049650474166833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171845999523366433649444555 257768999285049650474166833)
  ·
    refine ⟨193326749463787237855625125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257768999285049650474166833 193326749463787237855625125)
    ·
      refine ⟨36248765524460107097929711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193326749463787237855625125 36248765524460107097929711)
      ·
        refine ⟨54373148286690160646894567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36248765524460107097929711 54373148286690160646894567)
        ·
          refine ⟨81559722430035240970341851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54373148286690160646894567 81559722430035240970341851)
          ·
            refine ⟨122339583645052861455512777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81559722430035240970341851 122339583645052861455512777)
            ·
              refine ⟨91754687733789646091634583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122339583645052861455512777 91754687733789646091634583)
              ·
                refine ⟨137632031600684469137451875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91754687733789646091634583 137632031600684469137451875)
                ·
                  refine ⟨206448047401026703706177813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137632031600684469137451875 206448047401026703706177813)
                  ·
                    refine ⟨9677252221923126736227085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 206448047401026703706177813 9677252221923126736227085)
                    ·
                      refine ⟨3628969583221172526085157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9677252221923126736227085 3628969583221172526085157)
                      ·
                        rfl

theorem cell23_7067393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_7067393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067393 prefixEnd_7067393 := by exact prefixLift 7067393
  have htrace : WordTrace (prefixWord ++ tailWord_7067393) baseStart_7067393 baseEnd_7067393 := by
    simpa [prefixWord, tailWord_7067393, baseEnd_7067393] using wordTrace_append hprefix tailTrace_7067393
  have hstable : (prefixWord ++ tailWord_7067393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067393).length < 2 ^ (prefixWord ++ tailWord_7067393).sum := by decide
  have hdescent : baseEnd_7067393 < baseStart_7067393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067403 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4]
def baseStart_7067403 : Nat := 118140960795 + 7067403 * 2 ^ 59
def prefixEnd_7067403 : Nat := 4983230072969 + 3 ^ 40 * 7067403 * 2
def baseEnd_7067403 : Nat := 3628974718027717486960111

theorem tailTrace_7067403 : CollatzResearch.WordTrace tailWord_7067403 prefixEnd_7067403 3628974718027717486960111 := by
  unfold tailWord_7067403
  simp only [CollatzResearch.WordTrace]
  refine ⟨257769364015013422182030863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171846242676675614788020575 257769364015013422182030863)
  ·
    refine ⟨386654046022520133273046295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257769364015013422182030863 386654046022520133273046295)
    ·
      refine ⟨579981069033780199909569443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386654046022520133273046295 579981069033780199909569443)
      ·
        refine ⟨869971603550670299864354165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579981069033780199909569443 869971603550670299864354165)
        ·
          refine ⟨81559837832875340612283203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 869971603550670299864354165 81559837832875340612283203)
          ·
            refine ⟨122339756749313010918424805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81559837832875340612283203 122339756749313010918424805)
            ·
              refine ⟨22938704390496189547204651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122339756749313010918424805 22938704390496189547204651)
              ·
                refine ⟨34408056585744284320806977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22938704390496189547204651 34408056585744284320806977)
                ·
                  refine ⟨25806042439308213240605233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34408056585744284320806977 25806042439308213240605233)
                  ·
                    refine ⟨19354531829481159930453925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25806042439308213240605233 19354531829481159930453925)
                    ·
                      refine ⟨3628974718027717486960111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19354531829481159930453925 3628974718027717486960111)
                      ·
                        rfl

theorem cell23_7067403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_7067403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067403 prefixEnd_7067403 := by exact prefixLift 7067403
  have htrace : WordTrace (prefixWord ++ tailWord_7067403) baseStart_7067403 baseEnd_7067403 := by
    simpa [prefixWord, tailWord_7067403, baseEnd_7067403] using wordTrace_append hprefix tailTrace_7067403
  have hstable : (prefixWord ++ tailWord_7067403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067403).length < 2 ^ (prefixWord ++ tailWord_7067403).sum := by decide
  have hdescent : baseEnd_7067403 < baseStart_7067403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067413 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 7]
def baseStart_7067413 : Nat := 118140960795 + 7067413 * 2 ^ 59
def prefixEnd_7067413 : Nat := 4983230072969 + 3 ^ 40 * 7067413 * 2
def baseEnd_7067413 : Nat := 403219983648251383092785

theorem tailTrace_7067413 : CollatzResearch.WordTrace tailWord_7067413 prefixEnd_7067413 403219983648251383092785 := by
  unfold tailWord_7067413
  simp only [CollatzResearch.WordTrace]
  refine ⟨257769728744977193889894893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171846485829984795926596595 257769728744977193889894893)
  ·
    refine ⟨96663648279366447708710585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257769728744977193889894893 96663648279366447708710585)
    ·
      refine ⟨72497736209524835781532939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96663648279366447708710585 72497736209524835781532939)
      ·
        refine ⟨108746604314287253672299409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72497736209524835781532939 108746604314287253672299409)
        ·
          refine ⟨81559953235715440254224557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108746604314287253672299409 81559953235715440254224557)
          ·
            refine ⟨30584982463393290095334209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81559953235715440254224557 30584982463393290095334209)
            ·
              refine ⟨22938736847544967571500657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30584982463393290095334209 22938736847544967571500657)
              ·
                refine ⟨17204052635658725678625493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22938736847544967571500657 17204052635658725678625493)
                ·
                  refine ⟨403219983648251383092785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17204052635658725678625493 403219983648251383092785)
                  ·
                    rfl

theorem cell23_7067413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_7067413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067413 prefixEnd_7067413 := by exact prefixLift 7067413
  have htrace : WordTrace (prefixWord ++ tailWord_7067413) baseStart_7067413 baseEnd_7067413 := by
    simpa [prefixWord, tailWord_7067413, baseEnd_7067413] using wordTrace_append hprefix tailTrace_7067413
  have hstable : (prefixWord ++ tailWord_7067413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067413).length < 2 ^ (prefixWord ++ tailWord_7067413).sum := by decide
  have hdescent : baseEnd_7067413 < baseStart_7067413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067463 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_7067463 : Nat := 118140960795 + 7067463 * 2 ^ 59
def prefixEnd_7067463 : Nat := 4983230072969 + 3 ^ 40 * 7067463 * 2
def baseEnd_7067463 : Nat := 3629005526866987252209835

theorem tailTrace_7067463 : CollatzResearch.WordTrace tailWord_7067463 prefixEnd_7067463 3629005526866987252209835 := by
  unfold tailWord_7067463
  simp only [CollatzResearch.WordTrace]
  refine ⟨257771552394796052429215043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171847701596530701619476695 257771552394796052429215043)
  ·
    refine ⟨386657328592194078643822565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257771552394796052429215043 386657328592194078643822565)
    ·
      refine ⟨72498249111036389745716731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386657328592194078643822565 72498249111036389745716731)
      ·
        refine ⟨108747373666554584618575097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72498249111036389745716731 108747373666554584618575097)
        ·
          refine ⟨81560530249915938463931323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108747373666554584618575097 81560530249915938463931323)
          ·
            refine ⟨122340795374873907695896985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81560530249915938463931323 122340795374873907695896985)
            ·
              refine ⟨91755596531155430771922739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122340795374873907695896985 91755596531155430771922739)
              ·
                refine ⟨137633394796733146157884109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91755596531155430771922739 137633394796733146157884109)
                ·
                  refine ⟨51612523048774929809206541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137633394796733146157884109 51612523048774929809206541)
                  ·
                    refine ⟨19354696143290598678452453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51612523048774929809206541 19354696143290598678452453)
                    ·
                      refine ⟨3629005526866987252209835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19354696143290598678452453 3629005526866987252209835)
                      ·
                        rfl

theorem cell23_7067463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_7067463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067463 prefixEnd_7067463 := by exact prefixLift 7067463
  have htrace : WordTrace (prefixWord ++ tailWord_7067463) baseStart_7067463 baseEnd_7067463 := by
    simpa [prefixWord, tailWord_7067463, baseEnd_7067463] using wordTrace_append hprefix tailTrace_7067463
  have hstable : (prefixWord ++ tailWord_7067463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067463).length < 2 ^ (prefixWord ++ tailWord_7067463).sum := by decide
  have hdescent : baseEnd_7067463 < baseStart_7067463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067480 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 6, 4, 2]
def baseStart_7067480 : Nat := 118140960795 + 7067480 * 2 ^ 59
def prefixEnd_7067480 : Nat := 4983230072969 + 3 ^ 40 * 7067480 * 2
def baseEnd_7067480 : Nat := 3629014256038113685697257

theorem tailTrace_7067480 : CollatzResearch.WordTrace tailWord_7067480 prefixEnd_7067480 3629014256038113685697257 := by
  unfold tailWord_7067480
  simp only [CollatzResearch.WordTrace]
  refine ⟨128886086217867232166291947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171848114957156309555055929 128886086217867232166291947)
  ·
    refine ⟨193329129326800848249437921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128886086217867232166291947 193329129326800848249437921)
    ·
      refine ⟨144996846995100636187078441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193329129326800848249437921 144996846995100636187078441)
      ·
        refine ⟨108747635246325477140308831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144996846995100636187078441 108747635246325477140308831)
        ·
          refine ⟨163121452869488215710463247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108747635246325477140308831 163121452869488215710463247)
          ·
            refine ⟨244682179304232323565694871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163121452869488215710463247 244682179304232323565694871)
            ·
              refine ⟨367023268956348485348542307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244682179304232323565694871 367023268956348485348542307)
              ·
                refine ⟨550534903434522728022813461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367023268956348485348542307 550534903434522728022813461)
                ·
                  refine ⟨25806323598493252876069381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 550534903434522728022813461 25806323598493252876069381)
                  ·
                    refine ⟨4838685674717484914263009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25806323598493252876069381 4838685674717484914263009)
                    ·
                      refine ⟨3629014256038113685697257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838685674717484914263009 3629014256038113685697257)
                      ·
                        rfl

theorem cell23_7067480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_7067480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067480 prefixEnd_7067480 := by exact prefixLift 7067480
  have htrace : WordTrace (prefixWord ++ tailWord_7067480) baseStart_7067480 baseEnd_7067480 := by
    simpa [prefixWord, tailWord_7067480, baseEnd_7067480] using wordTrace_append hprefix tailTrace_7067480
  have hstable : (prefixWord ++ tailWord_7067480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067480).length < 2 ^ (prefixWord ++ tailWord_7067480).sum := by decide
  have hdescent : baseEnd_7067480 < baseStart_7067480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067493 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7067493 : Nat := 118140960795 + 7067493 * 2 ^ 59
def prefixEnd_7067493 : Nat := 4983230072969 + 3 ^ 40 * 7067493 * 2
def baseEnd_7067493 : Nat := 3629020931286622134834697

theorem tailTrace_7067493 : CollatzResearch.WordTrace tailWord_7067493 prefixEnd_7067493 3629020931286622134834697 := by
  unfold tailWord_7067493
  simp only [CollatzResearch.WordTrace]
  refine ⟨257772646584687367552807133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171848431056458245035204755 257772646584687367552807133)
  ·
    refine ⟨96664742469257762832302675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257772646584687367552807133 96664742469257762832302675)
    ·
      refine ⟨144997113703886644248454013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96664742469257762832302675 144997113703886644248454013)
      ·
        refine ⟨54373917638957491593170255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144997113703886644248454013 54373917638957491593170255)
        ·
          refine ⟨81560876458436237389755383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54373917638957491593170255 81560876458436237389755383)
          ·
            refine ⟨122341314687654356084633075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81560876458436237389755383 122341314687654356084633075)
            ·
              refine ⟨183511972031481534126949613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122341314687654356084633075 183511972031481534126949613)
              ·
                refine ⟨68816989511805575297606105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183511972031481534126949613 68816989511805575297606105)
                ·
                  refine ⟨51612742133854181473204579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68816989511805575297606105 51612742133854181473204579)
                  ·
                    refine ⟨77419113200781272209806869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51612742133854181473204579 77419113200781272209806869)
                    ·
                      refine ⟨3629020931286622134834697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77419113200781272209806869 3629020931286622134834697)
                      ·
                        rfl

theorem cell23_7067493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7067493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067493 prefixEnd_7067493 := by exact prefixLift 7067493
  have htrace : WordTrace (prefixWord ++ tailWord_7067493) baseStart_7067493 baseEnd_7067493 := by
    simpa [prefixWord, tailWord_7067493, baseEnd_7067493] using wordTrace_append hprefix tailTrace_7067493
  have hstable : (prefixWord ++ tailWord_7067493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067493).length < 2 ^ (prefixWord ++ tailWord_7067493).sum := by decide
  have hdescent : baseEnd_7067493 < baseStart_7067493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067498 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_7067498 : Nat := 118140960795 + 7067498 * 2 ^ 59
def prefixEnd_7067498 : Nat := 4983230072969 + 3 ^ 40 * 7067498 * 2
def baseEnd_7067498 : Nat := 403224833187766068363575

theorem tailTrace_7067498 : CollatzResearch.WordTrace tailWord_7067498 prefixEnd_7067498 403224833187766068363575 := by
  unfold tailWord_7067498
  simp only [CollatzResearch.WordTrace]
  refine ⟨64443207237417313351684787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171848552633112835604492765 64443207237417313351684787)
  ·
    refine ⟨96664810856125970027527181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64443207237417313351684787 96664810856125970027527181)
    ·
      refine ⟨36249304071047238760322693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96664810856125970027527181 36249304071047238760322693)
      ·
        refine ⟨6796744513321357267560505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36249304071047238760322693 6796744513321357267560505)
        ·
          refine ⟨5097558384991017950670379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6796744513321357267560505 5097558384991017950670379)
          ·
            refine ⟨7646337577486526926005569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097558384991017950670379 7646337577486526926005569)
            ·
              refine ⟨5734753183114895194504177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646337577486526926005569 5734753183114895194504177)
              ·
                refine ⟨4301064887336171395878133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5734753183114895194504177 4301064887336171395878133)
                ·
                  refine ⟨403224833187766068363575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301064887336171395878133 403224833187766068363575)
                  ·
                    rfl

theorem cell23_7067498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_7067498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067498 prefixEnd_7067498 := by exact prefixLift 7067498
  have htrace : WordTrace (prefixWord ++ tailWord_7067498) baseStart_7067498 baseEnd_7067498 := by
    simpa [prefixWord, tailWord_7067498, baseEnd_7067498] using wordTrace_append hprefix tailTrace_7067498
  have hstable : (prefixWord ++ tailWord_7067498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067498).length < 2 ^ (prefixWord ++ tailWord_7067498).sum := by decide
  have hdescent : baseEnd_7067498 < baseStart_7067498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067534 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7067534 : Nat := 118140960795 + 7067534 * 2 ^ 59
def prefixEnd_7067534 : Nat := 4983230072969 + 3 ^ 40 * 7067534 * 2
def baseEnd_7067534 : Nat := 3629041983993456474422009

theorem tailTrace_7067534 : CollatzResearch.WordTrace tailWord_7067534 prefixEnd_7067534 3629041983993456474422009 := by
  unfold tailWord_7067534
  simp only [CollatzResearch.WordTrace]
  refine ⟨32221767747192353944381207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171849427985025887703366437 32221767747192353944381207)
  ·
    refine ⟨48332651620788530916571811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32221767747192353944381207 48332651620788530916571811)
    ·
      refine ⟨72498977431182796374857717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48332651620788530916571811 72498977431182796374857717)
      ·
        refine ⟨6796779134173387160142911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72498977431182796374857717 6796779134173387160142911)
        ·
          refine ⟨10195168701260080740214367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796779134173387160142911 10195168701260080740214367)
          ·
            refine ⟨15292753051890121110321551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10195168701260080740214367 15292753051890121110321551)
            ·
              refine ⟨22939129577835181665482327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15292753051890121110321551 22939129577835181665482327)
              ·
                refine ⟨34408694366752772498223491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22939129577835181665482327 34408694366752772498223491)
                ·
                  refine ⟨51613041550129158747335237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34408694366752772498223491 51613041550129158747335237)
                  ·
                    refine ⟨9677445290649217265125357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51613041550129158747335237 9677445290649217265125357)
                    ·
                      refine ⟨3629041983993456474422009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9677445290649217265125357 3629041983993456474422009)
                      ·
                        rfl

theorem cell23_7067534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7067534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067534 prefixEnd_7067534 := by exact prefixLift 7067534
  have htrace : WordTrace (prefixWord ++ tailWord_7067534) baseStart_7067534 baseEnd_7067534 := by
    simpa [prefixWord, tailWord_7067534, baseEnd_7067534] using wordTrace_append hprefix tailTrace_7067534
  have hstable : (prefixWord ++ tailWord_7067534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067534).length < 2 ^ (prefixWord ++ tailWord_7067534).sum := by decide
  have hdescent : baseEnd_7067534 < baseStart_7067534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067554 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_7067554 : Nat := 118140960795 + 7067554 * 2 ^ 59
def prefixEnd_7067554 : Nat := 4983230072969 + 3 ^ 40 * 7067554 * 2
def baseEnd_7067554 : Nat := 403228028178505155130213

theorem tailTrace_7067554 : CollatzResearch.WordTrace tailWord_7067554 prefixEnd_7067554 403228028178505155130213 := by
  unfold tailWord_7067554
  simp only [CollatzResearch.WordTrace]
  refine ⟨64443717859366593742694429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171849914291644249980518477 64443717859366593742694429)
  ·
    refine ⟨24166394197262472653510411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64443717859366593742694429 24166394197262472653510411)
    ·
      refine ⟨36249591295893708980265617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24166394197262472653510411 36249591295893708980265617)
      ·
        refine ⟨27187193471920281735199213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36249591295893708980265617 27187193471920281735199213)
        ·
          refine ⟨10195197551970105650699705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27187193471920281735199213 10195197551970105650699705)
          ·
            refine ⟨7646398163977579238024779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10195197551970105650699705 7646398163977579238024779)
            ·
              refine ⟨11469597245966368857037169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646398163977579238024779 11469597245966368857037169)
              ·
                refine ⟨8602197934474776642777877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11469597245966368857037169 8602197934474776642777877)
                ·
                  refine ⟨403228028178505155130213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8602197934474776642777877 403228028178505155130213)
                  ·
                    rfl

theorem cell23_7067554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_7067554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067554 prefixEnd_7067554 := by exact prefixLift 7067554
  have htrace : WordTrace (prefixWord ++ tailWord_7067554) baseStart_7067554 baseEnd_7067554 := by
    simpa [prefixWord, tailWord_7067554, baseEnd_7067554] using wordTrace_append hprefix tailTrace_7067554
  have hstable : (prefixWord ++ tailWord_7067554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067554).length < 2 ^ (prefixWord ++ tailWord_7067554).sum := by decide
  have hdescent : baseEnd_7067554 < baseStart_7067554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067557 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 2, 3, 2]
def baseStart_7067557 : Nat := 118140960795 + 7067557 * 2 ^ 59
def prefixEnd_7067557 : Nat := 4983230072969 + 3 ^ 40 * 7067557 * 2
def baseEnd_7067557 : Nat := 3629053794048509884434403

theorem tailTrace_7067557 : CollatzResearch.WordTrace tailWord_7067557 prefixEnd_7067557 3629053794048509884434403 := by
  unfold tailWord_7067557
  simp only [CollatzResearch.WordTrace]
  refine ⟨257774980856455506483136925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171849987237637004322091283 257774980856455506483136925)
  ·
    refine ⟨96665617821170814931176347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257774980856455506483136925 96665617821170814931176347)
    ·
      refine ⟨144998426731756222396764521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96665617821170814931176347 144998426731756222396764521)
      ·
        refine ⟨108748820048817166797573391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144998426731756222396764521 108748820048817166797573391)
        ·
          refine ⟨163123230073225750196360087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108748820048817166797573391 163123230073225750196360087)
          ·
            refine ⟨244684845109838625294540131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163123230073225750196360087 244684845109838625294540131)
            ·
              refine ⟨367027267664757937941810197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244684845109838625294540131 367027267664757937941810197)
              ·
                refine ⟨17204403171785528341022353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367027267664757937941810197 17204403171785528341022353)
                ·
                  refine ⟨12903302378839146255766765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17204403171785528341022353 12903302378839146255766765)
                  ·
                    refine ⟨4838738392064679845912537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12903302378839146255766765 4838738392064679845912537)
                    ·
                      refine ⟨3629053794048509884434403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838738392064679845912537 3629053794048509884434403)
                      ·
                        rfl

theorem cell23_7067557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_7067557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067557 prefixEnd_7067557 := by exact prefixLift 7067557
  have htrace : WordTrace (prefixWord ++ tailWord_7067557) baseStart_7067557 baseEnd_7067557 := by
    simpa [prefixWord, tailWord_7067557, baseEnd_7067557] using wordTrace_append hprefix tailTrace_7067557
  have hstable : (prefixWord ++ tailWord_7067557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067557).length < 2 ^ (prefixWord ++ tailWord_7067557).sum := by decide
  have hdescent : baseEnd_7067557 < baseStart_7067557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067570 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_7067570 : Nat := 118140960795 + 7067570 * 2 ^ 59
def prefixEnd_7067570 : Nat := 4983230072969 + 3 ^ 40 * 7067570 * 2
def baseEnd_7067570 : Nat := 3629060469297018333571843

theorem tailTrace_7067570 : CollatzResearch.WordTrace tailWord_7067570 prefixEnd_7067570 3629060469297018333571843 := by
  unfold tailWord_7067570
  simp only [CollatzResearch.WordTrace]
  refine ⟨64443863751352102425840041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171850303336938939802240109 64443863751352102425840041)
  ·
    refine ⟨48332897813514076819380031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64443863751352102425840041 48332897813514076819380031)
    ·
      refine ⟨72499346720271115229070047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48332897813514076819380031 72499346720271115229070047)
      ·
        refine ⟨108749020080406672843605071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72499346720271115229070047 108749020080406672843605071)
        ·
          refine ⟨163123530120610009265407607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108749020080406672843605071 163123530120610009265407607)
          ·
            refine ⟨244685295180915013898111411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163123530120610009265407607 244685295180915013898111411)
            ·
              refine ⟨367027942771372520847167117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244685295180915013898111411 367027942771372520847167117)
              ·
                refine ⟨137635478539264695317687669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367027942771372520847167117 137635478539264695317687669)
                ·
                  refine ⟨12903326113056065186033219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137635478539264695317687669 12903326113056065186033219)
                  ·
                    refine ⟨19354989169584097779049829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12903326113056065186033219 19354989169584097779049829)
                    ·
                      refine ⟨3629060469297018333571843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19354989169584097779049829 3629060469297018333571843)
                      ·
                        rfl

theorem cell23_7067570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_7067570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067570 prefixEnd_7067570 := by exact prefixLift 7067570
  have htrace : WordTrace (prefixWord ++ tailWord_7067570) baseStart_7067570 baseEnd_7067570 := by
    simpa [prefixWord, tailWord_7067570, baseEnd_7067570] using wordTrace_append hprefix tailTrace_7067570
  have hstable : (prefixWord ++ tailWord_7067570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067570).length < 2 ^ (prefixWord ++ tailWord_7067570).sum := by decide
  have hdescent : baseEnd_7067570 < baseStart_7067570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067593 : List Nat := [1, 2, 1, 1, 2, 1, 2, 13]
def baseStart_7067593 : Nat := 118140960795 + 7067593 * 2 ^ 59
def prefixEnd_7067593 : Nat := 4983230072969 + 3 ^ 40 * 7067593 * 2
def baseEnd_7067593 : Nat := 134410084420447101614231

theorem tailTrace_7067593 : CollatzResearch.WordTrace tailWord_7067593 prefixEnd_7067593 134410084420447101614231 := by
  unfold tailWord_7067593
  simp only [CollatzResearch.WordTrace]
  refine ⟨257776293884325084631447433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171850862589550056420964955 257776293884325084631447433)
  ·
    refine ⟨193332220413243813473585575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257776293884325084631447433 193332220413243813473585575)
    ·
      refine ⟨289998330619865720210378363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193332220413243813473585575 289998330619865720210378363)
      ·
        refine ⟨434997495929798580315567545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289998330619865720210378363 434997495929798580315567545)
        ·
          refine ⟨326248121947348935236675659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434997495929798580315567545 326248121947348935236675659)
          ·
            refine ⟨489372182921023402855013489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326248121947348935236675659 489372182921023402855013489)
            ·
              refine ⟨367029137190767552141260117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489372182921023402855013489 367029137190767552141260117)
              ·
                refine ⟨134410084420447101614231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 367029137190767552141260117 134410084420447101614231)
                ·
                  rfl

theorem cell23_7067593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 13].length) (baseStart_7067593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067593 prefixEnd_7067593 := by exact prefixLift 7067593
  have htrace : WordTrace (prefixWord ++ tailWord_7067593) baseStart_7067593 baseEnd_7067593 := by
    simpa [prefixWord, tailWord_7067593, baseEnd_7067593] using wordTrace_append hprefix tailTrace_7067593
  have hstable : (prefixWord ++ tailWord_7067593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067593).length < 2 ^ (prefixWord ++ tailWord_7067593).sum := by decide
  have hdescent : baseEnd_7067593 < baseStart_7067593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067600 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_7067600 : Nat := 118140960795 + 7067600 * 2 ^ 59
def prefixEnd_7067600 : Nat := 4983230072969 + 3 ^ 40 * 7067600 * 2
def baseEnd_7067600 : Nat := 3629075873716653216196705

theorem tailTrace_7067600 : CollatzResearch.WordTrace tailWord_7067600 prefixEnd_7067600 3629075873716653216196705 := by
  unfold tailWord_7067600
  simp only [CollatzResearch.WordTrace]
  refine ⟨128888274597649862413476127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171851032796866483217968169 128888274597649862413476127)
  ·
    refine ⟨193332411896474793620214191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128888274597649862413476127 193332411896474793620214191)
    ·
      refine ⟨289998617844712190430321287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193332411896474793620214191 289998617844712190430321287)
      ·
        refine ⟨434997926767068285645481931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289998617844712190430321287 434997926767068285645481931)
        ·
          refine ⟨652496890150602428468222897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434997926767068285645481931 652496890150602428468222897)
          ·
            refine ⟨489372667612951821351167173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652496890150602428468222897 489372667612951821351167173)
            ·
              refine ⟨91757375177428466503343845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489372667612951821351167173 91757375177428466503343845)
              ·
                refine ⟨17204507845767837469376971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91757375177428466503343845 17204507845767837469376971)
                ·
                  refine ⟨25806761768651756204065457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17204507845767837469376971 25806761768651756204065457)
                  ·
                    refine ⟨19355071326488817153049093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25806761768651756204065457 19355071326488817153049093)
                    ·
                      refine ⟨3629075873716653216196705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19355071326488817153049093 3629075873716653216196705)
                      ·
                        rfl

theorem cell23_7067600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_7067600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067600 prefixEnd_7067600 := by exact prefixLift 7067600
  have htrace : WordTrace (prefixWord ++ tailWord_7067600) baseStart_7067600 baseEnd_7067600 := by
    simpa [prefixWord, tailWord_7067600, baseEnd_7067600] using wordTrace_append hprefix tailTrace_7067600
  have hstable : (prefixWord ++ tailWord_7067600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067600).length < 2 ^ (prefixWord ++ tailWord_7067600).sum := by decide
  have hdescent : baseEnd_7067600 < baseStart_7067600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067607 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_7067607 : Nat := 118140960795 + 7067607 * 2 ^ 59
def prefixEnd_7067607 : Nat := 4983230072969 + 3 ^ 40 * 7067607 * 2
def baseEnd_7067607 : Nat := 3629079468081234688809173

theorem tailTrace_7067607 : CollatzResearch.WordTrace tailWord_7067607 prefixEnd_7067607 3629079468081234688809173 := by
  unfold tailWord_7067607
  simp only [CollatzResearch.WordTrace]
  refine ⟨257776804506274365022457075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171851203004182910014971383 257776804506274365022457075)
  ·
    refine ⟨386665206759411547533685613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257776804506274365022457075 386665206759411547533685613)
    ·
      refine ⟨144999452534779330325132105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386665206759411547533685613 144999452534779330325132105)
      ·
        refine ⟨108749589401084497743849079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144999452534779330325132105 108749589401084497743849079)
        ·
          refine ⟨163124384101626746615773619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108749589401084497743849079 163124384101626746615773619)
          ·
            refine ⟨244686576152440119923660429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163124384101626746615773619 244686576152440119923660429)
            ·
              refine ⟨91757466057165044971372661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244686576152440119923660429 91757466057165044971372661)
              ·
                refine ⟨8602262442859222966066187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91757466057165044971372661 8602262442859222966066187)
                ·
                  refine ⟨12903393664288834449099281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602262442859222966066187 12903393664288834449099281)
                  ·
                    refine ⟨9677545248216625836824461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12903393664288834449099281 9677545248216625836824461)
                    ·
                      refine ⟨3629079468081234688809173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9677545248216625836824461 3629079468081234688809173)
                      ·
                        rfl

theorem cell23_7067607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_7067607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067607 prefixEnd_7067607 := by exact prefixLift 7067607
  have htrace : WordTrace (prefixWord ++ tailWord_7067607) baseStart_7067607 baseEnd_7067607 := by
    simpa [prefixWord, tailWord_7067607, baseEnd_7067607] using wordTrace_append hprefix tailTrace_7067607
  have hstable : (prefixWord ++ tailWord_7067607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067607).length < 2 ^ (prefixWord ++ tailWord_7067607).sum := by decide
  have hdescent : baseEnd_7067607 < baseStart_7067607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067638 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_7067638 : Nat := 118140960795 + 7067638 * 2 ^ 59
def prefixEnd_7067638 : Nat := 4983230072969 + 3 ^ 40 * 7067638 * 2
def baseEnd_7067638 : Nat := 3629095385981524067521531

theorem tailTrace_7067638 : CollatzResearch.WordTrace tailWord_7067638 prefixEnd_7067638 3629095385981524067521531 := by
  unfold tailWord_7067638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111120948072628582302223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171851956779441371544557045 16111120948072628582302223)
  ·
    refine ⟨24166681422108942873453335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16111120948072628582302223 24166681422108942873453335)
    ·
      refine ⟨36250022133163414310180003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24166681422108942873453335 36250022133163414310180003)
      ·
        refine ⟨54375033199745121465270005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36250022133163414310180003 54375033199745121465270005)
        ·
          refine ⟨5097659362476105137369063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54375033199745121465270005 5097659362476105137369063)
          ·
            refine ⟨7646489043714157706053595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097659362476105137369063 7646489043714157706053595)
            ·
              refine ⟨11469733565571236559080393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646489043714157706053595 11469733565571236559080393)
              ·
                refine ⟨8602300174178427419310295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11469733565571236559080393 8602300174178427419310295)
                ·
                  refine ⟨12903450261267641128965443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602300174178427419310295 12903450261267641128965443)
                  ·
                    refine ⟨19355175391901461693448165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12903450261267641128965443 19355175391901461693448165)
                    ·
                      refine ⟨3629095385981524067521531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19355175391901461693448165 3629095385981524067521531)
                      ·
                        rfl

theorem cell23_7067638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_7067638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067638 prefixEnd_7067638 := by exact prefixLift 7067638
  have htrace : WordTrace (prefixWord ++ tailWord_7067638) baseStart_7067638 baseEnd_7067638 := by
    simpa [prefixWord, tailWord_7067638, baseEnd_7067638] using wordTrace_append hprefix tailTrace_7067638
  have hstable : (prefixWord ++ tailWord_7067638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067638).length < 2 ^ (prefixWord ++ tailWord_7067638).sum := by decide
  have hdescent : baseEnd_7067638 < baseStart_7067638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067661 : List Nat := [1, 7, 1, 2, 2, 10]
def baseStart_7067661 : Nat := 118140960795 + 7067661 * 2 ^ 59
def prefixEnd_7067661 : Nat := 4983230072969 + 3 ^ 40 * 7067661 * 2
def baseEnd_7067661 : Nat := 14934597514553816779975

theorem tailTrace_7067661 : CollatzResearch.WordTrace tailWord_7067661 prefixEnd_7067661 14934597514553816779975 := by
  unfold tailWord_7067661
  simp only [CollatzResearch.WordTrace]
  refine ⟨257778774048078732244922837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171852516032052488163281891 257778774048078732244922837)
  ·
    refine ⟨6041690016751845286990379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 257778774048078732244922837 6041690016751845286990379)
    ·
      refine ⟨9062535025127767930485569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041690016751845286990379 9062535025127767930485569)
      ·
        refine ⟨6796901268845825947864177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9062535025127767930485569 6796901268845825947864177)
        ·
          refine ⟨5097675951634369460898133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6796901268845825947864177 5097675951634369460898133)
          ·
            refine ⟨14934597514553816779975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5097675951634369460898133 14934597514553816779975)
            ·
              rfl

theorem cell23_7067661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 10].length) (baseStart_7067661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067661 prefixEnd_7067661 := by exact prefixLift 7067661
  have htrace : WordTrace (prefixWord ++ tailWord_7067661) baseStart_7067661 baseEnd_7067661 := by
    simpa [prefixWord, tailWord_7067661, baseEnd_7067661] using wordTrace_append hprefix tailTrace_7067661
  have hstable : (prefixWord ++ tailWord_7067661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067661).length < 2 ^ (prefixWord ++ tailWord_7067661).sum := by decide
  have hdescent : baseEnd_7067661 < baseStart_7067661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067677 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7067677 : Nat := 118140960795 + 7067677 * 2 ^ 59
def prefixEnd_7067677 : Nat := 4983230072969 + 3 ^ 40 * 7067677 * 2
def baseEnd_7067677 : Nat := 3629115411727049414933851

theorem tailTrace_7067677 : CollatzResearch.WordTrace tailWord_7067677 prefixEnd_7067677 3629115411727049414933851 := by
  unfold tailWord_7067677
  simp only [CollatzResearch.WordTrace]
  refine ⟨257779357616020766977505285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171852905077347177985003523 257779357616020766977505285)
  ·
    refine ⟨48333629553003893808282241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257779357616020766977505285 48333629553003893808282241)
    ·
      refine ⟨36250222164752920356211681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48333629553003893808282241 36250222164752920356211681)
      ·
        refine ⟨27187666623564690267158761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36250222164752920356211681 27187666623564690267158761)
        ·
          refine ⟨20390749967673517700369071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27187666623564690267158761 20390749967673517700369071)
          ·
            refine ⟨30586124951510276550553607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20390749967673517700369071 30586124951510276550553607)
            ·
              refine ⟨45879187427265414825830411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30586124951510276550553607 45879187427265414825830411)
              ·
                refine ⟨68818781140898122238745617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45879187427265414825830411 68818781140898122238745617)
                ·
                  refine ⟨51614085855673591679059213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68818781140898122238745617 51614085855673591679059213)
                  ·
                    refine ⟨19355282195877596879647205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51614085855673591679059213 19355282195877596879647205)
                    ·
                      refine ⟨3629115411727049414933851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19355282195877596879647205 3629115411727049414933851)
                      ·
                        rfl

theorem cell23_7067677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7067677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067677 prefixEnd_7067677 := by exact prefixLift 7067677
  have htrace : WordTrace (prefixWord ++ tailWord_7067677) baseStart_7067677 baseEnd_7067677 := by
    simpa [prefixWord, tailWord_7067677, baseEnd_7067677] using wordTrace_append hprefix tailTrace_7067677
  have hstable : (prefixWord ++ tailWord_7067677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067677).length < 2 ^ (prefixWord ++ tailWord_7067677).sum := by decide
  have hdescent : baseEnd_7067677 < baseStart_7067677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067767 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_7067767 : Nat := 118140960795 + 7067767 * 2 ^ 59
def prefixEnd_7067767 : Nat := 4983230072969 + 3 ^ 40 * 7067767 * 2
def baseEnd_7067767 : Nat := 3629161624985954062808437

theorem tailTrace_7067767 : CollatzResearch.WordTrace tailWord_7067767 prefixEnd_7067767 3629161624985954062808437 := by
  unfold tailWord_7067767
  simp only [CollatzResearch.WordTrace]
  refine ⟨257782640185694712348281555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171855093457129808232187703 257782640185694712348281555)
  ·
    refine ⟨386673960278542068522422333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257782640185694712348281555 386673960278542068522422333)
    ·
      refine ⟨145002735104453275695908375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386673960278542068522422333 145002735104453275695908375)
      ·
        refine ⟨217504102656679913543862563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145002735104453275695908375 217504102656679913543862563)
        ·
          refine ⟨326256153985019870315793845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217504102656679913543862563 326256153985019870315793845)
          ·
            refine ⟨30586514436095612842105673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326256153985019870315793845 30586514436095612842105673)
            ·
              refine ⟨22939885827071709631579255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30586514436095612842105673 22939885827071709631579255)
              ·
                refine ⟨34409828740607564447368883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22939885827071709631579255 34409828740607564447368883)
                ·
                  refine ⟨51614743110911346671053325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34409828740607564447368883 51614743110911346671053325)
                  ·
                    refine ⟨19355528666591755001644997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51614743110911346671053325 19355528666591755001644997)
                    ·
                      refine ⟨3629161624985954062808437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19355528666591755001644997 3629161624985954062808437)
                      ·
                        rfl

theorem cell23_7067767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_7067767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067767 prefixEnd_7067767 := by exact prefixLift 7067767
  have htrace : WordTrace (prefixWord ++ tailWord_7067767) baseStart_7067767 baseEnd_7067767 := by
    simpa [prefixWord, tailWord_7067767, baseEnd_7067767] using wordTrace_append hprefix tailTrace_7067767
  have hstable : (prefixWord ++ tailWord_7067767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067767).length < 2 ^ (prefixWord ++ tailWord_7067767).sum := by decide
  have hdescent : baseEnd_7067767 < baseStart_7067767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067784 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7067784 : Nat := 118140960795 + 7067784 * 2 ^ 59
def prefixEnd_7067784 : Nat := 4983230072969 + 3 ^ 40 * 7067784 * 2
def baseEnd_7067784 : Nat := 3629170354157080496295859

theorem tailTrace_7067784 : CollatzResearch.WordTrace tailWord_7067784 prefixEnd_7067784 3629170354157080496295859 := by
  unfold tailWord_7067784
  simp only [CollatzResearch.WordTrace]
  refine ⟨128891630113316562125825203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171855506817755416167766937 128891630113316562125825203)
  ·
    refine ⟨193337445169974843188737805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128891630113316562125825203 193337445169974843188737805)
    ·
      refine ⟨72501541938740566195776677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193337445169974843188737805 72501541938740566195776677)
      ·
        refine ⟨13594039113513856161708127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72501541938740566195776677 13594039113513856161708127)
        ·
          refine ⟨20391058670270784242562191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594039113513856161708127 20391058670270784242562191)
          ·
            refine ⟨30586588005406176363843287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20391058670270784242562191 30586588005406176363843287)
            ·
              refine ⟨45879882008109264545764931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30586588005406176363843287 45879882008109264545764931)
              ·
                refine ⟨68819823012163896818647397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45879882008109264545764931 68819823012163896818647397)
                ·
                  refine ⟨12903716814780730653496387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68819823012163896818647397 12903716814780730653496387)
                  ·
                    refine ⟨19355575222171095980244581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12903716814780730653496387 19355575222171095980244581)
                    ·
                      refine ⟨3629170354157080496295859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19355575222171095980244581 3629170354157080496295859)
                      ·
                        rfl

theorem cell23_7067784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7067784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067784 prefixEnd_7067784 := by exact prefixLift 7067784
  have htrace : WordTrace (prefixWord ++ tailWord_7067784) baseStart_7067784 baseEnd_7067784 := by
    simpa [prefixWord, tailWord_7067784, baseEnd_7067784] using wordTrace_append hprefix tailTrace_7067784
  have hstable : (prefixWord ++ tailWord_7067784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067784).length < 2 ^ (prefixWord ++ tailWord_7067784).sum := by decide
  have hdescent : baseEnd_7067784 < baseStart_7067784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067804 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7067804 : Nat := 118140960795 + 7067804 * 2 ^ 59
def prefixEnd_7067804 : Nat := 4983230072969 + 3 ^ 40 * 7067804 * 2
def baseEnd_7067804 : Nat := 3629180623770170418045767

theorem tailTrace_7067804 : CollatzResearch.WordTrace tailWord_7067804 prefixEnd_7067804 3629180623770170418045767 := by
  unfold tailWord_7067804
  simp only [CollatzResearch.WordTrace]
  refine ⟨128891994843280333833689233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171855993124373778444918977 128891994843280333833689233)
  ·
    refine ⟨96668996132460250375266925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128891994843280333833689233 96668996132460250375266925)
    ·
      refine ⟨36250873549672593890725097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96668996132460250375266925 36250873549672593890725097)
      ·
        refine ⟨27188155162254445418043823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36250873549672593890725097 27188155162254445418043823)
        ·
          refine ⟨40782232743381668127065735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27188155162254445418043823 40782232743381668127065735)
          ·
            refine ⟨61173349115072502190598603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40782232743381668127065735 61173349115072502190598603)
            ·
              refine ⟨91760023672608753285897905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61173349115072502190598603 91760023672608753285897905)
              ·
                refine ⟨68820017754456564964423429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91760023672608753285897905 68820017754456564964423429)
                ·
                  refine ⟨12903753328960605930829393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68820017754456564964423429 12903753328960605930829393)
                  ·
                    refine ⟨9677814996720454448122045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12903753328960605930829393 9677814996720454448122045)
                    ·
                      refine ⟨3629180623770170418045767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9677814996720454448122045 3629180623770170418045767)
                      ·
                        rfl

theorem cell23_7067804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7067804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067804 prefixEnd_7067804 := by exact prefixLift 7067804
  have htrace : WordTrace (prefixWord ++ tailWord_7067804) baseStart_7067804 baseEnd_7067804 := by
    simpa [prefixWord, tailWord_7067804, baseEnd_7067804] using wordTrace_append hprefix tailTrace_7067804
  have hstable : (prefixWord ++ tailWord_7067804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067804).length < 2 ^ (prefixWord ++ tailWord_7067804).sum := by decide
  have hdescent : baseEnd_7067804 < baseStart_7067804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067818 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7067818 : Nat := 118140960795 + 7067818 * 2 ^ 59
def prefixEnd_7067818 : Nat := 4983230072969 + 3 ^ 40 * 7067818 * 2
def baseEnd_7067818 : Nat := 3629187812499333363270703

theorem tailTrace_7067818 : CollatzResearch.WordTrace tailWord_7067818 prefixEnd_7067818 3629187812499333363270703 := by
  unfold tailWord_7067818
  simp only [CollatzResearch.WordTrace]
  refine ⟨64446125077127487014597027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171856333539006632038925405 64446125077127487014597027)
  ·
    refine ⟨96669187615691230521895541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64446125077127487014597027 96669187615691230521895541)
    ·
      refine ⟨9062736338971052861427707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96669187615691230521895541 9062736338971052861427707)
      ·
        refine ⟨13594104508456579292141561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062736338971052861427707 13594104508456579292141561)
        ·
          refine ⟨10195578381342434469106171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13594104508456579292141561 10195578381342434469106171)
          ·
            refine ⟨15293367572013651703659257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10195578381342434469106171 15293367572013651703659257)
            ·
              refine ⟨11470025679010238777744443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15293367572013651703659257 11470025679010238777744443)
              ·
                refine ⟨17205038518515358166616665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11470025679010238777744443 17205038518515358166616665)
                ·
                  refine ⟨12903778888886518624962499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17205038518515358166616665 12903778888886518624962499)
                  ·
                    refine ⟨19355668333329777937443749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12903778888886518624962499 19355668333329777937443749)
                    ·
                      refine ⟨3629187812499333363270703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19355668333329777937443749 3629187812499333363270703)
                      ·
                        rfl

theorem cell23_7067818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7067818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067818 prefixEnd_7067818 := by exact prefixLift 7067818
  have htrace : WordTrace (prefixWord ++ tailWord_7067818) baseStart_7067818 baseEnd_7067818 := by
    simpa [prefixWord, tailWord_7067818, baseEnd_7067818] using wordTrace_append hprefix tailTrace_7067818
  have hstable : (prefixWord ++ tailWord_7067818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067818).length < 2 ^ (prefixWord ++ tailWord_7067818).sum := by decide
  have hdescent : baseEnd_7067818 < baseStart_7067818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067821 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7067821 : Nat := 118140960795 + 7067821 * 2 ^ 59
def prefixEnd_7067821 : Nat := 4983230072969 + 3 ^ 40 * 7067821 * 2
def baseEnd_7067821 : Nat := 3629189352941296851533189

theorem tailTrace_7067821 : CollatzResearch.WordTrace tailWord_7067821 prefixEnd_7067821 3629189352941296851533189 := by
  unfold tailWord_7067821
  simp only [CollatzResearch.WordTrace]
  refine ⟨257784609727499079570747317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171856406484999386380498211 257784609727499079570747317)
  ·
    refine ⟨24167307161953038709757561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257784609727499079570747317 24167307161953038709757561)
    ·
      refine ⟨18125480371464779032318171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24167307161953038709757561 18125480371464779032318171)
      ·
        refine ⟨27188220557197168548477257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18125480371464779032318171 27188220557197168548477257)
        ·
          refine ⟨20391165417897876411357943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27188220557197168548477257 20391165417897876411357943)
          ·
            refine ⟨30586748126846814617036915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20391165417897876411357943 30586748126846814617036915)
            ·
              refine ⟨45880122190270221925555373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30586748126846814617036915 45880122190270221925555373)
              ·
                refine ⟨17205045821351333222083265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45880122190270221925555373 17205045821351333222083265)
                ·
                  refine ⟨12903784366013499916562449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17205045821351333222083265 12903784366013499916562449)
                  ·
                    refine ⟨9677838274510124937421837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12903784366013499916562449 9677838274510124937421837)
                    ·
                      refine ⟨3629189352941296851533189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9677838274510124937421837 3629189352941296851533189)
                      ·
                        rfl

theorem cell23_7067821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7067821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067821 prefixEnd_7067821 := by exact prefixLift 7067821
  have htrace : WordTrace (prefixWord ++ tailWord_7067821) baseStart_7067821 baseEnd_7067821 := by
    simpa [prefixWord, tailWord_7067821, baseEnd_7067821] using wordTrace_append hprefix tailTrace_7067821
  have hstable : (prefixWord ++ tailWord_7067821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067821).length < 2 ^ (prefixWord ++ tailWord_7067821).sum := by decide
  have hdescent : baseEnd_7067821 < baseStart_7067821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067854 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_7067854 : Nat := 118140960795 + 7067854 * 2 ^ 59
def prefixEnd_7067854 : Nat := 4983230072969 + 3 ^ 40 * 7067854 * 2
def baseEnd_7067854 : Nat := 1209735432600965074140179

theorem tailTrace_7067854 : CollatzResearch.WordTrace tailWord_7067854 prefixEnd_7067854 1209735432600965074140179 := by
  unfold tailWord_7067854
  simp only [CollatzResearch.WordTrace]
  refine ⟨32223226667047440775837327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171857208890919684137799077 32223226667047440775837327)
  ·
    refine ⟨48334840000571161163755991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32223226667047440775837327 48334840000571161163755991)
    ·
      refine ⟨72502260000856741745633987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48334840000571161163755991 72502260000856741745633987)
      ·
        refine ⟨108753390001285112618450981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72502260000856741745633987 108753390001285112618450981)
        ·
          refine ⟨20391260625240958615959559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108753390001285112618450981 20391260625240958615959559)
          ·
            refine ⟨30586890937861437923939339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20391260625240958615959559 30586890937861437923939339)
            ·
              refine ⟨45880336406792156885909009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30586890937861437923939339 45880336406792156885909009)
              ·
                refine ⟨34410252305094117664431757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45880336406792156885909009 34410252305094117664431757)
                ·
                  refine ⟨12903844614410294124161909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34410252305094117664431757 12903844614410294124161909)
                  ·
                    refine ⟨1209735432600965074140179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12903844614410294124161909 1209735432600965074140179)
                    ·
                      rfl

theorem cell23_7067854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_7067854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067854 prefixEnd_7067854 := by exact prefixLift 7067854
  have htrace : WordTrace (prefixWord ++ tailWord_7067854) baseStart_7067854 baseEnd_7067854 := by
    simpa [prefixWord, tailWord_7067854, baseEnd_7067854] using wordTrace_append hprefix tailTrace_7067854
  have hstable : (prefixWord ++ tailWord_7067854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067854).length < 2 ^ (prefixWord ++ tailWord_7067854).sum := by decide
  have hdescent : baseEnd_7067854 < baseStart_7067854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067867 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 1, 6]
def baseStart_7067867 : Nat := 118140960795 + 7067867 * 2 ^ 59
def prefixEnd_7067867 : Nat := 4983230072969 + 3 ^ 40 * 7067867 * 2
def baseEnd_7067867 : Nat := 1209737657683801223852659

theorem tailTrace_7067867 : CollatzResearch.WordTrace tailWord_7067867 prefixEnd_7067867 1209737657683801223852659 := by
  unfold tailWord_7067867
  simp only [CollatzResearch.WordTrace]
  refine ⟨257786287485332429426921855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171857524990221619617947903 257786287485332429426921855)
  ·
    refine ⟨386679431227998644140382783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257786287485332429426921855 386679431227998644140382783)
    ·
      refine ⟨580019146841997966210574175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386679431227998644140382783 580019146841997966210574175)
      ·
        refine ⟨870028720262996949315861263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580019146841997966210574175 870028720262996949315861263)
        ·
          refine ⟨1305043080394495423973791895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870028720262996949315861263 1305043080394495423973791895)
          ·
            refine ⟨1957564620591743135960687843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305043080394495423973791895 1957564620591743135960687843)
            ·
              refine ⟨2936346930887614703941031765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957564620591743135960687843 2936346930887614703941031765)
              ·
                refine ⟨17205157798169617405904483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2936346930887614703941031765 17205157798169617405904483)
                ·
                  refine ⟨25807736697254426108856725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17205157798169617405904483 25807736697254426108856725)
                  ·
                    refine ⟨1209737657683801223852659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25807736697254426108856725 1209737657683801223852659)
                    ·
                      rfl

theorem cell23_7067867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 6].length) (baseStart_7067867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067867 prefixEnd_7067867 := by exact prefixLift 7067867
  have htrace : WordTrace (prefixWord ++ tailWord_7067867) baseStart_7067867 baseEnd_7067867 := by
    simpa [prefixWord, tailWord_7067867, baseEnd_7067867] using wordTrace_append hprefix tailTrace_7067867
  have hstable : (prefixWord ++ tailWord_7067867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067867).length < 2 ^ (prefixWord ++ tailWord_7067867).sum := by decide
  have hdescent : baseEnd_7067867 < baseStart_7067867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067884 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_7067884 : Nat := 118140960795 + 7067884 * 2 ^ 59
def prefixEnd_7067884 : Nat := 4983230072969 + 3 ^ 40 * 7067884 * 2
def baseEnd_7067884 : Nat := 1209740567407510035015133

theorem tailTrace_7067884 : CollatzResearch.WordTrace tailWord_7067884 prefixEnd_7067884 1209740567407510035015133 := by
  unfold tailWord_7067884
  simp only [CollatzResearch.WordTrace]
  refine ⟨128893453763135420665145353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171857938350847227553527137 128893453763135420665145353)
  ·
    refine ⟨96670090322351565498859015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128893453763135420665145353 96670090322351565498859015)
    ·
      refine ⟨145005135483527348248288523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96670090322351565498859015 145005135483527348248288523)
      ·
        refine ⟨217507703225291022372432785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145005135483527348248288523 217507703225291022372432785)
        ·
          refine ⟨163130777418968266779324589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217507703225291022372432785 163130777418968266779324589)
          ·
            refine ⟨61174041532113100042246721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163130777418968266779324589 61174041532113100042246721)
            ·
              refine ⟨45880531149084825031685041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61174041532113100042246721 45880531149084825031685041)
              ·
                refine ⟨34410398361813618773763781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45880531149084825031685041 34410398361813618773763781)
                ·
                  refine ⟨6451949692840053520080709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34410398361813618773763781 6451949692840053520080709)
                  ·
                    refine ⟨1209740567407510035015133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6451949692840053520080709 1209740567407510035015133)
                    ·
                      rfl

theorem cell23_7067884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_7067884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067884 prefixEnd_7067884 := by exact prefixLift 7067884
  have htrace : WordTrace (prefixWord ++ tailWord_7067884) baseStart_7067884 baseEnd_7067884 := by
    simpa [prefixWord, tailWord_7067884, baseEnd_7067884] using wordTrace_append hprefix tailTrace_7067884
  have hstable : (prefixWord ++ tailWord_7067884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067884).length < 2 ^ (prefixWord ++ tailWord_7067884).sum := by decide
  have hdescent : baseEnd_7067884 < baseStart_7067884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067891 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 5, 2, 2]
def baseStart_7067891 : Nat := 118140960795 + 7067891 * 2 ^ 59
def prefixEnd_7067891 : Nat := 4983230072969 + 3 ^ 40 * 7067891 * 2
def baseEnd_7067891 : Nat := 3629225296587111577657867

theorem tailTrace_7067891 : CollatzResearch.WordTrace tailWord_7067891 prefixEnd_7067891 3629225296587111577657867 := by
  unfold tailWord_7067891
  simp only [CollatzResearch.WordTrace]
  refine ⟨257787162837245481525795527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171858108558163654350530351 257787162837245481525795527)
  ·
    refine ⟨386680744255868222288693291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257787162837245481525795527 386680744255868222288693291)
    ·
      refine ⟨580021116383802333433039937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386680744255868222288693291 580021116383802333433039937)
      ·
        refine ⟨435015837287851750074779953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580021116383802333433039937 435015837287851750074779953)
        ·
          refine ⟨326261877965888812556084965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435015837287851750074779953 326261877965888812556084965)
          ·
            refine ⟨61174102118604152354265931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326261877965888812556084965 61174102118604152354265931)
            ·
              refine ⟨91761153177906228531398897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61174102118604152354265931 91761153177906228531398897)
              ·
                refine ⟨68820864883429671398549173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91761153177906228531398897 68820864883429671398549173)
                ·
                  refine ⟨6451956082821531693613985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68820864883429671398549173 6451956082821531693613985)
                  ·
                    refine ⟨4838967062116148770210489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6451956082821531693613985 4838967062116148770210489)
                    ·
                      refine ⟨3629225296587111577657867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4838967062116148770210489 3629225296587111577657867)
                      ·
                        rfl

theorem cell23_7067891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 2, 2].length) (baseStart_7067891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067891 prefixEnd_7067891 := by exact prefixLift 7067891
  have htrace : WordTrace (prefixWord ++ tailWord_7067891) baseStart_7067891 baseEnd_7067891 := by
    simpa [prefixWord, tailWord_7067891, baseEnd_7067891] using wordTrace_append hprefix tailTrace_7067891
  have hstable : (prefixWord ++ tailWord_7067891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067891).length < 2 ^ (prefixWord ++ tailWord_7067891).sum := by decide
  have hdescent : baseEnd_7067891 < baseStart_7067891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067918 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_7067918 : Nat := 118140960795 + 7067918 * 2 ^ 59
def prefixEnd_7067918 : Nat := 4983230072969 + 3 ^ 40 * 7067918 * 2
def baseEnd_7067918 : Nat := 1209746386854927657340081

theorem tailTrace_7067918 : CollatzResearch.WordTrace tailWord_7067918 prefixEnd_7067918 1209746386854927657340081 := by
  unfold tailWord_7067918
  simp only [CollatzResearch.WordTrace]
  refine ⟨32223518451018458142128551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171858765072098443424685605 32223518451018458142128551)
  ·
    refine ⟨48335277676527687213192827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32223518451018458142128551 48335277676527687213192827)
    ·
      refine ⟨72502916514791530819789241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48335277676527687213192827 72502916514791530819789241)
      ·
        refine ⟨54377187386093648114841931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72502916514791530819789241 54377187386093648114841931)
        ·
          refine ⟨81565781079140472172262897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54377187386093648114841931 81565781079140472172262897)
          ·
            refine ⟨61174335809355354129197173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81565781079140472172262897 61174335809355354129197173)
            ·
              refine ⟨5735093982127064449612235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61174335809355354129197173 5735093982127064449612235)
              ·
                refine ⟨8602640973190596674418353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735093982127064449612235 8602640973190596674418353)
                ·
                  refine ⟨6451980729892947505813765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8602640973190596674418353 6451980729892947505813765)
                  ·
                    refine ⟨1209746386854927657340081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6451980729892947505813765 1209746386854927657340081)
                    ·
                      rfl

theorem cell23_7067918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_7067918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067918 prefixEnd_7067918 := by exact prefixLift 7067918
  have htrace : WordTrace (prefixWord ++ tailWord_7067918) baseStart_7067918 baseEnd_7067918 := by
    simpa [prefixWord, tailWord_7067918, baseEnd_7067918] using wordTrace_append hprefix tailTrace_7067918
  have hstable : (prefixWord ++ tailWord_7067918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067918).length < 2 ^ (prefixWord ++ tailWord_7067918).sum := by decide
  have hdescent : baseEnd_7067918 < baseStart_7067918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067921 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_7067921 : Nat := 118140960795 + 7067921 * 2 ^ 59
def prefixEnd_7067921 : Nat := 4983230072969 + 3 ^ 40 * 7067921 * 2
def baseEnd_7067921 : Nat := 3629240701006746460282729

theorem tailTrace_7067921 : CollatzResearch.WordTrace tailWord_7067921 prefixEnd_7067921 3629240701006746460282729 := by
  unfold tailWord_7067921
  simp only [CollatzResearch.WordTrace]
  refine ⟨257788257027136796649387617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171858838018091197766258411 257788257027136796649387617)
  ·
    refine ⟨193341192770352597487040713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257788257027136796649387617 193341192770352597487040713)
    ·
      refine ⟨145005894577764448115280535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193341192770352597487040713 145005894577764448115280535)
      ·
        refine ⟨217508841866646672172920803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145005894577764448115280535 217508841866646672172920803)
        ·
          refine ⟨326263262799970008259381205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217508841866646672172920803 326263262799970008259381205)
          ·
            refine ⟨7646795221874297068579247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 326263262799970008259381205 7646795221874297068579247)
            ·
              refine ⟨11470192832811445602868871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646795221874297068579247 11470192832811445602868871)
              ·
                refine ⟨17205289249217168404303307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11470192832811445602868871 17205289249217168404303307)
                ·
                  refine ⟨25807933873825752606454961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17205289249217168404303307 25807933873825752606454961)
                  ·
                    refine ⟨19355950405369314454841221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25807933873825752606454961 19355950405369314454841221)
                    ·
                      refine ⟨3629240701006746460282729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19355950405369314454841221 3629240701006746460282729)
                      ·
                        rfl

theorem cell23_7067921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_7067921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067921 prefixEnd_7067921 := by exact prefixLift 7067921
  have htrace : WordTrace (prefixWord ++ tailWord_7067921) baseStart_7067921 baseEnd_7067921 := by
    simpa [prefixWord, tailWord_7067921, baseEnd_7067921] using wordTrace_append hprefix tailTrace_7067921
  have hstable : (prefixWord ++ tailWord_7067921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067921).length < 2 ^ (prefixWord ++ tailWord_7067921).sum := by decide
  have hdescent : baseEnd_7067921 < baseStart_7067921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067964 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_7067964 : Nat := 118140960795 + 7067964 * 2 ^ 59
def prefixEnd_7067964 : Nat := 4983230072969 + 3 ^ 40 * 7067964 * 2
def baseEnd_7067964 : Nat := 3629262780674889792045031

theorem tailTrace_7067964 : CollatzResearch.WordTrace tailWord_7067964 prefixEnd_7067964 3629262780674889792045031 := by
  unfold tailWord_7067964
  simp only [CollatzResearch.WordTrace]
  refine ⟨128894912682990507496601473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171859883577320676662135297 128894912682990507496601473)
  ·
    refine ⟨96671184512242880622451105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128894912682990507496601473 96671184512242880622451105)
    ·
      refine ⟨72503388384182160466838329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96671184512242880622451105 72503388384182160466838329)
      ·
        refine ⟨54377541288136620350128747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72503388384182160466838329 54377541288136620350128747)
        ·
          refine ⟨81566311932204930525193121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54377541288136620350128747 81566311932204930525193121)
          ·
            refine ⟨61174733949153697893894841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81566311932204930525193121 61174733949153697893894841)
            ·
              refine ⟨45881050461865273420421131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61174733949153697893894841 45881050461865273420421131)
              ·
                refine ⟨68821575692797910130631697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45881050461865273420421131 68821575692797910130631697)
                ·
                  refine ⟨51616181769598432597973773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68821575692797910130631697 51616181769598432597973773)
                  ·
                    refine ⟨19356068163599412224240165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51616181769598432597973773 19356068163599412224240165)
                    ·
                      refine ⟨3629262780674889792045031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19356068163599412224240165 3629262780674889792045031)
                      ·
                        rfl

theorem cell23_7067964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_7067964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067964 prefixEnd_7067964 := by exact prefixLift 7067964
  have htrace : WordTrace (prefixWord ++ tailWord_7067964) baseStart_7067964 baseEnd_7067964 := by
    simpa [prefixWord, tailWord_7067964, baseEnd_7067964] using wordTrace_append hprefix tailTrace_7067964
  have hstable : (prefixWord ++ tailWord_7067964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067964).length < 2 ^ (prefixWord ++ tailWord_7067964).sum := by decide
  have hdescent : baseEnd_7067964 < baseStart_7067964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067984 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_7067984 : Nat := 118140960795 + 7067984 * 2 ^ 59
def prefixEnd_7067984 : Nat := 4983230072969 + 3 ^ 40 * 7067984 * 2
def baseEnd_7067984 : Nat := 3629273050287979713794939

theorem tailTrace_7067984 : CollatzResearch.WordTrace tailWord_7067984 prefixEnd_7067984 3629273050287979713794939 := by
  unfold tailWord_7067984
  simp only [CollatzResearch.WordTrace]
  refine ⟨128895277412954279204465503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171860369883939038939287337 128895277412954279204465503)
  ·
    refine ⟨193342916119431418806698255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128895277412954279204465503 193342916119431418806698255)
    ·
      refine ⟨290014374179147128210047383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193342916119431418806698255 290014374179147128210047383)
      ·
        refine ⟨435021561268720692315071075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290014374179147128210047383 435021561268720692315071075)
        ·
          refine ⟨652532341903081038472606613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435021561268720692315071075 652532341903081038472606613)
          ·
            refine ⟨30587453526706923678403435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 652532341903081038472606613 30587453526706923678403435)
            ·
              refine ⟨45881180290060385517605153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30587453526706923678403435 45881180290060385517605153)
              ·
                refine ⟨34410885217545289138203865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45881180290060385517605153 34410885217545289138203865)
                ·
                  refine ⟨25808163913158966853652899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34410885217545289138203865 25808163913158966853652899)
                  ·
                    refine ⟨38712245869738450280479349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25808163913158966853652899 38712245869738450280479349)
                    ·
                      refine ⟨3629273050287979713794939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38712245869738450280479349 3629273050287979713794939)
                      ·
                        rfl

theorem cell23_7067984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_7067984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067984 prefixEnd_7067984 := by exact prefixLift 7067984
  have htrace : WordTrace (prefixWord ++ tailWord_7067984) baseStart_7067984 baseEnd_7067984 := by
    simpa [prefixWord, tailWord_7067984, baseEnd_7067984] using wordTrace_append hprefix tailTrace_7067984
  have hstable : (prefixWord ++ tailWord_7067984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067984).length < 2 ^ (prefixWord ++ tailWord_7067984).sum := by decide
  have hdescent : baseEnd_7067984 < baseStart_7067984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067985 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 1, 3, 2]
def baseStart_7067985 : Nat := 118140960795 + 7067985 * 2 ^ 59
def prefixEnd_7067985 : Nat := 4983230072969 + 3 ^ 40 * 7067985 * 2
def baseEnd_7067985 : Nat := 3629273563768634209882435

theorem tailTrace_7067985 : CollatzResearch.WordTrace tailWord_7067985 prefixEnd_7067985 3629273563768634209882435 := by
  unfold tailWord_7067985
  simp only [CollatzResearch.WordTrace]
  refine ⟨257790591298904935579717409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171860394199269957053144939 257790591298904935579717409)
  ·
    refine ⟨193342943474178701684788057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257790591298904935579717409 193342943474178701684788057)
    ·
      refine ⟨145007207605634026263591043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193342943474178701684788057 145007207605634026263591043)
      ·
        refine ⟨217510811408451039395386565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145007207605634026263591043 217510811408451039395386565)
        ·
          refine ⟨40783277139084569886634981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217510811408451039395386565 40783277139084569886634981)
          ·
            refine ⟨7646864463578356853744059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40783277139084569886634981 7646864463578356853744059)
            ·
              refine ⟨11470296695367535280616089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646864463578356853744059 11470296695367535280616089)
              ·
                refine ⟨8602722521525651460462067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11470296695367535280616089 8602722521525651460462067)
                ·
                  refine ⟨12904083782288477190693101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602722521525651460462067 12904083782288477190693101)
                  ·
                    refine ⟨4839031418358178946509913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12904083782288477190693101 4839031418358178946509913)
                    ·
                      refine ⟨3629273563768634209882435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839031418358178946509913 3629273563768634209882435)
                      ·
                        rfl

theorem cell23_7067985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_7067985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067985 prefixEnd_7067985 := by exact prefixLift 7067985
  have htrace : WordTrace (prefixWord ++ tailWord_7067985) baseStart_7067985 baseEnd_7067985 := by
    simpa [prefixWord, tailWord_7067985, baseEnd_7067985] using wordTrace_append hprefix tailTrace_7067985
  have hstable : (prefixWord ++ tailWord_7067985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067985).length < 2 ^ (prefixWord ++ tailWord_7067985).sum := by decide
  have hdescent : baseEnd_7067985 < baseStart_7067985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7067994 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_7067994 : Nat := 118140960795 + 7067994 * 2 ^ 59
def prefixEnd_7067994 : Nat := 4983230072969 + 3 ^ 40 * 7067994 * 2
def baseEnd_7067994 : Nat := 3629278185094524674669893

theorem tailTrace_7067994 : CollatzResearch.WordTrace tailWord_7067994 prefixEnd_7067994 3629278185094524674669893 := by
  unfold tailWord_7067994
  simp only [CollatzResearch.WordTrace]
  refine ⟨64447729888968082529198759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171860613037248220077863357 64447729888968082529198759)
  ·
    refine ⟨96671594833452123793798139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64447729888968082529198759 96671594833452123793798139)
    ·
      refine ⟨145007392250178185690697209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96671594833452123793798139 145007392250178185690697209)
      ·
        refine ⟨108755544187633639268022907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145007392250178185690697209 108755544187633639268022907)
        ·
          refine ⟨163133316281450458902034361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108755544187633639268022907 163133316281450458902034361)
          ·
            refine ⟨122349987211087844176525771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163133316281450458902034361 122349987211087844176525771)
            ·
              refine ⟨183524980816631766264788657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122349987211087844176525771 183524980816631766264788657)
              ·
                refine ⟨137643735612473824698591493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183524980816631766264788657 137643735612473824698591493)
                ·
                  refine ⟨25808200427338842130985905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137643735612473824698591493 25808200427338842130985905)
                  ·
                    refine ⟨19356150320504131598239429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25808200427338842130985905 19356150320504131598239429)
                    ·
                      refine ⟨3629278185094524674669893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19356150320504131598239429 3629278185094524674669893)
                      ·
                        rfl

theorem cell23_7067994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_7067994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7067994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7067994 prefixEnd_7067994 := by exact prefixLift 7067994
  have htrace : WordTrace (prefixWord ++ tailWord_7067994) baseStart_7067994 baseEnd_7067994 := by
    simpa [prefixWord, tailWord_7067994, baseEnd_7067994] using wordTrace_append hprefix tailTrace_7067994
  have hstable : (prefixWord ++ tailWord_7067994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7067994).length < 2 ^ (prefixWord ++ tailWord_7067994).sum := by decide
  have hdescent : baseEnd_7067994 < baseStart_7067994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7067994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068002 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7068002 : Nat := 118140960795 + 7068002 * 2 ^ 59
def prefixEnd_7068002 : Nat := 4983230072969 + 3 ^ 40 * 7068002 * 2
def baseEnd_7068002 : Nat := 3629282292939760643369857

theorem tailTrace_7068002 : CollatzResearch.WordTrace tailWord_7068002 prefixEnd_7068002 3629282292939760643369857 := by
  unfold tailWord_7068002
  simp only [CollatzResearch.WordTrace]
  refine ⟨64447802834960836870771565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171860807559895564988724173 64447802834960836870771565)
  ·
    refine ⟨24167926063110313826539337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64447802834960836870771565 24167926063110313826539337)
    ·
      refine ⟨18125944547332735369904503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24167926063110313826539337 18125944547332735369904503)
      ·
        refine ⟨27188916820999103054856755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18125944547332735369904503 27188916820999103054856755)
        ·
          refine ⟨40783375231498654582285133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27188916820999103054856755 40783375231498654582285133)
          ·
            refine ⟨15293765711811995468356925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40783375231498654582285133 15293765711811995468356925)
            ·
              refine ⟨5735162141929498300633847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15293765711811995468356925 5735162141929498300633847)
              ·
                refine ⟨8602743212894247450950771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735162141929498300633847 8602743212894247450950771)
                ·
                  refine ⟨12904114819341371176426157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602743212894247450950771 12904114819341371176426157)
                  ·
                    refine ⟨4839043057253014191159809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12904114819341371176426157 4839043057253014191159809)
                    ·
                      refine ⟨3629282292939760643369857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839043057253014191159809 3629282292939760643369857)
                      ·
                        rfl

theorem cell23_7068002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7068002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068002 prefixEnd_7068002 := by exact prefixLift 7068002
  have htrace : WordTrace (prefixWord ++ tailWord_7068002) baseStart_7068002 baseEnd_7068002 := by
    simpa [prefixWord, tailWord_7068002, baseEnd_7068002] using wordTrace_append hprefix tailTrace_7068002
  have hstable : (prefixWord ++ tailWord_7068002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068002).length < 2 ^ (prefixWord ++ tailWord_7068002).sum := by decide
  have hdescent : baseEnd_7068002 < baseStart_7068002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068171 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 3, 6]
def baseStart_7068171 : Nat := 118140960795 + 7068171 * 2 ^ 59
def prefixEnd_7068171 : Nat := 4983230072969 + 3 ^ 40 * 7068171 * 2
def baseEnd_7068171 : Nat := 1209789690390123494052193

theorem tailTrace_7068171 : CollatzResearch.WordTrace tailWord_7068171 prefixEnd_7068171 1209789690390123494052193 := by
  unfold tailWord_7068171
  simp only [CollatzResearch.WordTrace]
  refine ⟨257797375276231089345988367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171864916850820726230658911 257797375276231089345988367)
  ·
    refine ⟨386696062914346634018982551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257797375276231089345988367 386696062914346634018982551)
    ·
      refine ⟨580044094371519951028473827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386696062914346634018982551 580044094371519951028473827)
      ·
        refine ⟨870066141557279926542710741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580044094371519951028473827 870066141557279926542710741)
        ·
          refine ⟨20392175192748748278344783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 870066141557279926542710741 20392175192748748278344783)
          ·
            refine ⟨30588262789123122417517175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20392175192748748278344783 30588262789123122417517175)
            ·
              refine ⟨45882394183684683626275763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30588262789123122417517175 45882394183684683626275763)
              ·
                refine ⟨68823591275527025439413645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45882394183684683626275763 68823591275527025439413645)
                ·
                  refine ⟨25808846728322634539780117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68823591275527025439413645 25808846728322634539780117)
                  ·
                    refine ⟨1209789690390123494052193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25808846728322634539780117 1209789690390123494052193)
                    ·
                      rfl

theorem cell23_7068171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 6].length) (baseStart_7068171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068171 prefixEnd_7068171 := by exact prefixLift 7068171
  have htrace : WordTrace (prefixWord ++ tailWord_7068171) baseStart_7068171 baseEnd_7068171 := by
    simpa [prefixWord, tailWord_7068171, baseEnd_7068171] using wordTrace_append hprefix tailTrace_7068171
  have hstable : (prefixWord ++ tailWord_7068171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068171).length < 2 ^ (prefixWord ++ tailWord_7068171).sum := by decide
  have hdescent : baseEnd_7068171 < baseStart_7068171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068189 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_7068189 : Nat := 118140960795 + 7068189 * 2 ^ 59
def prefixEnd_7068189 : Nat := 4983230072969 + 3 ^ 40 * 7068189 * 2
def baseEnd_7068189 : Nat := 3629378313822151411731497

theorem tailTrace_7068189 : CollatzResearch.WordTrace tailWord_7068189 prefixEnd_7068189 3629378313822151411731497 := by
  unfold tailWord_7068189
  simp only [CollatzResearch.WordTrace]
  refine ⟨257798031790165878420143621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171865354526777252280095747 257798031790165878420143621)
  ·
    refine ⟨48337130960656102203776929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257798031790165878420143621 48337130960656102203776929)
    ·
      refine ⟨36252848220492076652832697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48337130960656102203776929 36252848220492076652832697)
      ·
        refine ⟨27189636165369057489624523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36252848220492076652832697 27189636165369057489624523)
        ·
          refine ⟨40784454248053586234436785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27189636165369057489624523 40784454248053586234436785)
          ·
            refine ⟨30588340686040189675827589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40784454248053586234436785 30588340686040189675827589)
            ·
              refine ⟨5735313878632535564217673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30588340686040189675827589 5735313878632535564217673)
              ·
                refine ⟨4301485408974401673163255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735313878632535564217673 4301485408974401673163255)
                ·
                  refine ⟨6452228113461602509744883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301485408974401673163255 6452228113461602509744883)
                  ·
                    refine ⟨9678342170192403764617325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6452228113461602509744883 9678342170192403764617325)
                    ·
                      refine ⟨3629378313822151411731497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9678342170192403764617325 3629378313822151411731497)
                      ·
                        rfl

theorem cell23_7068189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_7068189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068189 prefixEnd_7068189 := by exact prefixLift 7068189
  have htrace : WordTrace (prefixWord ++ tailWord_7068189) baseStart_7068189 baseEnd_7068189 := by
    simpa [prefixWord, tailWord_7068189, baseEnd_7068189] using wordTrace_append hprefix tailTrace_7068189
  have hstable : (prefixWord ++ tailWord_7068189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068189).length < 2 ^ (prefixWord ++ tailWord_7068189).sum := by decide
  have hdescent : baseEnd_7068189 < baseStart_7068189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068191 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_7068191 : Nat := 118140960795 + 7068191 * 2 ^ 59
def prefixEnd_7068191 : Nat := 4983230072969 + 3 ^ 40 * 7068191 * 2
def baseEnd_7068191 : Nat := 3629379340783460403906487

theorem tailTrace_7068191 : CollatzResearch.WordTrace tailWord_7068191 prefixEnd_7068191 3629379340783460403906487 := by
  unfold tailWord_7068191
  simp only [CollatzResearch.WordTrace]
  refine ⟨257798104736158632761716427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171865403157439088507810951 257798104736158632761716427)
  ·
    refine ⟨386697157104237949142574641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257798104736158632761716427 386697157104237949142574641)
    ·
      refine ⟨290022867828178461856930981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386697157104237949142574641 290022867828178461856930981)
      ·
        refine ⟨54379287717783461598174559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290022867828178461856930981 54379287717783461598174559)
        ·
          refine ⟨81568931576675192397261839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54379287717783461598174559 81568931576675192397261839)
          ·
            refine ⟨122353397365012788595892759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81568931576675192397261839 122353397365012788595892759)
            ·
              refine ⟨183530096047519182893839139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122353397365012788595892759 183530096047519182893839139)
              ·
                refine ⟨275295144071278774340758709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183530096047519182893839139 275295144071278774340758709)
                ·
                  refine ⟨25808919756682385094446129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275295144071278774340758709 25808919756682385094446129)
                  ·
                    refine ⟨19356689817511788820834597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25808919756682385094446129 19356689817511788820834597)
                    ·
                      refine ⟨3629379340783460403906487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19356689817511788820834597 3629379340783460403906487)
                      ·
                        rfl

theorem cell23_7068191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_7068191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068191 prefixEnd_7068191 := by exact prefixLift 7068191
  have htrace : WordTrace (prefixWord ++ tailWord_7068191) baseStart_7068191 baseEnd_7068191 := by
    simpa [prefixWord, tailWord_7068191, baseEnd_7068191] using wordTrace_append hprefix tailTrace_7068191
  have hstable : (prefixWord ++ tailWord_7068191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068191).length < 2 ^ (prefixWord ++ tailWord_7068191).sum := by decide
  have hdescent : baseEnd_7068191 < baseStart_7068191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068218 : List Nat := [3, 1, 1, 1, 3, 4, 3, 7]
def baseStart_7068218 : Nat := 118140960795 + 7068218 * 2 ^ 59
def prefixEnd_7068218 : Nat := 4983230072969 + 3 ^ 40 * 7068218 * 2
def baseEnd_7068218 : Nat := 134421970546708585121069

theorem tailTrace_7068218 : CollatzResearch.WordTrace tailWord_7068218 prefixEnd_7068218 134421970546708585121069 := by
  unfold tailWord_7068218
  simp only [CollatzResearch.WordTrace]
  refine ⟨64449772376765204093237327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171866059671373877581966205 64449772376765204093237327)
  ·
    refine ⟨96674658565147806139855991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64449772376765204093237327 96674658565147806139855991)
    ·
      refine ⟨145011987847721709209783987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96674658565147806139855991 145011987847721709209783987)
      ·
        refine ⟨217517981771582563814675981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145011987847721709209783987 217517981771582563814675981)
        ·
          refine ⟨81569243164343461430503493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217517981771582563814675981 81569243164343461430503493)
          ·
            refine ⟨15294233093314399018219405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81569243164343461430503493 15294233093314399018219405)
            ·
              refine ⟨5735337409992899631832277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15294233093314399018219405 5735337409992899631832277)
              ·
                refine ⟨134421970546708585121069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5735337409992899631832277 134421970546708585121069)
                ·
                  rfl

theorem cell23_7068218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_7068218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068218 prefixEnd_7068218 := by exact prefixLift 7068218
  have htrace : WordTrace (prefixWord ++ tailWord_7068218) baseStart_7068218 baseEnd_7068218 := by
    simpa [prefixWord, tailWord_7068218, baseEnd_7068218] using wordTrace_append hprefix tailTrace_7068218
  have hstable : (prefixWord ++ tailWord_7068218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068218).length < 2 ^ (prefixWord ++ tailWord_7068218).sum := by decide
  have hdescent : baseEnd_7068218 < baseStart_7068218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068229 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 1, 2, 2]
def baseStart_7068229 : Nat := 118140960795 + 7068229 * 2 ^ 59
def prefixEnd_7068229 : Nat := 4983230072969 + 3 ^ 40 * 7068229 * 2
def baseEnd_7068229 : Nat := 3629398853048331255231313

theorem tailTrace_7068229 : CollatzResearch.WordTrace tailWord_7068229 prefixEnd_7068229 3629398853048331255231313 := by
  unfold tailWord_7068229
  simp only [CollatzResearch.WordTrace]
  refine ⟨257799490710020965251599741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171866327140013976834399827 257799490710020965251599741)
  ·
    refine ⟨96674809016257861969349903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257799490710020965251599741 96674809016257861969349903)
    ·
      refine ⟨145012213524386792954024855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96674809016257861969349903 145012213524386792954024855)
      ·
        refine ⟨217518320286580189431037283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145012213524386792954024855 217518320286580189431037283)
        ·
          refine ⟨326277480429870284146555925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217518320286580189431037283 326277480429870284146555925)
          ·
            refine ⟨15294256895150169569369809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326277480429870284146555925 15294256895150169569369809)
            ·
              refine ⟨11470692671362627177027357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15294256895150169569369809 11470692671362627177027357)
              ·
                refine ⟨4301509751760985191385259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11470692671362627177027357 4301509751760985191385259)
                ·
                  refine ⟨6452264627641477787077889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301509751760985191385259 6452264627641477787077889)
                  ·
                    refine ⟨4839198470731108340308417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452264627641477787077889 4839198470731108340308417)
                    ·
                      refine ⟨3629398853048331255231313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839198470731108340308417 3629398853048331255231313)
                      ·
                        rfl

theorem cell23_7068229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_7068229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068229 prefixEnd_7068229 := by exact prefixLift 7068229
  have htrace : WordTrace (prefixWord ++ tailWord_7068229) baseStart_7068229 baseEnd_7068229 := by
    simpa [prefixWord, tailWord_7068229, baseEnd_7068229] using wordTrace_append hprefix tailTrace_7068229
  have hstable : (prefixWord ++ tailWord_7068229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068229).length < 2 ^ (prefixWord ++ tailWord_7068229).sum := by decide
  have hdescent : baseEnd_7068229 < baseStart_7068229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068288 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_7068288 : Nat := 118140960795 + 7068288 * 2 ^ 59
def prefixEnd_7068288 : Nat := 4983230072969 + 3 ^ 40 * 7068288 * 2
def baseEnd_7068288 : Nat := 3629429148406946524393541

theorem tailTrace_7068288 : CollatzResearch.WordTrace tailWord_7068288 prefixEnd_7068288 3629429148406946524393541 := by
  unfold tailWord_7068288
  simp only [CollatzResearch.WordTrace]
  refine ⟨128900821308403609163998759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171867761744538145551998345 128900821308403609163998759)
  ·
    refine ⟨193351231962605413745998139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128900821308403609163998759 193351231962605413745998139)
    ·
      refine ⟨290026847943908120618997209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193351231962605413745998139 290026847943908120618997209)
      ·
        refine ⟨217520135957931090464247907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290026847943908120618997209 217520135957931090464247907)
        ·
          refine ⟨326280203936896635696371861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217520135957931090464247907 326280203936896635696371861)
          ·
            refine ⟨15294384559542029798267431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326280203936896635696371861 15294384559542029798267431)
            ·
              refine ⟨22941576839313044697401147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15294384559542029798267431 22941576839313044697401147)
              ·
                refine ⟨34412365258969567046101721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22941576839313044697401147 34412365258969567046101721)
                ·
                  refine ⟨25809273944227175284576291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34412365258969567046101721 25809273944227175284576291)
                  ·
                    refine ⟨38713910916340762926864437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25809273944227175284576291 38713910916340762926864437)
                    ·
                      refine ⟨3629429148406946524393541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38713910916340762926864437 3629429148406946524393541)
                      ·
                        rfl

theorem cell23_7068288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_7068288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068288 prefixEnd_7068288 := by exact prefixLift 7068288
  have htrace : WordTrace (prefixWord ++ tailWord_7068288) baseStart_7068288 baseEnd_7068288 := by
    simpa [prefixWord, tailWord_7068288, baseEnd_7068288] using wordTrace_append hprefix tailTrace_7068288
  have hstable : (prefixWord ++ tailWord_7068288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068288).length < 2 ^ (prefixWord ++ tailWord_7068288).sum := by decide
  have hdescent : baseEnd_7068288 < baseStart_7068288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068291 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 9]
def baseStart_7068291 : Nat := 118140960795 + 7068291 * 2 ^ 59
def prefixEnd_7068291 : Nat := 4983230072969 + 3 ^ 40 * 7068291 * 2
def baseEnd_7068291 : Nat := 403270076538767779184003

theorem tailTrace_7068291 : CollatzResearch.WordTrace tailWord_7068291 prefixEnd_7068291 403270076538767779184003 := by
  unfold tailWord_7068291
  simp only [CollatzResearch.WordTrace]
  refine ⟨257801752035796349840356727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171867834690530899893571151 257801752035796349840356727)
  ·
    refine ⟨386702628053694524760535091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257801752035796349840356727 386702628053694524760535091)
    ·
      refine ⟨580053942080541787140802637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386702628053694524760535091 580053942080541787140802637)
      ·
        refine ⟨217520228280203170177800989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580053942080541787140802637 217520228280203170177800989)
        ·
          refine ⟨81570085605076188816675371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217520228280203170177800989 81570085605076188816675371)
          ·
            refine ⟨122355128407614283225013057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81570085605076188816675371 122355128407614283225013057)
            ·
              refine ⟨91766346305710712418759793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122355128407614283225013057 91766346305710712418759793)
              ·
                refine ⟨68824759729283034314069845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91766346305710712418759793 68824759729283034314069845)
                ·
                  refine ⟨403270076538767779184003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68824759729283034314069845 403270076538767779184003)
                  ·
                    rfl

theorem cell23_7068291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 9].length) (baseStart_7068291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068291 prefixEnd_7068291 := by exact prefixLift 7068291
  have htrace : WordTrace (prefixWord ++ tailWord_7068291) baseStart_7068291 baseEnd_7068291 := by
    simpa [prefixWord, tailWord_7068291, baseEnd_7068291] using wordTrace_append hprefix tailTrace_7068291
  have hstable : (prefixWord ++ tailWord_7068291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068291).length < 2 ^ (prefixWord ++ tailWord_7068291).sum := by decide
  have hdescent : baseEnd_7068291 < baseStart_7068291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068302 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_7068302 : Nat := 118140960795 + 7068302 * 2 ^ 59
def prefixEnd_7068302 : Nat := 4983230072969 + 3 ^ 40 * 7068302 * 2
def baseEnd_7068302 : Nat := 3629436337136109469618477

theorem tailTrace_7068302 : CollatzResearch.WordTrace tailWord_7068302 prefixEnd_7068302 3629436337136109469618477 := by
  unfold tailWord_7068302
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225269154844562339875895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171868102159170999146004773 32225269154844562339875895)
  ·
    refine ⟨48337903732266843509813843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32225269154844562339875895 48337903732266843509813843)
    ·
      refine ⟨72506855598400265264720765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48337903732266843509813843 72506855598400265264720765)
      ·
        refine ⟨27190070849400099474270287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72506855598400265264720765 27190070849400099474270287)
        ·
          refine ⟨40785106274100149211405431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27190070849400099474270287 40785106274100149211405431)
          ·
            refine ⟨61177659411150223817108147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40785106274100149211405431 61177659411150223817108147)
            ·
              refine ⟨91766489116725335725662221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61177659411150223817108147 91766489116725335725662221)
              ·
                refine ⟨34412433418772000897123333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91766489116725335725662221 34412433418772000897123333)
                ·
                  refine ⟨6452331266019750168210625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34412433418772000897123333 6452331266019750168210625)
                  ·
                    refine ⟨4839248449514812626157969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452331266019750168210625 4839248449514812626157969)
                    ·
                      refine ⟨3629436337136109469618477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839248449514812626157969 3629436337136109469618477)
                      ·
                        rfl

theorem cell23_7068302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_7068302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068302 prefixEnd_7068302 := by exact prefixLift 7068302
  have htrace : WordTrace (prefixWord ++ tailWord_7068302) baseStart_7068302 baseEnd_7068302 := by
    simpa [prefixWord, tailWord_7068302, baseEnd_7068302] using wordTrace_append hprefix tailTrace_7068302
  have hstable : (prefixWord ++ tailWord_7068302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068302).length < 2 ^ (prefixWord ++ tailWord_7068302).sum := by decide
  have hdescent : baseEnd_7068302 < baseStart_7068302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
