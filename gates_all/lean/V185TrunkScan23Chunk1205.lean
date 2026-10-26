import V185TrunkScan23Chunk1204

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7138338 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7138338 : Nat := 118140960795 + 7138338 * 2 ^ 59
def prefixEnd_7138338 : Nat := 4983230072969 + 3 ^ 40 * 7138338 * 2
def baseEnd_7138338 : Nat := 1221799489418132484482129

theorem tailTrace_7138338 : CollatzResearch.WordTrace tailWord_7138338 prefixEnd_7138338 1221799489418132484482129 := by
  unfold tailWord_7138338
  simp only [CollatzResearch.WordTrace]
  refine ⟨65089144003257007978881917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173571050675352021277018445 65089144003257007978881917)
  ·
    refine ⟨24408429001221377992080719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65089144003257007978881917 24408429001221377992080719)
    ·
      refine ⟨36612643501832066988121079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24408429001221377992080719 36612643501832066988121079)
      ·
        refine ⟨54918965252748100482181619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36612643501832066988121079 54918965252748100482181619)
        ·
          refine ⟨82378447879122150723272429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54918965252748100482181619 82378447879122150723272429)
          ·
            refine ⟨30891917954670806521227161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82378447879122150723272429 30891917954670806521227161)
            ·
              refine ⟨23168938466003104890920371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30891917954670806521227161 23168938466003104890920371)
              ·
                refine ⟨34753407699004657336380557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23168938466003104890920371 34753407699004657336380557)
                ·
                  refine ⟨13032527887126746501142709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34753407699004657336380557 13032527887126746501142709)
                  ·
                    refine ⟨1221799489418132484482129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13032527887126746501142709 1221799489418132484482129)
                    ·
                      rfl

theorem cell23_7138338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7138338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138338 prefixEnd_7138338 := by exact prefixLift 7138338
  have htrace : WordTrace (prefixWord ++ tailWord_7138338) baseStart_7138338 baseEnd_7138338 := by
    simpa [prefixWord, tailWord_7138338, baseEnd_7138338] using wordTrace_append hprefix tailTrace_7138338
  have hstable : (prefixWord ++ tailWord_7138338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138338).length < 2 ^ (prefixWord ++ tailWord_7138338).sum := by decide
  have hdescent : baseEnd_7138338 < baseStart_7138338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138352 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 1, 1, 3]
def baseStart_7138352 : Nat := 118140960795 + 7138352 * 2 ^ 59
def prefixEnd_7138352 : Nat := 4983230072969 + 3 ^ 40 * 7138352 * 2
def baseEnd_7138352 : Nat := 3665405656983560398671323

theorem tailTrace_7138352 : CollatzResearch.WordTrace tailWord_7138352 prefixEnd_7138352 3665405656983560398671323 := by
  unfold tailWord_7138352
  simp only [CollatzResearch.WordTrace]
  refine ⟨130178543317488656153268655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173571391089984874871024873 130178543317488656153268655)
  ·
    refine ⟨195267814976232984229902983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130178543317488656153268655 195267814976232984229902983)
    ·
      refine ⟨292901722464349476344854475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195267814976232984229902983 292901722464349476344854475)
      ·
        refine ⟨439352583696524214517281713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292901722464349476344854475 439352583696524214517281713)
        ·
          refine ⟨329514437772393160887961285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439352583696524214517281713 329514437772393160887961285)
          ·
            refine ⟨61783957082323717666492741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329514437772393160887961285 61783957082323717666492741)
            ·
              refine ⟨11584491952935697062467389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61783957082323717666492741 11584491952935697062467389)
              ·
                refine ⟨4344184482350886398425271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11584491952935697062467389 4344184482350886398425271)
                ·
                  refine ⟨6516276723526329597637907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344184482350886398425271 6516276723526329597637907)
                  ·
                    refine ⟨9774415085289494396456861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6516276723526329597637907 9774415085289494396456861)
                    ·
                      refine ⟨3665405656983560398671323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774415085289494396456861 3665405656983560398671323)
                      ·
                        rfl

theorem cell23_7138352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 1, 3].length) (baseStart_7138352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138352 prefixEnd_7138352 := by exact prefixLift 7138352
  have htrace : WordTrace (prefixWord ++ tailWord_7138352) baseStart_7138352 baseEnd_7138352 := by
    simpa [prefixWord, tailWord_7138352, baseEnd_7138352] using wordTrace_append hprefix tailTrace_7138352
  have hstable : (prefixWord ++ tailWord_7138352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138352).length < 2 ^ (prefixWord ++ tailWord_7138352).sum := by decide
  have hdescent : baseEnd_7138352 < baseStart_7138352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138368 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 4, 4]
def baseStart_7138368 : Nat := 118140960795 + 7138368 * 2 ^ 59
def prefixEnd_7138368 : Nat := 4983230072969 + 3 ^ 40 * 7138368 * 2
def baseEnd_7138368 : Nat := 1221804624224677445357083

theorem tailTrace_7138368 : CollatzResearch.WordTrace tailWord_7138368 prefixEnd_7138368 1221804624224677445357083 := by
  unfold tailWord_7138368
  simp only [CollatzResearch.WordTrace]
  refine ⟨130178835101459673519559879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173571780135279564692746505 130178835101459673519559879)
  ·
    refine ⟨195268252652189510279339819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130178835101459673519559879 195268252652189510279339819)
    ·
      refine ⟨292902378978284265419009729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195268252652189510279339819 292902378978284265419009729)
      ·
        refine ⟨219676784233713199064257297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292902378978284265419009729 219676784233713199064257297)
        ·
          refine ⟨164757588175284899298192973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219676784233713199064257297 164757588175284899298192973)
          ·
            refine ⟨61784095565731837236822365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164757588175284899298192973 61784095565731837236822365)
            ·
              refine ⟨23169035837149438963808387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61784095565731837236822365 23169035837149438963808387)
              ·
                refine ⟨34753553755724158445712581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23169035837149438963808387 34753553755724158445712581)
                ·
                  refine ⟨6516291329198279708571109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34753553755724158445712581 6516291329198279708571109)
                  ·
                    refine ⟨1221804624224677445357083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516291329198279708571109 1221804624224677445357083)
                    ·
                      rfl

theorem cell23_7138368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_7138368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138368 prefixEnd_7138368 := by exact prefixLift 7138368
  have htrace : WordTrace (prefixWord ++ tailWord_7138368) baseStart_7138368 baseEnd_7138368 := by
    simpa [prefixWord, tailWord_7138368, baseEnd_7138368] using wordTrace_append hprefix tailTrace_7138368
  have hstable : (prefixWord ++ tailWord_7138368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138368).length < 2 ^ (prefixWord ++ tailWord_7138368).sum := by decide
  have hdescent : baseEnd_7138368 < baseStart_7138368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138371 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6]
def baseStart_7138371 : Nat := 118140960795 + 7138371 * 2 ^ 59
def prefixEnd_7138371 : Nat := 4983230072969 + 3 ^ 40 * 7138371 * 2
def baseEnd_7138371 : Nat := 3665415413115995824333735

theorem tailTrace_7138371 : CollatzResearch.WordTrace tailWord_7138371 prefixEnd_7138371 3665415413115995824333735 := by
  unfold tailWord_7138371
  simp only [CollatzResearch.WordTrace]
  refine ⟨260357779621908478551478967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173571853081272319034319311 260357779621908478551478967)
  ·
    refine ⟨390536669432862717827218451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260357779621908478551478967 390536669432862717827218451)
    ·
      refine ⟨585805004149294076740827677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390536669432862717827218451 585805004149294076740827677)
      ·
        refine ⟨219676876555985278777810379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585805004149294076740827677 219676876555985278777810379)
        ·
          refine ⟨329515314833977918166715569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219676876555985278777810379 329515314833977918166715569)
          ·
            refine ⟨247136486125483438625036677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329515314833977918166715569 247136486125483438625036677)
            ·
              refine ⟨46338091148528144742194377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247136486125483438625036677 46338091148528144742194377)
              ·
                refine ⟨34753568361396108556645783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46338091148528144742194377 34753568361396108556645783)
                ·
                  refine ⟨52130352542094162834968675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34753568361396108556645783 52130352542094162834968675)
                  ·
                    refine ⟨78195528813141244252453013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52130352542094162834968675 78195528813141244252453013)
                    ·
                      refine ⟨3665415413115995824333735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78195528813141244252453013 3665415413115995824333735)
                      ·
                        rfl

theorem cell23_7138371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_7138371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138371 prefixEnd_7138371 := by exact prefixLift 7138371
  have htrace : WordTrace (prefixWord ++ tailWord_7138371) baseStart_7138371 baseEnd_7138371 := by
    simpa [prefixWord, tailWord_7138371, baseEnd_7138371] using wordTrace_append hprefix tailTrace_7138371
  have hstable : (prefixWord ++ tailWord_7138371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138371).length < 2 ^ (prefixWord ++ tailWord_7138371).sum := by decide
  have hdescent : baseEnd_7138371 < baseStart_7138371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138378 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_7138378 : Nat := 118140960795 + 7138378 * 2 ^ 59
def prefixEnd_7138378 : Nat := 4983230072969 + 3 ^ 40 * 7138378 * 2
def baseEnd_7138378 : Nat := 3665419007480577296946203

theorem tailTrace_7138378 : CollatzResearch.WordTrace tailWord_7138378 prefixEnd_7138378 3665419007480577296946203 := by
  unfold tailWord_7138378
  simp only [CollatzResearch.WordTrace]
  refine ⟨65089508733220779686745947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173572023288588745831322525 65089508733220779686745947)
  ·
    refine ⟨97634263099831169530118921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65089508733220779686745947 97634263099831169530118921)
    ·
      refine ⟨73225697324873377147589191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97634263099831169530118921 73225697324873377147589191)
      ·
        refine ⟨109838545987310065721383787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73225697324873377147589191 109838545987310065721383787)
        ·
          refine ⟨164757818980965098582075681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109838545987310065721383787 164757818980965098582075681)
          ·
            refine ⟨123568364235723823936556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164757818980965098582075681 123568364235723823936556761)
            ·
              refine ⟨92676273176792867952417571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123568364235723823936556761 92676273176792867952417571)
              ·
                refine ⟨139014409765189301928626357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92676273176792867952417571 139014409765189301928626357)
                ·
                  refine ⟨13032600915486497055808721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139014409765189301928626357 13032600915486497055808721)
                  ·
                    refine ⟨9774450686614872791856541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13032600915486497055808721 9774450686614872791856541)
                    ·
                      refine ⟨3665419007480577296946203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774450686614872791856541 3665419007480577296946203)
                      ·
                        rfl

theorem cell23_7138378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_7138378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138378 prefixEnd_7138378 := by exact prefixLift 7138378
  have htrace : WordTrace (prefixWord ++ tailWord_7138378) baseStart_7138378 baseEnd_7138378 := by
    simpa [prefixWord, tailWord_7138378, baseEnd_7138378] using wordTrace_append hprefix tailTrace_7138378
  have hstable : (prefixWord ++ tailWord_7138378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138378).length < 2 ^ (prefixWord ++ tailWord_7138378).sum := by decide
  have hdescent : baseEnd_7138378 < baseStart_7138378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138409 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 1, 2, 2]
def baseStart_7138409 : Nat := 118140960795 + 7138409 * 2 ^ 59
def prefixEnd_7138409 : Nat := 4983230072969 + 3 ^ 40 * 7138409 * 2
def baseEnd_7138409 : Nat := 3665434925380866675658561

theorem tailTrace_7138409 : CollatzResearch.WordTrace tailWord_7138409 prefixEnd_7138409 3665434925380866675658561 := by
  unfold tailWord_7138409
  simp only [CollatzResearch.WordTrace]
  refine ⟨260359165595770811041362281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173572777063847207360908187 260359165595770811041362281)
  ·
    refine ⟨195269374196828108281021711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260359165595770811041362281 195269374196828108281021711)
    ·
      refine ⟨292904061295242162421532567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195269374196828108281021711 292904061295242162421532567)
      ·
        refine ⟨439356091942863243632298851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292904061295242162421532567 439356091942863243632298851)
        ·
          refine ⟨659034137914294865448448277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439356091942863243632298851 659034137914294865448448277)
          ·
            refine ⟨30892225214732571817896013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 659034137914294865448448277 30892225214732571817896013)
            ·
              refine ⟨11584584455524714431711005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30892225214732571817896013 11584584455524714431711005)
              ·
                refine ⟨4344219170821767911891627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11584584455524714431711005 4344219170821767911891627)
                ·
                  refine ⟨6516328756232651867837441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344219170821767911891627 6516328756232651867837441)
                  ·
                    refine ⟨4887246567174488900878081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516328756232651867837441 4887246567174488900878081)
                    ·
                      refine ⟨3665434925380866675658561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887246567174488900878081 3665434925380866675658561)
                      ·
                        rfl

theorem cell23_7138409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 2, 2].length) (baseStart_7138409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138409 prefixEnd_7138409 := by exact prefixLift 7138409
  have htrace : WordTrace (prefixWord ++ tailWord_7138409) baseStart_7138409 baseEnd_7138409 := by
    simpa [prefixWord, tailWord_7138409, baseEnd_7138409] using wordTrace_append hprefix tailTrace_7138409
  have hstable : (prefixWord ++ tailWord_7138409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138409).length < 2 ^ (prefixWord ++ tailWord_7138409).sum := by decide
  have hdescent : baseEnd_7138409 < baseStart_7138409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138435 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 3, 3, 2]
def baseStart_7138435 : Nat := 118140960795 + 7138435 * 2 ^ 59
def prefixEnd_7138435 : Nat := 4983230072969 + 3 ^ 40 * 7138435 * 2
def baseEnd_7138435 : Nat := 3665448275877883573933441

theorem tailTrace_7138435 : CollatzResearch.WordTrace tailWord_7138435 prefixEnd_7138435 3665448275877883573933441 := by
  unfold tailWord_7138435
  simp only [CollatzResearch.WordTrace]
  refine ⟨260360113893676617481808759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173573409262451078321205839 260360113893676617481808759)
  ·
    refine ⟨390540170840514926222713139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260360113893676617481808759 390540170840514926222713139)
    ·
      refine ⟨585810256260772389334069709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390540170840514926222713139 585810256260772389334069709)
      ·
        refine ⟨219678846097789646000276141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585810256260772389334069709 219678846097789646000276141)
        ·
          refine ⟨82379567286671117250103553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219678846097789646000276141 82379567286671117250103553)
          ·
            refine ⟨61784675465003337937577665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82379567286671117250103553 61784675465003337937577665)
            ·
              refine ⟨46338506598752503453183249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61784675465003337937577665 46338506598752503453183249)
              ·
                refine ⟨34753879949064377589887437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46338506598752503453183249 34753879949064377589887437)
                ·
                  refine ⟨13032704980899141596207789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34753879949064377589887437 13032704980899141596207789)
                  ·
                    refine ⟨4887264367837178098577921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13032704980899141596207789 4887264367837178098577921)
                    ·
                      refine ⟨3665448275877883573933441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887264367837178098577921 3665448275877883573933441)
                      ·
                        rfl

theorem cell23_7138435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_7138435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138435 prefixEnd_7138435 := by exact prefixLift 7138435
  have htrace : WordTrace (prefixWord ++ tailWord_7138435) baseStart_7138435 baseEnd_7138435 := by
    simpa [prefixWord, tailWord_7138435, baseEnd_7138435] using wordTrace_append hprefix tailTrace_7138435
  have hstable : (prefixWord ++ tailWord_7138435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138435).length < 2 ^ (prefixWord ++ tailWord_7138435).sum := by decide
  have hdescent : baseEnd_7138435 < baseStart_7138435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138442 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_7138442 : Nat := 118140960795 + 7138442 * 2 ^ 59
def prefixEnd_7138442 : Nat := 4983230072969 + 3 ^ 40 * 7138442 * 2
def baseEnd_7138442 : Nat := 3665451870242465046545909

theorem tailTrace_7138442 : CollatzResearch.WordTrace tailWord_7138442 prefixEnd_7138442 3665451870242465046545909 := by
  unfold tailWord_7138442
  simp only [CollatzResearch.WordTrace]
  refine ⟨65090092301162814419328395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173573579469767505118209053 65090092301162814419328395)
  ·
    refine ⟨97635138451744221628992593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65090092301162814419328395 97635138451744221628992593)
    ·
      refine ⟨73226353838808166221744445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97635138451744221628992593 73226353838808166221744445)
      ·
        refine ⟨27459882689553062333154167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73226353838808166221744445 27459882689553062333154167)
        ·
          refine ⟨41189824034329593499731251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27459882689553062333154167 41189824034329593499731251)
          ·
            refine ⟨61784736051494390249596877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41189824034329593499731251 61784736051494390249596877)
            ·
              refine ⟨23169276019310396343598829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61784736051494390249596877 23169276019310396343598829)
              ·
                refine ⟨8688478507241398628849561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23169276019310396343598829 8688478507241398628849561)
                ·
                  refine ⟨6516358880431048971637171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688478507241398628849561 6516358880431048971637171)
                  ·
                    refine ⟨9774538320646573457455757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6516358880431048971637171 9774538320646573457455757)
                    ·
                      refine ⟨3665451870242465046545909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774538320646573457455757 3665451870242465046545909)
                      ·
                        rfl

theorem cell23_7138442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_7138442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138442 prefixEnd_7138442 := by exact prefixLift 7138442
  have htrace : WordTrace (prefixWord ++ tailWord_7138442) baseStart_7138442 baseEnd_7138442 := by
    simpa [prefixWord, tailWord_7138442, baseEnd_7138442] using wordTrace_append hprefix tailTrace_7138442
  have hstable : (prefixWord ++ tailWord_7138442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138442).length < 2 ^ (prefixWord ++ tailWord_7138442).sum := by decide
  have hdescent : baseEnd_7138442 < baseStart_7138442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138469 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 1, 3, 2]
def baseStart_7138469 : Nat := 118140960795 + 7138469 * 2 ^ 59
def prefixEnd_7138469 : Nat := 4983230072969 + 3 ^ 40 * 7138469 * 2
def baseEnd_7138469 : Nat := 3665465734220136440908285

theorem tailTrace_7138469 : CollatzResearch.WordTrace tailWord_7138469 prefixEnd_7138469 3665465734220136440908285 := by
  unfold tailWord_7138469
  simp only [CollatzResearch.WordTrace]
  refine ⟨260361353975553441288546461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173574235983702294192364307 260361353975553441288546461)
  ·
    refine ⟨97635507740832540483204923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260361353975553441288546461 97635507740832540483204923)
    ·
      refine ⟨146453261611248810724807385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97635507740832540483204923 146453261611248810724807385)
      ·
        refine ⟨109839946208436608043605539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146453261611248810724807385 109839946208436608043605539)
        ·
          refine ⟨164759919312654912065408309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109839946208436608043605539 164759919312654912065408309)
          ·
            refine ⟨15446242435561398006132029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164759919312654912065408309 15446242435561398006132029)
            ·
              refine ⟨5792340913335524252299511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15446242435561398006132029 5792340913335524252299511)
              ·
                refine ⟨8688511370003286378449267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792340913335524252299511 8688511370003286378449267)
                ·
                  refine ⟨13032767055004929567673901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8688511370003286378449267 13032767055004929567673901)
                  ·
                    refine ⟨4887287645626848587877713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13032767055004929567673901 4887287645626848587877713)
                    ·
                      refine ⟨3665465734220136440908285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887287645626848587877713 3665465734220136440908285)
                      ·
                        rfl

theorem cell23_7138469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_7138469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138469 prefixEnd_7138469 := by exact prefixLift 7138469
  have htrace : WordTrace (prefixWord ++ tailWord_7138469) baseStart_7138469 baseEnd_7138469 := by
    simpa [prefixWord, tailWord_7138469, baseEnd_7138469] using wordTrace_append hprefix tailTrace_7138469
  have hstable : (prefixWord ++ tailWord_7138469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138469).length < 2 ^ (prefixWord ++ tailWord_7138469).sum := by decide
  have hdescent : baseEnd_7138469 < baseStart_7138469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138533 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 2, 2, 2]
def baseStart_7138533 : Nat := 118140960795 + 7138533 * 2 ^ 59
def prefixEnd_7138533 : Nat := 4983230072969 + 3 ^ 40 * 7138533 * 2
def baseEnd_7138533 : Nat := 3665498596982024190507991

theorem tailTrace_7138533 : CollatzResearch.WordTrace tailWord_7138533 prefixEnd_7138533 3665498596982024190507991 := by
  unfold tailWord_7138533
  simp only [CollatzResearch.WordTrace]
  refine ⟨260363688247321580218876253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173575792164881053479250835 260363688247321580218876253)
  ·
    refine ⟨97636383092745592582078595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260363688247321580218876253 97636383092745592582078595)
    ·
      refine ⟨146454574639118388873117893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97636383092745592582078595 146454574639118388873117893)
      ·
        refine ⟨27460232744834697913709605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146454574639118388873117893 27460232744834697913709605)
        ·
          refine ⟨5148793639656505858820551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27460232744834697913709605 5148793639656505858820551)
          ·
            refine ⟨7723190459484758788230827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148793639656505858820551 7723190459484758788230827)
            ·
              refine ⟨11584785689227138182346241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723190459484758788230827 11584785689227138182346241)
              ·
                refine ⟨8688589266920353636759681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11584785689227138182346241 8688589266920353636759681)
                ·
                  refine ⟨6516441950190265227569761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688589266920353636759681 6516441950190265227569761)
                  ·
                    refine ⟨4887331462642698920677321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516441950190265227569761 4887331462642698920677321)
                    ·
                      refine ⟨3665498596982024190507991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887331462642698920677321 3665498596982024190507991)
                      ·
                        rfl

theorem cell23_7138533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_7138533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138533 prefixEnd_7138533 := by exact prefixLift 7138533
  have htrace : WordTrace (prefixWord ++ tailWord_7138533) baseStart_7138533 baseEnd_7138533 := by
    simpa [prefixWord, tailWord_7138533, baseEnd_7138533] using wordTrace_append hprefix tailTrace_7138533
  have hstable : (prefixWord ++ tailWord_7138533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138533).length < 2 ^ (prefixWord ++ tailWord_7138533).sum := by decide
  have hdescent : baseEnd_7138533 < baseStart_7138533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138565 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_7138565 : Nat := 118140960795 + 7138565 * 2 ^ 59
def prefixEnd_7138565 : Nat := 4983230072969 + 3 ^ 40 * 7138565 * 2
def baseEnd_7138565 : Nat := 1221838342787656021769281

theorem tailTrace_7138565 : CollatzResearch.WordTrace tailWord_7138565 prefixEnd_7138565 1221838342787656021769281 := by
  unfold tailWord_7138565
  simp only [CollatzResearch.WordTrace]
  refine ⟨260364855383205649684041149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173576570255470433122694099 260364855383205649684041149)
  ·
    refine ⟨97636820768702118631515431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260364855383205649684041149 97636820768702118631515431)
    ·
      refine ⟨146455231153053177947273147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97636820768702118631515431 146455231153053177947273147)
      ·
        refine ⟨219682846729579766920909721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146455231153053177947273147 219682846729579766920909721)
        ·
          refine ⟨164762135047184825190682291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219682846729579766920909721 164762135047184825190682291)
          ·
            refine ⟨247143202570777237786023437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164762135047184825190682291 247143202570777237786023437)
            ·
              refine ⟨92678700964041464169758789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247143202570777237786023437 92678700964041464169758789)
              ·
                refine ⟨17377256430757774531829773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92678700964041464169758789 17377256430757774531829773)
                ·
                  refine ⟨6516471161534165449436165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17377256430757774531829773 6516471161534165449436165)
                  ·
                    refine ⟨1221838342787656021769281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516471161534165449436165 1221838342787656021769281)
                    ·
                      rfl

theorem cell23_7138565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_7138565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138565 prefixEnd_7138565 := by exact prefixLift 7138565
  have htrace : WordTrace (prefixWord ++ tailWord_7138565) baseStart_7138565 baseEnd_7138565 := by
    simpa [prefixWord, tailWord_7138565, baseEnd_7138565] using wordTrace_append hprefix tailTrace_7138565
  have hstable : (prefixWord ++ tailWord_7138565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138565).length < 2 ^ (prefixWord ++ tailWord_7138565).sum := by decide
  have hdescent : baseEnd_7138565 < baseStart_7138565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138612 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 6]
def baseStart_7138612 : Nat := 118140960795 + 7138612 * 2 ^ 59
def prefixEnd_7138612 : Nat := 4983230072969 + 3 ^ 40 * 7138612 * 2
def baseEnd_7138612 : Nat := 407282129105969931268903

theorem tailTrace_7138612 : CollatzResearch.WordTrace tailWord_7138612 prefixEnd_7138612 407282129105969931268903 := by
  unfold tailWord_7138612
  simp only [CollatzResearch.WordTrace]
  refine ⟨130183284807017688355501045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173577713076023584474001393 130183284807017688355501045)
  ·
    refine ⟨12204682950657908283328223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130183284807017688355501045 12204682950657908283328223)
    ·
      refine ⟨18307024425986862424992335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12204682950657908283328223 18307024425986862424992335)
      ·
        refine ⟨27460536638980293637488503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18307024425986862424992335 27460536638980293637488503)
        ·
          refine ⟨41190804958470440456232755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27460536638980293637488503 41190804958470440456232755)
          ·
            refine ⟨61786207437705660684349133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41190804958470440456232755 61786207437705660684349133)
            ·
              refine ⟨23169827789139622756630925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61786207437705660684349133 23169827789139622756630925)
              ·
                refine ⟨8688685420927358533736597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23169827789139622756630925 8688685420927358533736597)
                ·
                  refine ⟨407282129105969931268903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8688685420927358533736597 407282129105969931268903)
                  ·
                    rfl

theorem cell23_7138612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_7138612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138612 prefixEnd_7138612 := by exact prefixLift 7138612
  have htrace : WordTrace (prefixWord ++ tailWord_7138612) baseStart_7138612 baseEnd_7138612 := by
    simpa [prefixWord, tailWord_7138612, baseEnd_7138612] using wordTrace_append hprefix tailTrace_7138612
  have hstable : (prefixWord ++ tailWord_7138612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138612).length < 2 ^ (prefixWord ++ tailWord_7138612).sum := by decide
  have hdescent : baseEnd_7138612 < baseStart_7138612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138656 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 1, 1, 3]
def baseStart_7138656 : Nat := 118140960795 + 7138656 * 2 ^ 59
def prefixEnd_7138656 : Nat := 4983230072969 + 3 ^ 40 * 7138656 * 2
def baseEnd_7138656 : Nat := 3665561755102527209269925

theorem tailTrace_7138656 : CollatzResearch.WordTrace tailWord_7138656 prefixEnd_7138656 3665561755102527209269925 := by
  unfold tailWord_7138656
  simp only [CollatzResearch.WordTrace]
  refine ⟨130184087212937986112801911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173578782950583981483735881 130184087212937986112801911)
  ·
    refine ⟨195276130819406979169202867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130184087212937986112801911 195276130819406979169202867)
    ·
      refine ⟨292914196229110468753804301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195276130819406979169202867 292914196229110468753804301)
      ·
        refine ⟨109842823585916425782676613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292914196229110468753804301 109842823585916425782676613)
        ·
          refine ⟨20595529422359329834251865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109842823585916425782676613 20595529422359329834251865)
          ·
            refine ⟨15446647066769497375688899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20595529422359329834251865 15446647066769497375688899)
            ·
              refine ⟨23169970600154246063533349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15446647066769497375688899 23169970600154246063533349)
              ·
                refine ⟨4344369487528921136912503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23169970600154246063533349 4344369487528921136912503)
                ·
                  refine ⟨6516554231293381705368755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344369487528921136912503 6516554231293381705368755)
                  ·
                    refine ⟨9774831346940072558053133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6516554231293381705368755 9774831346940072558053133)
                    ·
                      refine ⟨3665561755102527209269925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774831346940072558053133 3665561755102527209269925)
                      ·
                        rfl

theorem cell23_7138656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_7138656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138656 prefixEnd_7138656 := by exact prefixLift 7138656
  have htrace : WordTrace (prefixWord ++ tailWord_7138656) baseStart_7138656 baseEnd_7138656 := by
    simpa [prefixWord, tailWord_7138656, baseEnd_7138656] using wordTrace_append hprefix tailTrace_7138656
  have hstable : (prefixWord ++ tailWord_7138656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138656).length < 2 ^ (prefixWord ++ tailWord_7138656).sum := by decide
  have hdescent : baseEnd_7138656 < baseStart_7138656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138672 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 2, 4]
def baseStart_7138672 : Nat := 118140960795 + 7138672 * 2 ^ 59
def prefixEnd_7138672 : Nat := 4983230072969 + 3 ^ 40 * 7138672 * 2
def baseEnd_7138672 : Nat := 1221856656930999715556617

theorem tailTrace_7138672 : CollatzResearch.WordTrace tailWord_7138672 prefixEnd_7138672 1221856656930999715556617 := by
  unfold tailWord_7138672
  simp only [CollatzResearch.WordTrace]
  refine ⟨130184378996909003479093135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173579171995878671305457513 130184378996909003479093135)
  ·
    refine ⟨195276568495363505218639703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130184378996909003479093135 195276568495363505218639703)
    ·
      refine ⟨292914852743045257827959555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195276568495363505218639703 292914852743045257827959555)
      ·
        refine ⟨439372279114567886741939333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292914852743045257827959555 439372279114567886741939333)
        ·
          refine ⟨82382302333981478764113625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439372279114567886741939333 82382302333981478764113625)
          ·
            refine ⟨61786726750486109073085219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82382302333981478764113625 61786726750486109073085219)
            ·
              refine ⟨92680090125729163609627829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61786726750486109073085219 92680090125729163609627829)
              ·
                refine ⟨8688758449287109088402609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92680090125729163609627829 8688758449287109088402609)
                ·
                  refine ⟨6516568836965331816301957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688758449287109088402609 6516568836965331816301957)
                  ·
                    refine ⟨1221856656930999715556617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516568836965331816301957 1221856656930999715556617)
                    ·
                      rfl

theorem cell23_7138672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_7138672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138672 prefixEnd_7138672 := by exact prefixLift 7138672
  have htrace : WordTrace (prefixWord ++ tailWord_7138672) baseStart_7138672 baseEnd_7138672 := by
    simpa [prefixWord, tailWord_7138672, baseEnd_7138672] using wordTrace_append hprefix tailTrace_7138672
  have hstable : (prefixWord ++ tailWord_7138672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138672).length < 2 ^ (prefixWord ++ tailWord_7138672).sum := by decide
  have hdescent : baseEnd_7138672 < baseStart_7138672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138679 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 3, 2, 2]
def baseStart_7138679 : Nat := 118140960795 + 7138679 * 2 ^ 59
def prefixEnd_7138679 : Nat := 4983230072969 + 3 ^ 40 * 7138679 * 2
def baseEnd_7138679 : Nat := 3665573565157580619282319

theorem tailTrace_7138679 : CollatzResearch.WordTrace tailWord_7138679 prefixEnd_7138679 3665573565157580619282319 := by
  unfold tailWord_7138679
  simp only [CollatzResearch.WordTrace]
  refine ⟨260369013304792647153691091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173579342203195098102460727 260369013304792647153691091)
  ·
    refine ⟨390553519957188970730536637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260369013304792647153691091 390553519957188970730536637)
    ·
      refine ⟨146457569983945864023951239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390553519957188970730536637 146457569983945864023951239)
      ·
        refine ⟨219686354975918796035926859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146457569983945864023951239 219686354975918796035926859)
        ·
          refine ⟨329529532463878194053890289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219686354975918796035926859 329529532463878194053890289)
          ·
            refine ⟨247147149347908645540417717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329529532463878194053890289 247147149347908645540417717)
            ·
              refine ⟨23170045251366435519414161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247147149347908645540417717 23170045251366435519414161)
              ·
                refine ⟨17377533938524826639560621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23170045251366435519414161 17377533938524826639560621)
                ·
                  refine ⟨6516575226946809989835233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17377533938524826639560621 6516575226946809989835233)
                  ·
                    refine ⟨4887431420210107492376425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516575226946809989835233 4887431420210107492376425)
                    ·
                      refine ⟨3665573565157580619282319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887431420210107492376425 3665573565157580619282319)
                      ·
                        rfl

theorem cell23_7138679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_7138679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138679 prefixEnd_7138679 := by exact prefixLift 7138679
  have htrace : WordTrace (prefixWord ++ tailWord_7138679) baseStart_7138679 baseEnd_7138679 := by
    simpa [prefixWord, tailWord_7138679, baseEnd_7138679] using wordTrace_append hprefix tailTrace_7138679
  have hstable : (prefixWord ++ tailWord_7138679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138679).length < 2 ^ (prefixWord ++ tailWord_7138679).sum := by decide
  have hdescent : baseEnd_7138679 < baseStart_7138679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138690 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7138690 : Nat := 118140960795 + 7138690 * 2 ^ 59
def prefixEnd_7138690 : Nat := 4983230072969 + 3 ^ 40 * 7138690 * 2
def baseEnd_7138690 : Nat := 3665579213444780076244769

theorem tailTrace_7138690 : CollatzResearch.WordTrace tailWord_7138690 prefixEnd_7138690 3665579213444780076244769 := by
  unfold tailWord_7138690
  simp only [CollatzResearch.WordTrace]
  refine ⟨65092353626938199008085381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173579609671835197354894349 65092353626938199008085381)
  ·
    refine ⟨12204816305050912314016009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65092353626938199008085381 12204816305050912314016009)
    ·
      refine ⟨9153612228788184235512007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12204816305050912314016009 9153612228788184235512007)
      ·
        refine ⟨13730418343182276353268011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9153612228788184235512007 13730418343182276353268011)
        ·
          refine ⟨20595627514773414529902017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13730418343182276353268011 20595627514773414529902017)
          ·
            refine ⟨15446720636080060897426513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20595627514773414529902017 15446720636080060897426513)
            ·
              refine ⟨11585040477060045673069885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15446720636080060897426513 11585040477060045673069885)
              ·
                refine ⟨4344390178897517127401207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11585040477060045673069885 4344390178897517127401207)
                ·
                  refine ⟨6516585268346275691101811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344390178897517127401207 6516585268346275691101811)
                  ·
                    refine ⟨9774877902519413536652717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6516585268346275691101811 9774877902519413536652717)
                    ·
                      refine ⟨3665579213444780076244769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774877902519413536652717 3665579213444780076244769)
                      ·
                        rfl

theorem cell23_7138690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7138690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138690 prefixEnd_7138690 := by exact prefixLift 7138690
  have htrace : WordTrace (prefixWord ++ tailWord_7138690) baseStart_7138690 baseEnd_7138690 := by
    simpa [prefixWord, tailWord_7138690, baseEnd_7138690] using wordTrace_append hprefix tailTrace_7138690
  have hstable : (prefixWord ++ tailWord_7138690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138690).length < 2 ^ (prefixWord ++ tailWord_7138690).sum := by decide
  have hdescent : baseEnd_7138690 < baseStart_7138690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138692 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_7138692 : Nat := 118140960795 + 7138692 * 2 ^ 59
def prefixEnd_7138692 : Nat := 4983230072969 + 3 ^ 40 * 7138692 * 2
def baseEnd_7138692 : Nat := 3665580240406089068419759

theorem tailTrace_7138692 : CollatzResearch.WordTrace tailWord_7138692 prefixEnd_7138692 3665580240406089068419759 := by
  unfold tailWord_7138692
  simp only [CollatzResearch.WordTrace]
  refine ⟨130184743726872775186957165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173579658302497033582609553 130184743726872775186957165)
  ·
    refine ⟨48819278897577290695108937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130184743726872775186957165 48819278897577290695108937)
    ·
      refine ⟨36614459173182968021331703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48819278897577290695108937 36614459173182968021331703)
      ·
        refine ⟨54921688759774452031997555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36614459173182968021331703 54921688759774452031997555)
        ·
          refine ⟨82382533139661678047996333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54921688759774452031997555 82382533139661678047996333)
          ·
            refine ⟨30893449927373129267998625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82382533139661678047996333 30893449927373129267998625)
            ·
              refine ⟨23170087445529846950998969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30893449927373129267998625 23170087445529846950998969)
              ·
                refine ⟨17377565584147385213249227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23170087445529846950998969 17377565584147385213249227)
                ·
                  refine ⟨26066348376221077819873841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17377565584147385213249227 26066348376221077819873841)
                  ·
                    refine ⟨19549761282165808364905381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26066348376221077819873841 19549761282165808364905381)
                    ·
                      refine ⟨3665580240406089068419759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19549761282165808364905381 3665580240406089068419759)
                      ·
                        rfl

theorem cell23_7138692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_7138692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138692 prefixEnd_7138692 := by exact prefixLift 7138692
  have htrace : WordTrace (prefixWord ++ tailWord_7138692) baseStart_7138692 baseEnd_7138692 := by
    simpa [prefixWord, tailWord_7138692, baseEnd_7138692] using wordTrace_append hprefix tailTrace_7138692
  have hstable : (prefixWord ++ tailWord_7138692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138692).length < 2 ^ (prefixWord ++ tailWord_7138692).sum := by decide
  have hdescent : baseEnd_7138692 < baseStart_7138692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138696 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_7138696 : Nat := 118140960795 + 7138696 * 2 ^ 59
def prefixEnd_7138696 : Nat := 4983230072969 + 3 ^ 40 * 7138696 * 2
def baseEnd_7138696 : Nat := 3665582294328707052769741

theorem tailTrace_7138696 : CollatzResearch.WordTrace tailWord_7138696 prefixEnd_7138696 3665582294328707052769741 := by
  unfold tailWord_7138696
  simp only [CollatzResearch.WordTrace]
  refine ⟨130184816672865529528529971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173579755563820706038039961 130184816672865529528529971)
  ·
    refine ⟨195277225009298294292794957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130184816672865529528529971 195277225009298294292794957)
    ·
      refine ⟨73228959378486860359798109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195277225009298294292794957 73228959378486860359798109)
      ·
        refine ⟨27460859766932572634924291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73228959378486860359798109 27460859766932572634924291)
        ·
          refine ⟨41191289650398858952386437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27460859766932572634924291 41191289650398858952386437)
          ·
            refine ⟨7723366809449786053572457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41191289650398858952386437 7723366809449786053572457)
            ·
              refine ⟨5792525107087339540179343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7723366809449786053572457 5792525107087339540179343)
              ·
                refine ⟨8688787660631009310269015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792525107087339540179343 8688787660631009310269015)
                ·
                  refine ⟨13033181490946513965403523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8688787660631009310269015 13033181490946513965403523)
                  ·
                    refine ⟨19549772236419770948105285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13033181490946513965403523 19549772236419770948105285)
                    ·
                      refine ⟨3665582294328707052769741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19549772236419770948105285 3665582294328707052769741)
                      ·
                        rfl

theorem cell23_7138696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_7138696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138696 prefixEnd_7138696 := by exact prefixLift 7138696
  have htrace : WordTrace (prefixWord ++ tailWord_7138696) baseStart_7138696 baseEnd_7138696 := by
    simpa [prefixWord, tailWord_7138696, baseEnd_7138696] using wordTrace_append hprefix tailTrace_7138696
  have hstable : (prefixWord ++ tailWord_7138696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138696).length < 2 ^ (prefixWord ++ tailWord_7138696).sum := by decide
  have hdescent : baseEnd_7138696 < baseStart_7138696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138702 : List Nat := [4, 1, 1, 4, 2, 1, 10]
def baseStart_7138702 : Nat := 118140960795 + 7138702 * 2 ^ 59
def prefixEnd_7138702 : Nat := 4983230072969 + 3 ^ 40 * 7138702 * 2
def baseEnd_7138702 : Nat := 45254140434723876904873

theorem tailTrace_7138702 : CollatzResearch.WordTrace tailWord_7138702 prefixEnd_7138702 45254140434723876904873 := by
  unfold tailWord_7138702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546231522963665260222295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173579901455806214721185573 32546231522963665260222295)
  ·
    refine ⟨48819347284445497890333443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32546231522963665260222295 48819347284445497890333443)
    ·
      refine ⟨73229020926668246835500165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48819347284445497890333443 73229020926668246835500165)
      ·
        refine ⟨13730441423750296281656281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73229020926668246835500165 13730441423750296281656281)
        ·
          refine ⟨10297831067812722211242211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13730441423750296281656281 10297831067812722211242211)
          ·
            refine ⟨15446746601719083316863317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10297831067812722211242211 15446746601719083316863317)
            ·
              refine ⟨45254140434723876904873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15446746601719083316863317 45254140434723876904873)
              ·
                rfl

theorem cell23_7138702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 10].length) (baseStart_7138702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138702 prefixEnd_7138702 := by exact prefixLift 7138702
  have htrace : WordTrace (prefixWord ++ tailWord_7138702) baseStart_7138702 baseEnd_7138702 := by
    simpa [prefixWord, tailWord_7138702, baseEnd_7138702] using wordTrace_append hprefix tailTrace_7138702
  have hstable : (prefixWord ++ tailWord_7138702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138702).length < 2 ^ (prefixWord ++ tailWord_7138702).sum := by decide
  have hdescent : baseEnd_7138702 < baseStart_7138702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138706 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_7138706 : Nat := 118140960795 + 7138706 * 2 ^ 59
def prefixEnd_7138706 : Nat := 4983230072969 + 3 ^ 40 * 7138706 * 2
def baseEnd_7138706 : Nat := 1221862476378417337881565

theorem tailTrace_7138706 : CollatzResearch.WordTrace tailWord_7138706 prefixEnd_7138706 1221862476378417337881565 := by
  unfold tailWord_7138706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65092499518923707691230993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173579998717129887176615981 65092499518923707691230993)
  ·
    refine ⟨48819374639192780768423245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65092499518923707691230993 48819374639192780768423245)
    ·
      refine ⟨18307265489697292788158717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48819374639192780768423245 18307265489697292788158717)
      ·
        refine ⟨6865224558636484795559519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18307265489697292788158717 6865224558636484795559519)
        ·
          refine ⟨10297836837954727193339279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6865224558636484795559519 10297836837954727193339279)
          ·
            refine ⟨15446755256932090790008919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10297836837954727193339279 15446755256932090790008919)
            ·
              refine ⟨23170132885398136185013379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15446755256932090790008919 23170132885398136185013379)
              ·
                refine ⟨34755199328097204277520069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23170132885398136185013379 34755199328097204277520069)
                ·
                  refine ⟨6516599874018225802035013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34755199328097204277520069 6516599874018225802035013)
                  ·
                    refine ⟨1221862476378417337881565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516599874018225802035013 1221862476378417337881565)
                    ·
                      rfl

theorem cell23_7138706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_7138706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138706 prefixEnd_7138706 := by exact prefixLift 7138706
  have htrace : WordTrace (prefixWord ++ tailWord_7138706) baseStart_7138706 baseEnd_7138706 := by
    simpa [prefixWord, tailWord_7138706, baseEnd_7138706] using wordTrace_append hprefix tailTrace_7138706
  have hstable : (prefixWord ++ tailWord_7138706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138706).length < 2 ^ (prefixWord ++ tailWord_7138706).sum := by decide
  have hdescent : baseEnd_7138706 < baseStart_7138706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138735 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_7138735 : Nat := 118140960795 + 7138735 * 2 ^ 59
def prefixEnd_7138735 : Nat := 4983230072969 + 3 ^ 40 * 7138735 * 2
def baseEnd_7138735 : Nat := 3665602320074232400182061

theorem tailTrace_7138735 : CollatzResearch.WordTrace tailWord_7138735 prefixEnd_7138735 3665602320074232400182061 := by
  unfold tailWord_7138735
  simp only [CollatzResearch.WordTrace]
  refine ⟨260371055792589768717729659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173580703861726512478486439 260371055792589768717729659)
  ·
    refine ⟨390556583688884653076594489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260371055792589768717729659 390556583688884653076594489)
    ·
      refine ⟨292917437766663489807445867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390556583688884653076594489 292917437766663489807445867)
      ·
        refine ⟨439376156649995234711168801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292917437766663489807445867 439376156649995234711168801)
        ·
          refine ⟨329532117487496426033376601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439376156649995234711168801 329532117487496426033376601)
          ·
            refine ⟨247149088115622319525032451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329532117487496426033376601 247149088115622319525032451)
            ·
              refine ⟨370723632173433479287548677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247149088115622319525032451 370723632173433479287548677)
              ·
                refine ⟨69510681032518777366415377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370723632173433479287548677 69510681032518777366415377)
                ·
                  refine ⟨52133010774389083024811533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69510681032518777366415377 52133010774389083024811533)
                  ·
                    refine ⟨19549879040395906134304325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52133010774389083024811533 19549879040395906134304325)
                    ·
                      refine ⟨3665602320074232400182061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19549879040395906134304325 3665602320074232400182061)
                      ·
                        rfl

theorem cell23_7138735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_7138735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138735 prefixEnd_7138735 := by exact prefixLift 7138735
  have htrace : WordTrace (prefixWord ++ tailWord_7138735) baseStart_7138735 baseEnd_7138735 := by
    simpa [prefixWord, tailWord_7138735, baseEnd_7138735] using wordTrace_append hprefix tailTrace_7138735
  have hstable : (prefixWord ++ tailWord_7138735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138735).length < 2 ^ (prefixWord ++ tailWord_7138735).sum := by decide
  have hdescent : baseEnd_7138735 < baseStart_7138735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138755 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_7138755 : Nat := 118140960795 + 7138755 * 2 ^ 59
def prefixEnd_7138755 : Nat := 4983230072969 + 3 ^ 40 * 7138755 * 2
def baseEnd_7138755 : Nat := 3665612589687322321931969

theorem tailTrace_7138755 : CollatzResearch.WordTrace tailWord_7138755 prefixEnd_7138755 3665612589687322321931969 := by
  unfold tailWord_7138755
  simp only [CollatzResearch.WordTrace]
  refine ⟨260371785252517312133457719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173581190168344874755638479 260371785252517312133457719)
  ·
    refine ⟨390557677878775968200186579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260371785252517312133457719 390557677878775968200186579)
    ·
      refine ⟨585836516818163952300279869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390557677878775968200186579 585836516818163952300279869)
      ·
        refine ⟨219688693806811482112604951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585836516818163952300279869 219688693806811482112604951)
        ·
          refine ⟨329533040710217223168907427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219688693806811482112604951 329533040710217223168907427)
          ·
            refine ⟨494299561065325834753361141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329533040710217223168907427 494299561065325834753361141)
            ·
              refine ⟨46340583849874297008127607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 494299561065325834753361141 46340583849874297008127607)
              ·
                refine ⟨69510875774811445512191411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46340583849874297008127607 69510875774811445512191411)
                ·
                  refine ⟨104266313662217168268287117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69510875774811445512191411 104266313662217168268287117)
                  ·
                    refine ⟨39099867623331438100607669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104266313662217168268287117 39099867623331438100607669)
                    ·
                      refine ⟨3665612589687322321931969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39099867623331438100607669 3665612589687322321931969)
                      ·
                        rfl

theorem cell23_7138755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_7138755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138755 prefixEnd_7138755 := by exact prefixLift 7138755
  have htrace : WordTrace (prefixWord ++ tailWord_7138755) baseStart_7138755 baseEnd_7138755 := by
    simpa [prefixWord, tailWord_7138755, baseEnd_7138755] using wordTrace_append hprefix tailTrace_7138755
  have hstable : (prefixWord ++ tailWord_7138755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138755).length < 2 ^ (prefixWord ++ tailWord_7138755).sum := by decide
  have hdescent : baseEnd_7138755 < baseStart_7138755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138820 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7138820 : Nat := 118140960795 + 7138820 * 2 ^ 59
def prefixEnd_7138820 : Nat := 4983230072969 + 3 ^ 40 * 7138820 * 2
def baseEnd_7138820 : Nat := 3665645965929864567619171

theorem tailTrace_7138820 : CollatzResearch.WordTrace tailWord_7138820 prefixEnd_7138820 3665645965929864567619171 := by
  unfold tailWord_7138820
  simp only [CollatzResearch.WordTrace]
  refine ⟨130187077998640914117286957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173582770664854552156382609 130187077998640914117286957)
  ·
    refine ⟨48820154249490342793982609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130187077998640914117286957 48820154249490342793982609)
    ·
      refine ⟨36615115687117757095486957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48820154249490342793982609 36615115687117757095486957)
      ·
        refine ⟨13730668382669158910807609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36615115687117757095486957 13730668382669158910807609)
        ·
          refine ⟨10298001287001869183105707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13730668382669158910807609 10298001287001869183105707)
          ·
            refine ⟨15447001930502803774658561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298001287001869183105707 15447001930502803774658561)
            ·
              refine ⟨11585251447877102830993921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15447001930502803774658561 11585251447877102830993921)
              ·
                refine ⟨8688938585907827123245441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11585251447877102830993921 8688938585907827123245441)
                ·
                  refine ⟨6516703939430870342434081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688938585907827123245441 6516703939430870342434081)
                  ·
                    refine ⟨4887527954573152756825561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516703939430870342434081 4887527954573152756825561)
                    ·
                      refine ⟨3665645965929864567619171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887527954573152756825561 3665645965929864567619171)
                      ·
                        rfl

theorem cell23_7138820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7138820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138820 prefixEnd_7138820 := by exact prefixLift 7138820
  have htrace : WordTrace (prefixWord ++ tailWord_7138820) baseStart_7138820 baseEnd_7138820 := by
    simpa [prefixWord, tailWord_7138820, baseEnd_7138820] using wordTrace_append hprefix tailTrace_7138820
  have hstable : (prefixWord ++ tailWord_7138820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138820).length < 2 ^ (prefixWord ++ tailWord_7138820).sum := by decide
  have hdescent : baseEnd_7138820 < baseStart_7138820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138826 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_7138826 : Nat := 118140960795 + 7138826 * 2 ^ 59
def prefixEnd_7138826 : Nat := 4983230072969 + 3 ^ 40 * 7138826 * 2
def baseEnd_7138826 : Nat := 407294338534865727127127

theorem tailTrace_7138826 : CollatzResearch.WordTrace tailWord_7138826 prefixEnd_7138826 407294338534865727127127 := by
  unfold tailWord_7138826
  simp only [CollatzResearch.WordTrace]
  refine ⟨65093593708815022814823083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173582916556840060839528221 65093593708815022814823083)
  ·
    refine ⟨97640390563222534222234625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65093593708815022814823083 97640390563222534222234625)
    ·
      refine ⟨73230292922416900666675969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97640390563222534222234625 73230292922416900666675969)
      ·
        refine ⟨54922719691812675500006977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73230292922416900666675969 54922719691812675500006977)
        ·
          refine ⟨41192039768859506625005233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54922719691812675500006977 41192039768859506625005233)
          ·
            refine ⟨30894029826644629968753925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41192039768859506625005233 30894029826644629968753925)
            ·
              refine ⟨5792630592495868119141361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30894029826644629968753925 5792630592495868119141361)
              ·
                refine ⟨4344472944371901089356021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792630592495868119141361 4344472944371901089356021)
                ·
                  refine ⟨407294338534865727127127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4344472944371901089356021 407294338534865727127127)
                  ·
                    rfl

theorem cell23_7138826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_7138826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138826 prefixEnd_7138826 := by exact prefixLift 7138826
  have htrace : WordTrace (prefixWord ++ tailWord_7138826) baseStart_7138826 baseEnd_7138826 := by
    simpa [prefixWord, tailWord_7138826, baseEnd_7138826] using wordTrace_append hprefix tailTrace_7138826
  have hstable : (prefixWord ++ tailWord_7138826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138826).length < 2 ^ (prefixWord ++ tailWord_7138826).sum := by decide
  have hdescent : baseEnd_7138826 < baseStart_7138826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138842 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_7138842 : Nat := 118140960795 + 7138842 * 2 ^ 59
def prefixEnd_7138842 : Nat := 4983230072969 + 3 ^ 40 * 7138842 * 2
def baseEnd_7138842 : Nat := 3665657262504263481544069

theorem tailTrace_7138842 : CollatzResearch.WordTrace tailWord_7138842 prefixEnd_7138842 3665657262504263481544069 := by
  unfold tailWord_7138842
  simp only [CollatzResearch.WordTrace]
  refine ⟨65093739600800531497968695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173583305602134750661249853 65093739600800531497968695)
  ·
    refine ⟨97640609401200797246953043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65093739600800531497968695 97640609401200797246953043)
    ·
      refine ⟨146460914101801195870429565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97640609401200797246953043 146460914101801195870429565)
      ·
        refine ⟨54922842788175448451411087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146460914101801195870429565 54922842788175448451411087)
        ·
          refine ⟨82384264182263172677116631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54922842788175448451411087 82384264182263172677116631)
          ·
            refine ⟨123576396273394759015674947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82384264182263172677116631 123576396273394759015674947)
            ·
              refine ⟨185364594410092138523512421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123576396273394759015674947 185364594410092138523512421)
              ·
                refine ⟨34755861451892275973158579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185364594410092138523512421 34755861451892275973158579)
                ·
                  refine ⟨52133792177838413959737869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34755861451892275973158579 52133792177838413959737869)
                  ·
                    refine ⟨19550172066689405234901701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52133792177838413959737869 19550172066689405234901701)
                    ·
                      refine ⟨3665657262504263481544069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19550172066689405234901701 3665657262504263481544069)
                      ·
                        rfl

theorem cell23_7138842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_7138842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138842 prefixEnd_7138842 := by exact prefixLift 7138842
  have htrace : WordTrace (prefixWord ++ tailWord_7138842) baseStart_7138842 baseEnd_7138842 := by
    simpa [prefixWord, tailWord_7138842, baseEnd_7138842] using wordTrace_append hprefix tailTrace_7138842
  have hstable : (prefixWord ++ tailWord_7138842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138842).length < 2 ^ (prefixWord ++ tailWord_7138842).sum := by decide
  have hdescent : baseEnd_7138842 < baseStart_7138842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138872 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_7138872 : Nat := 118140960795 + 7138872 * 2 ^ 59
def prefixEnd_7138872 : Nat := 4983230072969 + 3 ^ 40 * 7138872 * 2
def baseEnd_7138872 : Nat := 3665672666923898364168931

theorem tailTrace_7138872 : CollatzResearch.WordTrace tailWord_7138872 prefixEnd_7138872 3665672666923898364168931 := by
  unfold tailWord_7138872
  simp only [CollatzResearch.WordTrace]
  refine ⟨130188026296546720557733435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173584035062062294076977913 130188026296546720557733435)
  ·
    refine ⟨195282039444820080836600153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130188026296546720557733435 195282039444820080836600153)
    ·
      refine ⟨146461529583615060627450115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195282039444820080836600153 146461529583615060627450115)
      ·
        refine ⟨219692294375422590941175173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146461529583615060627450115 219692294375422590941175173)
        ·
          refine ⟨41192305195391735801470345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219692294375422590941175173 41192305195391735801470345)
          ·
            refine ⟨30894228896543801851102759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41192305195391735801470345 30894228896543801851102759)
            ·
              refine ⟨46341343344815702776654139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30894228896543801851102759 46341343344815702776654139)
              ·
                refine ⟨69512015017223554164981209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46341343344815702776654139 69512015017223554164981209)
                ·
                  refine ⟨52134011262917665623735907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69512015017223554164981209 52134011262917665623735907)
                  ·
                    refine ⟨78201016894376498435603861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52134011262917665623735907 78201016894376498435603861)
                    ·
                      refine ⟨3665672666923898364168931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78201016894376498435603861 3665672666923898364168931)
                      ·
                        rfl

theorem cell23_7138872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_7138872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138872 prefixEnd_7138872 := by exact prefixLift 7138872
  have htrace : WordTrace (prefixWord ++ tailWord_7138872) baseStart_7138872 baseEnd_7138872 := by
    simpa [prefixWord, tailWord_7138872, baseEnd_7138872] using wordTrace_append hprefix tailTrace_7138872
  have hstable : (prefixWord ++ tailWord_7138872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138872).length < 2 ^ (prefixWord ++ tailWord_7138872).sum := by decide
  have hdescent : baseEnd_7138872 < baseStart_7138872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138920 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 1, 4]
def baseStart_7138920 : Nat := 118140960795 + 7138920 * 2 ^ 59
def prefixEnd_7138920 : Nat := 4983230072969 + 3 ^ 40 * 7138920 * 2
def baseEnd_7138920 : Nat := 1221899104665104725456237

theorem tailTrace_7138920 : CollatzResearch.WordTrace tailWord_7138920 prefixEnd_7138920 1221899104665104725456237 := by
  unfold tailWord_7138920
  simp only [CollatzResearch.WordTrace]
  refine ⟨130188901648459772656607107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173585202197946363542142809 130188901648459772656607107)
  ·
    refine ⟨195283352472689658984910661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130188901648459772656607107 195283352472689658984910661)
    ·
      refine ⟨36615628588629311059670749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195283352472689658984910661 36615628588629311059670749)
      ·
        refine ⟨13730860720735991647376531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36615628588629311059670749 13730860720735991647376531)
        ·
          refine ⟨20596291081103987471064797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13730860720735991647376531 20596291081103987471064797)
          ·
            refine ⟨7723609155413995301649299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20596291081103987471064797 7723609155413995301649299)
            ·
              refine ⟨11585413733120992952473949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723609155413995301649299 11585413733120992952473949)
              ·
                refine ⟨4344530149920372357177731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11585413733120992952473949 4344530149920372357177731)
                ·
                  refine ⟨6516795224880558535766597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344530149920372357177731 6516795224880558535766597)
                  ·
                    refine ⟨1221899104665104725456237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516795224880558535766597 1221899104665104725456237)
                    ·
                      rfl

theorem cell23_7138920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_7138920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138920 prefixEnd_7138920 := by exact prefixLift 7138920
  have htrace : WordTrace (prefixWord ++ tailWord_7138920) baseStart_7138920 baseEnd_7138920 := by
    simpa [prefixWord, tailWord_7138920, baseEnd_7138920] using wordTrace_append hprefix tailTrace_7138920
  have hstable : (prefixWord ++ tailWord_7138920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138920).length < 2 ^ (prefixWord ++ tailWord_7138920).sum := by decide
  have hdescent : baseEnd_7138920 < baseStart_7138920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138949 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_7138949 : Nat := 118140960795 + 7138949 * 2 ^ 59
def prefixEnd_7138949 : Nat := 4983230072969 + 3 ^ 40 * 7138949 * 2
def baseEnd_7138949 : Nat := 3665712204934294562906077

theorem tailTrace_7138949 : CollatzResearch.WordTrace tailWord_7138949 prefixEnd_7138949 3665712204934294562906077 := by
  unfold tailWord_7138949
  simp only [CollatzResearch.WordTrace]
  refine ⟨260378861013814483266019901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173585907342542988844013267 260378861013814483266019901)
  ·
    refine ⟨97642072880180431224757463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260378861013814483266019901 97642072880180431224757463)
    ·
      refine ⟨146463109320270646837136195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97642072880180431224757463 146463109320270646837136195)
      ·
        refine ⟨219694663980405970255704293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146463109320270646837136195 219694663980405970255704293)
        ·
          refine ⟨41192749496326119422944555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219694663980405970255704293 41192749496326119422944555)
          ·
            refine ⟨61789124244489179134416833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41192749496326119422944555 61789124244489179134416833)
            ·
              refine ⟨46341843183366884350812625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61789124244489179134416833 46341843183366884350812625)
              ·
                refine ⟨34756382387525163263109469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46341843183366884350812625 34756382387525163263109469)
                ·
                  refine ⟨13033643395321936223666051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34756382387525163263109469 13033643395321936223666051)
                  ·
                    refine ⟨19550465092982904335499077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13033643395321936223666051 19550465092982904335499077)
                    ·
                      refine ⟨3665712204934294562906077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19550465092982904335499077 3665712204934294562906077)
                      ·
                        rfl

theorem cell23_7138949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_7138949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138949 prefixEnd_7138949 := by exact prefixLift 7138949
  have htrace : WordTrace (prefixWord ++ tailWord_7138949) baseStart_7138949 baseEnd_7138949 := by
    simpa [prefixWord, tailWord_7138949, baseEnd_7138949] using wordTrace_append hprefix tailTrace_7138949
  have hstable : (prefixWord ++ tailWord_7138949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138949).length < 2 ^ (prefixWord ++ tailWord_7138949).sum := by decide
  have hdescent : baseEnd_7138949 < baseStart_7138949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138979 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4]
def baseStart_7138979 : Nat := 118140960795 + 7138979 * 2 ^ 59
def prefixEnd_7138979 : Nat := 4983230072969 + 3 ^ 40 * 7138979 * 2
def baseEnd_7138979 : Nat := 3665727609353929445530939

theorem tailTrace_7138979 : CollatzResearch.WordTrace tailWord_7138979 prefixEnd_7138979 3665727609353929445530939 := by
  unfold tailWord_7138979
  simp only [CollatzResearch.WordTrace]
  refine ⟨260379955203705798389611991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173586636802470532259741327 260379955203705798389611991)
  ·
    refine ⟨390569932805558697584417987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260379955203705798389611991 390569932805558697584417987)
    ·
      refine ⟨585854899208338046376626981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390569932805558697584417987 585854899208338046376626981)
      ·
        refine ⟨109847793601563383695617559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 585854899208338046376626981 109847793601563383695617559)
        ·
          refine ⟨164771690402345075543426339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109847793601563383695617559 164771690402345075543426339)
          ·
            refine ⟨247157535603517613315139509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164771690402345075543426339 247157535603517613315139509)
            ·
              refine ⟨23171018962829776248294329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247157535603517613315139509 23171018962829776248294329)
              ·
                refine ⟨17378264222122332186220747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23171018962829776248294329 17378264222122332186220747)
                ·
                  refine ⟨26067396333183498279331121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17378264222122332186220747 26067396333183498279331121)
                  ·
                    refine ⟨19550547249887623709498341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26067396333183498279331121 19550547249887623709498341)
                    ·
                      refine ⟨3665727609353929445530939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19550547249887623709498341 3665727609353929445530939)
                      ·
                        rfl

theorem cell23_7138979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_7138979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138979 prefixEnd_7138979 := by exact prefixLift 7138979
  have htrace : WordTrace (prefixWord ++ tailWord_7138979) baseStart_7138979 baseEnd_7138979 := by
    simpa [prefixWord, tailWord_7138979, baseEnd_7138979] using wordTrace_append hprefix tailTrace_7138979
  have hstable : (prefixWord ++ tailWord_7138979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138979).length < 2 ^ (prefixWord ++ tailWord_7138979).sum := by decide
  have hdescent : baseEnd_7138979 < baseStart_7138979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139006 : List Nat := [4, 2, 1, 1, 2, 4, 1, 8]
def baseStart_7139006 : Nat := 118140960795 + 7139006 * 2 ^ 59
def prefixEnd_7139006 : Nat := 4983230072969 + 3 ^ 40 * 7139006 * 2
def baseEnd_7139006 : Nat := 135768202715985216292345

theorem tailTrace_7139006 : CollatzResearch.WordTrace tailWord_7139006 prefixEnd_7139006 135768202715985216292345 := by
  unfold tailWord_7139006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547617496825997750105609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173587293316405321333896581 32547617496825997750105609)
  ·
    refine ⟨24410713122619498312579207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32547617496825997750105609 24410713122619498312579207)
    ·
      refine ⟨36616069683929247468868811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24410713122619498312579207 36616069683929247468868811)
      ·
        refine ⟨54924104525893871203303217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36616069683929247468868811 54924104525893871203303217)
        ·
          refine ⟨41193078394420403402477413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54924104525893871203303217 41193078394420403402477413)
          ·
            refine ⟨7723702198953825637964515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41193078394420403402477413 7723702198953825637964515)
            ·
              refine ⟨11585553298430738456946773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723702198953825637964515 11585553298430738456946773)
              ·
                refine ⟨135768202715985216292345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11585553298430738456946773 135768202715985216292345)
                ·
                  rfl

theorem cell23_7139006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_7139006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139006 prefixEnd_7139006 := by exact prefixLift 7139006
  have htrace : WordTrace (prefixWord ++ tailWord_7139006) baseStart_7139006 baseEnd_7139006 := by
    simpa [prefixWord, tailWord_7139006, baseEnd_7139006] using wordTrace_append hprefix tailTrace_7139006
  have hstable : (prefixWord ++ tailWord_7139006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139006).length < 2 ^ (prefixWord ++ tailWord_7139006).sum := by decide
  have hdescent : baseEnd_7139006 < baseStart_7139006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139016 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_7139016 : Nat := 118140960795 + 7139016 * 2 ^ 59
def prefixEnd_7139016 : Nat := 4983230072969 + 3 ^ 40 * 7139016 * 2
def baseEnd_7139016 : Nat := 3665746608138145800768269

theorem tailTrace_7139016 : CollatzResearch.WordTrace tailWord_7139016 prefixEnd_7139016 3665746608138145800768269 := by
  unfold tailWord_7139016
  simp only [CollatzResearch.WordTrace]
  refine ⟨130190652352285876854354451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173587536469714502472472601 130190652352285876854354451)
  ·
    refine ⟨195285978528428815281531677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130190652352285876854354451 195285978528428815281531677)
    ·
      refine ⟨73232241948160805730574379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195285978528428815281531677 73232241948160805730574379)
      ·
        refine ⟨109848362922241208595861569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73232241948160805730574379 109848362922241208595861569)
        ·
          refine ⟨82386272191680906446896177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109848362922241208595861569 82386272191680906446896177)
          ·
            refine ⟨61789704143760679835172133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82386272191680906446896177 61789704143760679835172133)
            ·
              refine ⟨11585569526955127469094775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61789704143760679835172133 11585569526955127469094775)
              ·
                refine ⟨17378354290432691203642163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11585569526955127469094775 17378354290432691203642163)
                ·
                  refine ⟨26067531435649036805463245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17378354290432691203642163 26067531435649036805463245)
                  ·
                    refine ⟨9775324288368388802048717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26067531435649036805463245 9775324288368388802048717)
                    ·
                      refine ⟨3665746608138145800768269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9775324288368388802048717 3665746608138145800768269)
                      ·
                        rfl

theorem cell23_7139016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_7139016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139016 prefixEnd_7139016 := by exact prefixLift 7139016
  have htrace : WordTrace (prefixWord ++ tailWord_7139016) baseStart_7139016 baseEnd_7139016 := by
    simpa [prefixWord, tailWord_7139016, baseEnd_7139016] using wordTrace_append hprefix tailTrace_7139016
  have hstable : (prefixWord ++ tailWord_7139016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139016).length < 2 ^ (prefixWord ++ tailWord_7139016).sum := by decide
  have hdescent : baseEnd_7139016 < baseStart_7139016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139059 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 3]
def baseStart_7139059 : Nat := 118140960795 + 7139059 * 2 ^ 59
def prefixEnd_7139059 : Nat := 4983230072969 + 3 ^ 40 * 7139059 * 2
def baseEnd_7139059 : Nat := 3665768687806289132530571

theorem tailTrace_7139059 : CollatzResearch.WordTrace tailWord_7139059 prefixEnd_7139059 3665768687806289132530571 := by
  unfold tailWord_7139059
  simp only [CollatzResearch.WordTrace]
  refine ⟨260382873043415972052524231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173588582028943981368349487 260382873043415972052524231)
  ·
    refine ⟨390574309565123958078786347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260382873043415972052524231 390574309565123958078786347)
    ·
      refine ⟨585861464347685937118179521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390574309565123958078786347 585861464347685937118179521)
      ·
        refine ⟨439396098260764452838634641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585861464347685937118179521 439396098260764452838634641)
        ·
          refine ⟨329547073695573339628975981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439396098260764452838634641 329547073695573339628975981)
          ·
            refine ⟨123580152635840002360865993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329547073695573339628975981 123580152635840002360865993)
            ·
              refine ⟨92685114476880001770649495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123580152635840002360865993 92685114476880001770649495)
              ·
                refine ⟨139027671715320002655974243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92685114476880001770649495 139027671715320002655974243)
                ·
                  refine ⟨208541507572980003983961365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139027671715320002655974243 208541507572980003983961365)
                  ·
                    refine ⟨9775383167483437686748189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208541507572980003983961365 9775383167483437686748189)
                    ·
                      refine ⟨3665768687806289132530571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9775383167483437686748189 3665768687806289132530571)
                      ·
                        rfl

theorem cell23_7139059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_7139059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139059 prefixEnd_7139059 := by exact prefixLift 7139059
  have htrace : WordTrace (prefixWord ++ tailWord_7139059) baseStart_7139059 baseEnd_7139059 := by
    simpa [prefixWord, tailWord_7139059, baseEnd_7139059] using wordTrace_append hprefix tailTrace_7139059
  have hstable : (prefixWord ++ tailWord_7139059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139059).length < 2 ^ (prefixWord ++ tailWord_7139059).sum := by decide
  have hdescent : baseEnd_7139059 < baseStart_7139059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139069 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_7139069 : Nat := 118140960795 + 7139069 * 2 ^ 59
def prefixEnd_7139069 : Nat := 4983230072969 + 3 ^ 40 * 7139069 * 2
def baseEnd_7139069 : Nat := 3665773822612834093405525

theorem tailTrace_7139069 : CollatzResearch.WordTrace tailWord_7139069 prefixEnd_7139069 3665773822612834093405525 := by
  unfold tailWord_7139069
  simp only [CollatzResearch.WordTrace]
  refine ⟨260383237773379743760388261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173588825182253162506925507 260383237773379743760388261)
  ·
    refine ⟨48821857082508701955072799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260383237773379743760388261 48821857082508701955072799)
    ·
      refine ⟨73232785623763052932609199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48821857082508701955072799 73232785623763052932609199)
      ·
        refine ⟨109849178435644579398913799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73232785623763052932609199 109849178435644579398913799)
        ·
          refine ⟨164773767653466869098370699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109849178435644579398913799 164773767653466869098370699)
          ·
            refine ⟨247160651480200303647556049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164773767653466869098370699 247160651480200303647556049)
            ·
              refine ⟨185370488610150227735667037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247160651480200303647556049 185370488610150227735667037)
              ·
                refine ⟨69513933228806335400875139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185370488610150227735667037 69513933228806335400875139)
                ·
                  refine ⟨104270899843209503101312709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69513933228806335400875139 104270899843209503101312709)
                  ·
                    refine ⟨19550793720601781831496133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104270899843209503101312709 19550793720601781831496133)
                    ·
                      refine ⟨3665773822612834093405525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19550793720601781831496133 3665773822612834093405525)
                      ·
                        rfl

theorem cell23_7139069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_7139069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139069 prefixEnd_7139069 := by exact prefixLift 7139069
  have htrace : WordTrace (prefixWord ++ tailWord_7139069) baseStart_7139069 baseEnd_7139069 := by
    simpa [prefixWord, tailWord_7139069, baseEnd_7139069] using wordTrace_append hprefix tailTrace_7139069
  have hstable : (prefixWord ++ tailWord_7139069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139069).length < 2 ^ (prefixWord ++ tailWord_7139069).sum := by decide
  have hdescent : baseEnd_7139069 < baseStart_7139069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139073 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_7139073 : Nat := 118140960795 + 7139073 * 2 ^ 59
def prefixEnd_7139073 : Nat := 4983230072969 + 3 ^ 40 * 7139073 * 2
def baseEnd_7139073 : Nat := 3665775876535452077755507

theorem tailTrace_7139073 : CollatzResearch.WordTrace tailWord_7139073 prefixEnd_7139073 3665775876535452077755507 := by
  unfold tailWord_7139073
  simp only [CollatzResearch.WordTrace]
  refine ⟨260383383665365252443533873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173588922443576834962355915 260383383665365252443533873)
  ·
    refine ⟨195287537749023939332650405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260383383665365252443533873 195287537749023939332650405)
    ·
      refine ⟨36616413327941988624871951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195287537749023939332650405 36616413327941988624871951)
      ·
        refine ⟨54924619991912982937307927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36616413327941988624871951 54924619991912982937307927)
        ·
          refine ⟨82386929987869474405961891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54924619991912982937307927 82386929987869474405961891)
          ·
            refine ⟨123580394981804211608942837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82386929987869474405961891 123580394981804211608942837)
            ·
              refine ⟨11585662029544144838338391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123580394981804211608942837 11585662029544144838338391)
              ·
                refine ⟨17378493044316217257507587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11585662029544144838338391 17378493044316217257507587)
                ·
                  refine ⟨26067739566474325886261381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17378493044316217257507587 26067739566474325886261381)
                  ·
                    refine ⟨4887701168713936103674009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26067739566474325886261381 4887701168713936103674009)
                    ·
                      refine ⟨3665775876535452077755507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887701168713936103674009 3665775876535452077755507)
                      ·
                        rfl

theorem cell23_7139073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_7139073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139073 prefixEnd_7139073 := by exact prefixLift 7139073
  have htrace : WordTrace (prefixWord ++ tailWord_7139073) baseStart_7139073 baseEnd_7139073 := by
    simpa [prefixWord, tailWord_7139073, baseEnd_7139073] using wordTrace_append hprefix tailTrace_7139073
  have hstable : (prefixWord ++ tailWord_7139073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139073).length < 2 ^ (prefixWord ++ tailWord_7139073).sum := by decide
  have hdescent : baseEnd_7139073 < baseStart_7139073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139085 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7139085 : Nat := 118140960795 + 7139085 * 2 ^ 59
def prefixEnd_7139085 : Nat := 4983230072969 + 3 ^ 40 * 7139085 * 2
def baseEnd_7139085 : Nat := 3665782038303306030805453

theorem tailTrace_7139085 : CollatzResearch.WordTrace tailWord_7139085 prefixEnd_7139085 3665782038303306030805453 := by
  unfold tailWord_7139085
  simp only [CollatzResearch.WordTrace]
  refine ⟨260383821341321778492970709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173589214227547852328647139 260383821341321778492970709)
  ·
    refine ⟨6102745812687229183429001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 260383821341321778492970709 6102745812687229183429001)
    ·
      refine ⟨4577059359515421887571751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6102745812687229183429001 4577059359515421887571751)
      ·
        refine ⟨6865589039273132831357627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577059359515421887571751 6865589039273132831357627)
        ·
          refine ⟨10298383558909699247036441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6865589039273132831357627 10298383558909699247036441)
          ·
            refine ⟨7723787669182274435277331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10298383558909699247036441 7723787669182274435277331)
            ·
              refine ⟨11585681503773411652915997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723787669182274435277331 11585681503773411652915997)
              ·
                refine ⟨4344630563915029369843499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11585681503773411652915997 4344630563915029369843499)
                ·
                  refine ⟨6516945845872544054765249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344630563915029369843499 6516945845872544054765249)
                  ·
                    refine ⟨4887709384404408041073937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516945845872544054765249 4887709384404408041073937)
                    ·
                      refine ⟨3665782038303306030805453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887709384404408041073937 3665782038303306030805453)
                      ·
                        rfl

theorem cell23_7139085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7139085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139085 prefixEnd_7139085 := by exact prefixLift 7139085
  have htrace : WordTrace (prefixWord ++ tailWord_7139085) baseStart_7139085 baseEnd_7139085 := by
    simpa [prefixWord, tailWord_7139085, baseEnd_7139085] using wordTrace_append hprefix tailTrace_7139085
  have hstable : (prefixWord ++ tailWord_7139085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139085).length < 2 ^ (prefixWord ++ tailWord_7139085).sum := by decide
  have hdescent : baseEnd_7139085 < baseStart_7139085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139119 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_7139119 : Nat := 118140960795 + 7139119 * 2 ^ 59
def prefixEnd_7139119 : Nat := 4983230072969 + 3 ^ 40 * 7139119 * 2
def baseEnd_7139119 : Nat := 3665799496645558897780295

theorem tailTrace_7139119 : CollatzResearch.WordTrace tailWord_7139119 prefixEnd_7139119 3665799496645558897780295 := by
  unfold tailWord_7139119
  simp only [CollatzResearch.WordTrace]
  refine ⟨260385061423198602299708411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173590040948799068199805607 260385061423198602299708411)
  ·
    refine ⟨390577592134797903449562617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260385061423198602299708411 390577592134797903449562617)
    ·
      refine ⟨292933194101098427587171963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390577592134797903449562617 292933194101098427587171963)
      ·
        refine ⟨439399791151647641380757945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292933194101098427587171963 439399791151647641380757945)
        ·
          refine ⟨329549843363735731035568459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439399791151647641380757945 329549843363735731035568459)
          ·
            refine ⟨494324765045603596553352689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329549843363735731035568459 494324765045603596553352689)
            ·
              refine ⟨370743573784202697415014517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494324765045603596553352689 370743573784202697415014517)
              ·
                refine ⟨34757210042269002882657611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370743573784202697415014517 34757210042269002882657611)
                ·
                  refine ⟨52135815063403504323986417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34757210042269002882657611 52135815063403504323986417)
                  ·
                    refine ⟨39101861297552628242989813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52135815063403504323986417 39101861297552628242989813)
                    ·
                      refine ⟨3665799496645558897780295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39101861297552628242989813 3665799496645558897780295)
                      ·
                        rfl

theorem cell23_7139119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_7139119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139119 prefixEnd_7139119 := by exact prefixLift 7139119
  have htrace : WordTrace (prefixWord ++ tailWord_7139119) baseStart_7139119 baseEnd_7139119 := by
    simpa [prefixWord, tailWord_7139119, baseEnd_7139119] using wordTrace_append hprefix tailTrace_7139119
  have hstable : (prefixWord ++ tailWord_7139119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139119).length < 2 ^ (prefixWord ++ tailWord_7139119).sum := by decide
  have hdescent : baseEnd_7139119 < baseStart_7139119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139124 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7139124 : Nat := 118140960795 + 7139124 * 2 ^ 59
def prefixEnd_7139124 : Nat := 4983230072969 + 3 ^ 40 * 7139124 * 2
def baseEnd_7139124 : Nat := 3665802064048831378217773

theorem tailTrace_7139124 : CollatzResearch.WordTrace tailWord_7139124 prefixEnd_7139124 3665802064048831378217773 := by
  unfold tailWord_7139124
  simp only [CollatzResearch.WordTrace]
  refine ⟨130192621894090244076820213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173590162525453658769093617 130192621894090244076820213)
  ·
    refine ⟨12205558302570960382201895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130192621894090244076820213 12205558302570960382201895)
    ·
      refine ⟨18308337453856440573302843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12205558302570960382201895 18308337453856440573302843)
      ·
        refine ⟨27462506180784660859954265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18308337453856440573302843 27462506180784660859954265)
        ·
          refine ⟨20596879635588495644965699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27462506180784660859954265 20596879635588495644965699)
          ·
            refine ⟨30895319453382743467448549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20596879635588495644965699 30895319453382743467448549)
            ·
              refine ⟨5792872397509264400146603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30895319453382743467448549 5792872397509264400146603)
              ·
                refine ⟨8689308596263896600219905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792872397509264400146603 8689308596263896600219905)
                ·
                  refine ⟨6516981447197922450164929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8689308596263896600219905 6516981447197922450164929)
                  ·
                    refine ⟨4887736085398441837623697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516981447197922450164929 4887736085398441837623697)
                    ·
                      refine ⟨3665802064048831378217773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887736085398441837623697 3665802064048831378217773)
                      ·
                        rfl

theorem cell23_7139124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7139124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139124 prefixEnd_7139124 := by exact prefixLift 7139124
  have htrace : WordTrace (prefixWord ++ tailWord_7139124) baseStart_7139124 baseEnd_7139124 := by
    simpa [prefixWord, tailWord_7139124, baseEnd_7139124] using wordTrace_append hprefix tailTrace_7139124
  have hstable : (prefixWord ++ tailWord_7139124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139124).length < 2 ^ (prefixWord ++ tailWord_7139124).sum := by decide
  have hdescent : baseEnd_7139124 < baseStart_7139124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139164 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 5]
def baseStart_7139164 : Nat := 118140960795 + 7139164 * 2 ^ 59
def prefixEnd_7139164 : Nat := 4983230072969 + 3 ^ 40 * 7139164 * 2
def baseEnd_7139164 : Nat := 407313622586112357968621

theorem tailTrace_7139164 : CollatzResearch.WordTrace tailWord_7139164 prefixEnd_7139164 407313622586112357968621 := by
  unfold tailWord_7139164
  simp only [CollatzResearch.WordTrace]
  refine ⟨130193351354017787492548273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173591135138690383323397697 130193351354017787492548273)
  ·
    refine ⟨97645013515513340619411205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130193351354017787492548273 97645013515513340619411205)
    ·
      refine ⟨18308440034158751366139601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97645013515513340619411205 18308440034158751366139601)
      ·
        refine ⟨13731330025619063524604701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18308440034158751366139601 13731330025619063524604701)
        ·
          refine ⟨5149248759607148821726763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13731330025619063524604701 5149248759607148821726763)
          ·
            refine ⟨7723873139410723232590145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149248759607148821726763 7723873139410723232590145)
            ·
              refine ⟨5792904854558042424442609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7723873139410723232590145 5792904854558042424442609)
              ·
                refine ⟨4344678640918531818331957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792904854558042424442609 4344678640918531818331957)
                ·
                  refine ⟨407313622586112357968621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4344678640918531818331957 407313622586112357968621)
                  ·
                    rfl

theorem cell23_7139164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_7139164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139164 prefixEnd_7139164 := by exact prefixLift 7139164
  have htrace : WordTrace (prefixWord ++ tailWord_7139164) baseStart_7139164 baseEnd_7139164 := by
    simpa [prefixWord, tailWord_7139164, baseEnd_7139164] using wordTrace_append hprefix tailTrace_7139164
  have hstable : (prefixWord ++ tailWord_7139164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139164).length < 2 ^ (prefixWord ++ tailWord_7139164).sum := by decide
  have hdescent : baseEnd_7139164 < baseStart_7139164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139207 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 1, 4]
def baseStart_7139207 : Nat := 118140960795 + 7139207 * 2 ^ 59
def prefixEnd_7139207 : Nat := 4983230072969 + 3 ^ 40 * 7139207 * 2
def baseEnd_7139207 : Nat := 1221948227647718184493297

theorem tailTrace_7139207 : CollatzResearch.WordTrace tailWord_7139207 prefixEnd_7139207 1221948227647718184493297 := by
  unfold tailWord_7139207
  simp only [CollatzResearch.WordTrace]
  refine ⟨260388271046879793328911875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173592180697919862219274583 260388271046879793328911875)
  ·
    refine ⟨390582406570319689993367813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260388271046879793328911875 390582406570319689993367813)
    ·
      refine ⟨73234201231934941873756465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390582406570319689993367813 73234201231934941873756465)
      ·
        refine ⟨54925650923951206405317349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73234201231934941873756465 54925650923951206405317349)
        ·
          refine ⟨10298559548240851200997003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54925650923951206405317349 10298559548240851200997003)
          ·
            refine ⟨15447839322361276801495505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298559548240851200997003 15447839322361276801495505)
            ·
              refine ⟨11585879491770957601121629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15447839322361276801495505 11585879491770957601121629)
              ·
                refine ⟨4344704809414109100420611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11585879491770957601121629 4344704809414109100420611)
                ·
                  refine ⟨6517057214121163650630917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344704809414109100420611 6517057214121163650630917)
                  ·
                    refine ⟨1221948227647718184493297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6517057214121163650630917 1221948227647718184493297)
                    ·
                      rfl

theorem cell23_7139207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_7139207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139207 prefixEnd_7139207 := by exact prefixLift 7139207
  have htrace : WordTrace (prefixWord ++ tailWord_7139207) baseStart_7139207 baseEnd_7139207 := by
    simpa [prefixWord, tailWord_7139207, baseEnd_7139207] using wordTrace_append hprefix tailTrace_7139207
  have hstable : (prefixWord ++ tailWord_7139207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139207).length < 2 ^ (prefixWord ++ tailWord_7139207).sum := by decide
  have hdescent : baseEnd_7139207 < baseStart_7139207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139220 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 6]
def baseStart_7139220 : Nat := 118140960795 + 7139220 * 2 ^ 59
def prefixEnd_7139220 : Nat := 4983230072969 + 3 ^ 40 * 7139220 * 2
def baseEnd_7139220 : Nat := 407316817576851444735259

theorem tailTrace_7139220 : CollatzResearch.WordTrace tailWord_7139220 prefixEnd_7139220 407316817576851444735259 := by
  unfold tailWord_7139220
  simp only [CollatzResearch.WordTrace]
  refine ⟨130194372597916348274567557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173592496797221797699423409 130194372597916348274567557)
  ·
    refine ⟨24411444862109315301481417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130194372597916348274567557 24411444862109315301481417)
    ·
      refine ⟨18308583646581986476111063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24411444862109315301481417 18308583646581986476111063)
      ·
        refine ⟨27462875469872979714166595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18308583646581986476111063 27462875469872979714166595)
        ·
          refine ⟨41194313204809469571249893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27462875469872979714166595 41194313204809469571249893)
          ·
            refine ⟨7723933725901775544609355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41194313204809469571249893 7723933725901775544609355)
            ·
              refine ⟨11585900588852663316914033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723933725901775544609355 11585900588852663316914033)
              ·
                refine ⟨8689425441639497487685525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11585900588852663316914033 8689425441639497487685525)
                ·
                  refine ⟨407316817576851444735259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8689425441639497487685525 407316817576851444735259)
                  ·
                    rfl

theorem cell23_7139220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_7139220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139220 prefixEnd_7139220 := by exact prefixLift 7139220
  have htrace : WordTrace (prefixWord ++ tailWord_7139220) baseStart_7139220 baseEnd_7139220 := by
    simpa [prefixWord, tailWord_7139220, baseEnd_7139220] using wordTrace_append hprefix tailTrace_7139220
  have hstable : (prefixWord ++ tailWord_7139220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139220).length < 2 ^ (prefixWord ++ tailWord_7139220).sum := by decide
  have hdescent : baseEnd_7139220 < baseStart_7139220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139256 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_7139256 : Nat := 118140960795 + 7139256 * 2 ^ 59
def prefixEnd_7139256 : Nat := 4983230072969 + 3 ^ 40 * 7139256 * 2
def baseEnd_7139256 : Nat := 3665869843495224861767165

theorem tailTrace_7139256 : CollatzResearch.WordTrace tailWord_7139256 prefixEnd_7139256 3665869843495224861767165 := by
  unfold tailWord_7139256
  simp only [CollatzResearch.WordTrace]
  refine ⟨130195029111851137348722811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173593372149134849798297081 130195029111851137348722811)
  ·
    refine ⟨195292543667776706023084217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130195029111851137348722811 195292543667776706023084217)
    ·
      refine ⟨146469407750832529517313163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195292543667776706023084217 146469407750832529517313163)
      ·
        refine ⟨219704111626248794275969745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146469407750832529517313163 219704111626248794275969745)
        ·
          refine ⟨164778083719686595706977309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219704111626248794275969745 164778083719686595706977309)
          ·
            refine ⟨61791781394882473390116491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164778083719686595706977309 61791781394882473390116491)
            ·
              refine ⟨92687672092323710085174737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61791781394882473390116491 92687672092323710085174737)
              ·
                refine ⟨69515754069242782563881053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92687672092323710085174737 69515754069242782563881053)
                ·
                  refine ⟨26068407775966043461455395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69515754069242782563881053 26068407775966043461455395)
                  ·
                    refine ⟨39102611663949065192183093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26068407775966043461455395 39102611663949065192183093)
                    ·
                      refine ⟨3665869843495224861767165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39102611663949065192183093 3665869843495224861767165)
                      ·
                        rfl

theorem cell23_7139256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_7139256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139256 prefixEnd_7139256 := by exact prefixLift 7139256
  have htrace : WordTrace (prefixWord ++ tailWord_7139256) baseStart_7139256 baseEnd_7139256 := by
    simpa [prefixWord, tailWord_7139256, baseEnd_7139256] using wordTrace_append hprefix tailTrace_7139256
  have hstable : (prefixWord ++ tailWord_7139256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139256).length < 2 ^ (prefixWord ++ tailWord_7139256).sum := by decide
  have hdescent : baseEnd_7139256 < baseStart_7139256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139276 : List Nat := [2, 2, 1, 4, 1, 2, 11]
def baseStart_7139276 : Nat := 118140960795 + 7139276 * 2 ^ 59
def prefixEnd_7139276 : Nat := 4983230072969 + 3 ^ 40 * 7139276 * 2
def baseEnd_7139276 : Nat := 45257779174176725722433

theorem tailTrace_7139276 : CollatzResearch.WordTrace tailWord_7139276 prefixEnd_7139276 45257779174176725722433 := by
  unfold tailWord_7139276
  simp only [CollatzResearch.WordTrace]
  refine ⟨130195393841814909056586841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173593858455753212075449121 130195393841814909056586841)
  ·
    refine ⟨97646545381361181792440131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130195393841814909056586841 97646545381361181792440131)
    ·
      refine ⟨146469818072041772688660197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97646545381361181792440131 146469818072041772688660197)
      ·
        refine ⟨27463090888507832379123787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146469818072041772688660197 27463090888507832379123787)
        ·
          refine ⟨41194636332761748568685681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27463090888507832379123787 41194636332761748568685681)
          ·
            refine ⟨30895977249571311426514261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41194636332761748568685681 30895977249571311426514261)
            ·
              refine ⟨45257779174176725722433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30895977249571311426514261 45257779174176725722433)
              ·
                rfl

theorem cell23_7139276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 11].length) (baseStart_7139276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139276 prefixEnd_7139276 := by exact prefixLift 7139276
  have htrace : WordTrace (prefixWord ++ tailWord_7139276) baseStart_7139276 baseEnd_7139276 := by
    simpa [prefixWord, tailWord_7139276, baseEnd_7139276] using wordTrace_append hprefix tailTrace_7139276
  have hstable : (prefixWord ++ tailWord_7139276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139276).length < 2 ^ (prefixWord ++ tailWord_7139276).sum := by decide
  have hdescent : baseEnd_7139276 < baseStart_7139276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139338 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_7139338 : Nat := 118140960795 + 7139338 * 2 ^ 59
def prefixEnd_7139338 : Nat := 4983230072969 + 3 ^ 40 * 7139338 * 2
def baseEnd_7139338 : Nat := 3665911948908893540941789

theorem tailTrace_7139338 : CollatzResearch.WordTrace tailWord_7139338 prefixEnd_7139338 3665911948908893540941789 := by
  unfold tailWord_7139338
  simp only [CollatzResearch.WordTrace]
  refine ⟨65098262252351300675482667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173595366006270135134620445 65098262252351300675482667)
  ·
    refine ⟨97647393378526951013224001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65098262252351300675482667 97647393378526951013224001)
    ·
      refine ⟨73235545033895213259918001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97647393378526951013224001 73235545033895213259918001)
      ·
        refine ⟨54926658775421409944938501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73235545033895213259918001 54926658775421409944938501)
        ·
          refine ⟨10298748520391514364675969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54926658775421409944938501 10298748520391514364675969)
          ·
            refine ⟨7724061390293635773506977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10298748520391514364675969 7724061390293635773506977)
            ·
              refine ⟨5793046042720226830130233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7724061390293635773506977 5793046042720226830130233)
              ·
                refine ⟨4344784532040170122597675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793046042720226830130233 4344784532040170122597675)
                ·
                  refine ⟨6517176798060255183896513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344784532040170122597675 6517176798060255183896513)
                  ·
                    refine ⟨4887882598545191387922385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6517176798060255183896513 4887882598545191387922385)
                    ·
                      refine ⟨3665911948908893540941789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887882598545191387922385 3665911948908893540941789)
                      ·
                        rfl

theorem cell23_7139338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_7139338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139338 prefixEnd_7139338 := by exact prefixLift 7139338
  have htrace : WordTrace (prefixWord ++ tailWord_7139338) baseStart_7139338 baseEnd_7139338 := by
    simpa [prefixWord, tailWord_7139338, baseEnd_7139338] using wordTrace_append hprefix tailTrace_7139338
  have hstable : (prefixWord ++ tailWord_7139338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139338).length < 2 ^ (prefixWord ++ tailWord_7139338).sum := by decide
  have hdescent : baseEnd_7139338 < baseStart_7139338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139343 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 10, 2]
def baseStart_7139343 : Nat := 118140960795 + 7139343 * 2 ^ 59
def prefixEnd_7139343 : Nat := 4983230072969 + 3 ^ 40 * 7139343 * 2
def baseEnd_7139343 : Nat := 3665914516312166021379265

theorem tailTrace_7139343 : CollatzResearch.WordTrace tailWord_7139343 prefixEnd_7139343 3665914516312166021379265 := by
  unfold tailWord_7139343
  simp only [CollatzResearch.WordTrace]
  refine ⟨260393231374387088555862683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173595487582924725703908455 260393231374387088555862683)
  ·
    refine ⟨390589847061580632833794025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260393231374387088555862683 390589847061580632833794025)
    ·
      refine ⟨292942385296185474625345519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390589847061580632833794025 292942385296185474625345519)
      ·
        refine ⟨439413577944278211938018279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292942385296185474625345519 439413577944278211938018279)
        ·
          refine ⟨659120366916417317907027419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439413577944278211938018279 659120366916417317907027419)
          ·
            refine ⟨988680550374625976860541129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659120366916417317907027419 988680550374625976860541129)
            ·
              refine ⟨741510412780969482645405847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988680550374625976860541129 741510412780969482645405847)
              ·
                refine ⟨1112265619171454223968108771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741510412780969482645405847 1112265619171454223968108771)
                ·
                  refine ⟨1668398428757181335952163157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112265619171454223968108771 1668398428757181335952163157)
                  ·
                    refine ⟨4887886021749554695172353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1668398428757181335952163157 4887886021749554695172353)
                    ·
                      refine ⟨3665914516312166021379265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887886021749554695172353 3665914516312166021379265)
                      ·
                        rfl

theorem cell23_7139343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10, 2].length) (baseStart_7139343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139343 prefixEnd_7139343 := by exact prefixLift 7139343
  have htrace : WordTrace (prefixWord ++ tailWord_7139343) baseStart_7139343 baseEnd_7139343 := by
    simpa [prefixWord, tailWord_7139343, baseEnd_7139343] using wordTrace_append hprefix tailTrace_7139343
  have hstable : (prefixWord ++ tailWord_7139343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139343).length < 2 ^ (prefixWord ++ tailWord_7139343).sum := by decide
  have hdescent : baseEnd_7139343 < baseStart_7139343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139363 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 3]
def baseStart_7139363 : Nat := 118140960795 + 7139363 * 2 ^ 59
def prefixEnd_7139363 : Nat := 4983230072969 + 3 ^ 40 * 7139363 * 2
def baseEnd_7139363 : Nat := 3665924785925255943129173

theorem tailTrace_7139363 : CollatzResearch.WordTrace tailWord_7139363 prefixEnd_7139363 3665924785925255943129173 := by
  unfold tailWord_7139363
  simp only [CollatzResearch.WordTrace]
  refine ⟨260393960834314631971590743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173595973889543087981060495 260393960834314631971590743)
  ·
    refine ⟨390590941251471947957386115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260393960834314631971590743 390590941251471947957386115)
    ·
      refine ⟨585886411877207921936079173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390590941251471947957386115 585886411877207921936079173)
      ·
        refine ⟨109853702226976485363014845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 585886411877207921936079173 109853702226976485363014845)
        ·
          refine ⟨41195138335116182011130567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109853702226976485363014845 41195138335116182011130567)
          ·
            refine ⟨61792707502674273016695851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41195138335116182011130567 61792707502674273016695851)
            ·
              refine ⟨92689061254011409525043777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61792707502674273016695851 92689061254011409525043777)
              ·
                refine ⟨69516795940508557143782833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92689061254011409525043777 69516795940508557143782833)
                ·
                  refine ⟨52137596955381417857837125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69516795940508557143782833 52137596955381417857837125)
                  ·
                    refine ⟨9775799429134015848344461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52137596955381417857837125 9775799429134015848344461)
                    ·
                      refine ⟨3665924785925255943129173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9775799429134015848344461 3665924785925255943129173)
                      ·
                        rfl

theorem cell23_7139363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_7139363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139363 prefixEnd_7139363 := by exact prefixLift 7139363
  have htrace : WordTrace (prefixWord ++ tailWord_7139363) baseStart_7139363 baseEnd_7139363 := by
    simpa [prefixWord, tailWord_7139363, baseEnd_7139363] using wordTrace_append hprefix tailTrace_7139363
  have hstable : (prefixWord ++ tailWord_7139363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139363).length < 2 ^ (prefixWord ++ tailWord_7139363).sum := by decide
  have hdescent : baseEnd_7139363 < baseStart_7139363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139413 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_7139413 : Nat := 118140960795 + 7139413 * 2 ^ 59
def prefixEnd_7139413 : Nat := 4983230072969 + 3 ^ 40 * 7139413 * 2
def baseEnd_7139413 : Nat := 1221983486652660249167981

theorem tailTrace_7139413 : CollatzResearch.WordTrace tailWord_7139413 prefixEnd_7139413 1221983486652660249167981 := by
  unfold tailWord_7139413
  simp only [CollatzResearch.WordTrace]
  refine ⟨260395784484133490510910893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173597189656088993673940595 260395784484133490510910893)
  ·
    refine ⟨97648419181550058941591585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260395784484133490510910893 97648419181550058941591585)
    ·
      refine ⟨73236314386162544206193689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97648419181550058941591585 73236314386162544206193689)
      ·
        refine ⟨54927235789621908154645267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73236314386162544206193689 54927235789621908154645267)
        ·
          refine ⟨82390853684432862231967901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54927235789621908154645267 82390853684432862231967901)
          ·
            refine ⟨30896570131662323336987963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82390853684432862231967901 30896570131662323336987963)
            ·
              refine ⟨46344855197493485005481945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30896570131662323336987963 46344855197493485005481945)
              ·
                refine ⟨34758641398120113754111459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46344855197493485005481945 34758641398120113754111459)
                ·
                  refine ⟨52137962097180170631167189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34758641398120113754111459 52137962097180170631167189)
                  ·
                    refine ⟨1221983486652660249167981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52137962097180170631167189 1221983486652660249167981)
                    ·
                      rfl

theorem cell23_7139413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_7139413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139413 prefixEnd_7139413 := by exact prefixLift 7139413
  have htrace : WordTrace (prefixWord ++ tailWord_7139413) baseStart_7139413 baseEnd_7139413 := by
    simpa [prefixWord, tailWord_7139413, baseEnd_7139413] using wordTrace_append hprefix tailTrace_7139413
  have hstable : (prefixWord ++ tailWord_7139413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139413).length < 2 ^ (prefixWord ++ tailWord_7139413).sum := by decide
  have hdescent : baseEnd_7139413 < baseStart_7139413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139433 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_7139433 : Nat := 118140960795 + 7139433 * 2 ^ 59
def prefixEnd_7139433 : Nat := 4983230072969 + 3 ^ 40 * 7139433 * 2
def baseEnd_7139433 : Nat := 3665960729571070669253851

theorem tailTrace_7139433 : CollatzResearch.WordTrace tailWord_7139433 prefixEnd_7139433 3665960729571070669253851 := by
  unfold tailWord_7139433
  simp only [CollatzResearch.WordTrace]
  refine ⟨260396513944061033926638953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173597675962707355951092635 260396513944061033926638953)
  ·
    refine ⟨195297385458045775444979215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260396513944061033926638953 195297385458045775444979215)
    ·
      refine ⟨292946078187068663167468823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195297385458045775444979215 292946078187068663167468823)
      ·
        refine ⟨439419117280602994751203235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292946078187068663167468823 439419117280602994751203235)
        ·
          refine ⟨659128675920904492126804853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439419117280602994751203235 659128675920904492126804853)
          ·
            refine ⟨61793313367584796136887955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 659128675920904492126804853 61793313367584796136887955)
            ·
              refine ⟨92689970051377194205331933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61793313367584796136887955 92689970051377194205331933)
              ·
                refine ⟨34758738769266447826999475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92689970051377194205331933 34758738769266447826999475)
                ·
                  refine ⟨52138108153899671740499213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34758738769266447826999475 52138108153899671740499213)
                  ·
                    refine ⟨19551790557712376902687205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52138108153899671740499213 19551790557712376902687205)
                    ·
                      refine ⟨3665960729571070669253851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19551790557712376902687205 3665960729571070669253851)
                      ·
                        rfl

theorem cell23_7139433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_7139433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139433 prefixEnd_7139433 := by exact prefixLift 7139433
  have htrace : WordTrace (prefixWord ++ tailWord_7139433) baseStart_7139433 baseEnd_7139433 := by
    simpa [prefixWord, tailWord_7139433, baseEnd_7139433] using wordTrace_append hprefix tailTrace_7139433
  have hstable : (prefixWord ++ tailWord_7139433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139433).length < 2 ^ (prefixWord ++ tailWord_7139433).sum := by decide
  have hdescent : baseEnd_7139433 < baseStart_7139433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139434 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_7139434 : Nat := 118140960795 + 7139434 * 2 ^ 59
def prefixEnd_7139434 : Nat := 4983230072969 + 3 ^ 40 * 7139434 * 2
def baseEnd_7139434 : Nat := 407329027005747240593483

theorem tailTrace_7139434 : CollatzResearch.WordTrace tailWord_7139434 prefixEnd_7139434 407329027005747240593483 := by
  unfold tailWord_7139434
  simp only [CollatzResearch.WordTrace]
  refine ⟨65099137604264352774356339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173597700278038274064950237 65099137604264352774356339)
  ·
    refine ⟨97648706406396529161534509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65099137604264352774356339 97648706406396529161534509)
    ·
      refine ⟨36618264902398698435575441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97648706406396529161534509 36618264902398698435575441)
      ·
        refine ⟨27463698676799023826681581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36618264902398698435575441 27463698676799023826681581)
        ·
          refine ⟨10298887003799633935005593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27463698676799023826681581 10298887003799633935005593)
          ·
            refine ⟨7724165252849725451254195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10298887003799633935005593 7724165252849725451254195)
            ·
              refine ⟨11586247879274588176881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724165252849725451254195 11586247879274588176881293)
              ·
                refine ⟨4344842954727970566330485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11586247879274588176881293 4344842954727970566330485)
                ·
                  refine ⟨407329027005747240593483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4344842954727970566330485 407329027005747240593483)
                  ·
                    rfl

theorem cell23_7139434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_7139434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139434 prefixEnd_7139434 := by exact prefixLift 7139434
  have htrace : WordTrace (prefixWord ++ tailWord_7139434) baseStart_7139434 baseEnd_7139434 := by
    simpa [prefixWord, tailWord_7139434, baseEnd_7139434] using wordTrace_append hprefix tailTrace_7139434
  have hstable : (prefixWord ++ tailWord_7139434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139434).length < 2 ^ (prefixWord ++ tailWord_7139434).sum := by decide
  have hdescent : baseEnd_7139434 < baseStart_7139434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139463 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_7139463 : Nat := 118140960795 + 7139463 * 2 ^ 59
def prefixEnd_7139463 : Nat := 4983230072969 + 3 ^ 40 * 7139463 * 2
def baseEnd_7139463 : Nat := 3665976133990705551878713

theorem tailTrace_7139463 : CollatzResearch.WordTrace tailWord_7139463 prefixEnd_7139463 3665976133990705551878713 := by
  unfold tailWord_7139463
  simp only [CollatzResearch.WordTrace]
  refine ⟨260397608133952349050231043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173598405422634899366820695 260397608133952349050231043)
  ·
    refine ⟨390596412200928523575346565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260397608133952349050231043 390596412200928523575346565)
    ·
      refine ⟨73236827287674098170377481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390596412200928523575346565 73236827287674098170377481)
      ·
        refine ⟨54927620465755573627783111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73236827287674098170377481 54927620465755573627783111)
        ·
          refine ⟨82391430698633360441674667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54927620465755573627783111 82391430698633360441674667)
          ·
            refine ⟨123587146047950040662512001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82391430698633360441674667 123587146047950040662512001)
            ·
              refine ⟨92690359535962530496884001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123587146047950040662512001 92690359535962530496884001)
              ·
                refine ⟨69517769651971897872663001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92690359535962530496884001 69517769651971897872663001)
                ·
                  refine ⟨52138327238978923404497251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69517769651971897872663001 52138327238978923404497251)
                  ·
                    refine ⟨78207490858468385106745877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52138327238978923404497251 78207490858468385106745877)
                    ·
                      refine ⟨3665976133990705551878713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78207490858468385106745877 3665976133990705551878713)
                      ·
                        rfl

theorem cell23_7139463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_7139463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139463 prefixEnd_7139463 := by exact prefixLift 7139463
  have htrace : WordTrace (prefixWord ++ tailWord_7139463) baseStart_7139463 baseEnd_7139463 := by
    simpa [prefixWord, tailWord_7139463, baseEnd_7139463] using wordTrace_append hprefix tailTrace_7139463
  have hstable : (prefixWord ++ tailWord_7139463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139463).length < 2 ^ (prefixWord ++ tailWord_7139463).sum := by decide
  have hdescent : baseEnd_7139463 < baseStart_7139463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139487 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7139487 : Nat := 118140960795 + 7139487 * 2 ^ 59
def prefixEnd_7139487 : Nat := 4983230072969 + 3 ^ 40 * 7139487 * 2
def baseEnd_7139487 : Nat := 3665988457526413457978603

theorem tailTrace_7139487 : CollatzResearch.WordTrace tailWord_7139487 prefixEnd_7139487 3665988457526413457978603 := by
  unfold tailWord_7139487
  simp only [CollatzResearch.WordTrace]
  refine ⟨260398483485865401149104715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173598988990576934099403143 260398483485865401149104715)
  ·
    refine ⟨390597725228798101723657073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260398483485865401149104715 390597725228798101723657073)
    ·
      refine ⟨292948293921598576292742805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390597725228798101723657073 292948293921598576292742805)
      ·
        refine ⟨13731951277574933263722319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 292948293921598576292742805 13731951277574933263722319)
        ·
          refine ⟨20597926916362399895583479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13731951277574933263722319 20597926916362399895583479)
          ·
            refine ⟨30896890374543599843375219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20597926916362399895583479 30896890374543599843375219)
            ·
              refine ⟨46345335561815399765062829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30896890374543599843375219 46345335561815399765062829)
              ·
                refine ⟨17379500835680774911898561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46345335561815399765062829 17379500835680774911898561)
                ·
                  refine ⟨13034625626760581183923921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17379500835680774911898561 13034625626760581183923921)
                  ·
                    refine ⟨9775969220070435887942941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13034625626760581183923921 9775969220070435887942941)
                    ·
                      refine ⟨3665988457526413457978603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9775969220070435887942941 3665988457526413457978603)
                      ·
                        rfl

theorem cell23_7139487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7139487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139487 prefixEnd_7139487 := by exact prefixLift 7139487
  have htrace : WordTrace (prefixWord ++ tailWord_7139487) baseStart_7139487 baseEnd_7139487 := by
    simpa [prefixWord, tailWord_7139487, baseEnd_7139487] using wordTrace_append hprefix tailTrace_7139487
  have hstable : (prefixWord ++ tailWord_7139487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139487).length < 2 ^ (prefixWord ++ tailWord_7139487).sum := by decide
  have hdescent : baseEnd_7139487 < baseStart_7139487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139511 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 1, 4]
def baseStart_7139511 : Nat := 118140960795 + 7139511 * 2 ^ 59
def prefixEnd_7139511 : Nat := 4983230072969 + 3 ^ 40 * 7139511 * 2
def baseEnd_7139511 : Nat := 1222000260354040454692831

theorem tailTrace_7139511 : CollatzResearch.WordTrace tailWord_7139511 prefixEnd_7139511 1222000260354040454692831 := by
  unfold tailWord_7139511
  simp only [CollatzResearch.WordTrace]
  refine ⟨260399358837778453247978387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173599572558518968831985591 260399358837778453247978387)
  ·
    refine ⟨390599038256667679871967581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260399358837778453247978387 390599038256667679871967581)
    ·
      refine ⟨146474639346250379951987843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390599038256667679871967581 146474639346250379951987843)
      ·
        refine ⟨219711959019375569927981765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146474639346250379951987843 219711959019375569927981765)
        ·
          refine ⟨41195992316132919361496581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219711959019375569927981765 41195992316132919361496581)
          ·
            refine ⟨7724248559274922380280609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41195992316132919361496581 7724248559274922380280609)
            ·
              refine ⟨5793186419456191785210457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7724248559274922380280609 5793186419456191785210457)
              ·
                refine ⟨4344889814592143838907843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793186419456191785210457 4344889814592143838907843)
                ·
                  refine ⟨6517334721888215758361765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344889814592143838907843 6517334721888215758361765)
                  ·
                    refine ⟨1222000260354040454692831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6517334721888215758361765 1222000260354040454692831)
                    ·
                      rfl

theorem cell23_7139511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_7139511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139511 prefixEnd_7139511 := by exact prefixLift 7139511
  have htrace : WordTrace (prefixWord ++ tailWord_7139511) baseStart_7139511 baseEnd_7139511 := by
    simpa [prefixWord, tailWord_7139511, baseEnd_7139511] using wordTrace_append hprefix tailTrace_7139511
  have hstable : (prefixWord ++ tailWord_7139511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139511).length < 2 ^ (prefixWord ++ tailWord_7139511).sum := by decide
  have hdescent : baseEnd_7139511 < baseStart_7139511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139517 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_7139517 : Nat := 118140960795 + 7139517 * 2 ^ 59
def prefixEnd_7139517 : Nat := 4983230072969 + 3 ^ 40 * 7139517 * 2
def baseEnd_7139517 : Nat := 3666003861946048340603465

theorem tailTrace_7139517 : CollatzResearch.WordTrace tailWord_7139517 prefixEnd_7139517 3666003861946048340603465 := by
  unfold tailWord_7139517
  simp only [CollatzResearch.WordTrace]
  refine ⟨260399577675756716272696805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173599718450504477515131203 260399577675756716272696805)
  ·
    refine ⟨48824920814204384301130651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260399577675756716272696805 48824920814204384301130651)
    ·
      refine ⟨73237381221306576451695977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48824920814204384301130651 73237381221306576451695977)
      ·
        refine ⟨54928035915979932338771983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73237381221306576451695977 54928035915979932338771983)
        ·
          refine ⟨82392053873969898508157975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54928035915979932338771983 82392053873969898508157975)
          ·
            refine ⟨123588080810954847762236963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82392053873969898508157975 123588080810954847762236963)
            ·
              refine ⟨185382121216432271643355445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123588080810954847762236963 185382121216432271643355445)
              ·
                refine ⟨17379573864040525466564573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185382121216432271643355445 17379573864040525466564573)
                ·
                  refine ⟨6517340199015197049961715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17379573864040525466564573 6517340199015197049961715)
                  ·
                    refine ⟨9776010298522795574942573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6517340199015197049961715 9776010298522795574942573)
                    ·
                      refine ⟨3666003861946048340603465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9776010298522795574942573 3666003861946048340603465)
                      ·
                        rfl

theorem cell23_7139517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_7139517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139517 prefixEnd_7139517 := by exact prefixLift 7139517
  have htrace : WordTrace (prefixWord ++ tailWord_7139517) baseStart_7139517 baseEnd_7139517 := by
    simpa [prefixWord, tailWord_7139517, baseEnd_7139517] using wordTrace_append hprefix tailTrace_7139517
  have hstable : (prefixWord ++ tailWord_7139517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139517).length < 2 ^ (prefixWord ++ tailWord_7139517).sum := by decide
  have hdescent : baseEnd_7139517 < baseStart_7139517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139520 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_7139520 : Nat := 118140960795 + 7139520 * 2 ^ 59
def prefixEnd_7139520 : Nat := 4983230072969 + 3 ^ 40 * 7139520 * 2
def baseEnd_7139520 : Nat := 1222001800796003942955317

theorem tailTrace_7139520 : CollatzResearch.WordTrace tailWord_7139520 prefixEnd_7139520 1222001800796003942955317 := by
  unfold tailWord_7139520
  simp only [CollatzResearch.WordTrace]
  refine ⟨130199843547372923892528007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173599791396497231856704009 130199843547372923892528007)
  ·
    refine ⟨195299765321059385838792011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130199843547372923892528007 195299765321059385838792011)
    ·
      refine ⟨292949647981589078758188017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195299765321059385838792011 292949647981589078758188017)
      ·
        refine ⟨219712235986191809068641013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292949647981589078758188017 219712235986191809068641013)
        ·
          refine ⟨20598022123705482100185095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219712235986191809068641013 20598022123705482100185095)
          ·
            refine ⟨30897033185558223150277643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20598022123705482100185095 30897033185558223150277643)
            ·
              refine ⟨46345549778337334725416465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30897033185558223150277643 46345549778337334725416465)
              ·
                refine ⟨34759162333753001044062349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46345549778337334725416465 34759162333753001044062349)
                ·
                  refine ⟨13034685875157375391523381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34759162333753001044062349 13034685875157375391523381)
                  ·
                    refine ⟨1222001800796003942955317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13034685875157375391523381 1222001800796003942955317)
                    ·
                      rfl

theorem cell23_7139520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_7139520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139520 prefixEnd_7139520 := by exact prefixLift 7139520
  have htrace : WordTrace (prefixWord ++ tailWord_7139520) baseStart_7139520 baseEnd_7139520 := by
    simpa [prefixWord, tailWord_7139520, baseEnd_7139520] using wordTrace_append hprefix tailTrace_7139520
  have hstable : (prefixWord ++ tailWord_7139520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139520).length < 2 ^ (prefixWord ++ tailWord_7139520).sum := by decide
  have hdescent : baseEnd_7139520 < baseStart_7139520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139534 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_7139534 : Nat := 118140960795 + 7139534 * 2 ^ 59
def prefixEnd_7139534 : Nat := 4983230072969 + 3 ^ 40 * 7139534 * 2
def baseEnd_7139534 : Nat := 3666012591117174774090887

theorem tailTrace_7139534 : CollatzResearch.WordTrace tailWord_7139534 prefixEnd_7139534 3666012591117174774090887 := by
  unfold tailWord_7139534
  simp only [CollatzResearch.WordTrace]
  refine ⟨32550024714586891022008207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173600131811130085450710437 32550024714586891022008207)
  ·
    refine ⟨48825037071880336533012311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32550024714586891022008207 48825037071880336533012311)
    ·
      refine ⟨73237555607820504799518467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48825037071880336533012311 73237555607820504799518467)
      ·
        refine ⟨109856333411730757199277701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73237555607820504799518467 109856333411730757199277701)
        ·
          refine ⟨20598062514699516974864569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109856333411730757199277701 20598062514699516974864569)
          ·
            refine ⟨15448546886024637731148427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20598062514699516974864569 15448546886024637731148427)
            ·
              refine ⟨23172820329036956596722641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15448546886024637731148427 23172820329036956596722641)
              ·
                refine ⟨17379615246777717447541981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23172820329036956596722641 17379615246777717447541981)
                ·
                  refine ⟨6517355717541644042828243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17379615246777717447541981 6517355717541644042828243)
                  ·
                    refine ⟨9776033576312466064242365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6517355717541644042828243 9776033576312466064242365)
                    ·
                      refine ⟨3666012591117174774090887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9776033576312466064242365 3666012591117174774090887)
                      ·
                        rfl

theorem cell23_7139534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_7139534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139534 prefixEnd_7139534 := by exact prefixLift 7139534
  have htrace : WordTrace (prefixWord ++ tailWord_7139534) baseStart_7139534 baseEnd_7139534 := by
    simpa [prefixWord, tailWord_7139534, baseEnd_7139534] using wordTrace_append hprefix tailTrace_7139534
  have hstable : (prefixWord ++ tailWord_7139534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139534).length < 2 ^ (prefixWord ++ tailWord_7139534).sum := by decide
  have hdescent : baseEnd_7139534 < baseStart_7139534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139544 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 2, 3, 2]
def baseStart_7139544 : Nat := 118140960795 + 7139544 * 2 ^ 59
def prefixEnd_7139544 : Nat := 4983230072969 + 3 ^ 40 * 7139544 * 2
def baseEnd_7139544 : Nat := 3666017725923719734965841

theorem tailTrace_7139544 : CollatzResearch.WordTrace tailWord_7139544 prefixEnd_7139544 3666017725923719734965841 := by
  unfold tailWord_7139544
  simp only [CollatzResearch.WordTrace]
  refine ⟨130200281223329449941964843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173600374964439266589286457 130200281223329449941964843)
  ·
    refine ⟨195300421834994174912947265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130200281223329449941964843 195300421834994174912947265)
    ·
      refine ⟨146475316376245631184710449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195300421834994174912947265 146475316376245631184710449)
      ·
        refine ⟨109856487282184223388532837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146475316376245631184710449 109856487282184223388532837)
        ·
          refine ⟨20598091365409541885349907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109856487282184223388532837 20598091365409541885349907)
          ·
            refine ⟨30897137048114312828024861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20598091365409541885349907 30897137048114312828024861)
            ·
              refine ⟨11586426393042867310509323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30897137048114312828024861 11586426393042867310509323)
              ·
                refine ⟨17379639589564300965763985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11586426393042867310509323 17379639589564300965763985)
                ·
                  refine ⟨13034729692173225724322989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17379639589564300965763985 13034729692173225724322989)
                  ·
                    refine ⟨4888023634564959646621121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13034729692173225724322989 4888023634564959646621121)
                    ·
                      refine ⟨3666017725923719734965841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888023634564959646621121 3666017725923719734965841)
                      ·
                        rfl

theorem cell23_7139544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_7139544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139544 prefixEnd_7139544 := by exact prefixLift 7139544
  have htrace : WordTrace (prefixWord ++ tailWord_7139544) baseStart_7139544 baseEnd_7139544 := by
    simpa [prefixWord, tailWord_7139544, baseEnd_7139544] using wordTrace_append hprefix tailTrace_7139544
  have hstable : (prefixWord ++ tailWord_7139544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139544).length < 2 ^ (prefixWord ++ tailWord_7139544).sum := by decide
  have hdescent : baseEnd_7139544 < baseStart_7139544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139563 : List Nat := [1, 1, 1, 1, 2, 5, 12]
def baseStart_7139563 : Nat := 118140960795 + 7139563 * 2 ^ 59
def prefixEnd_7139563 : Nat := 4983230072969 + 3 ^ 40 * 7139563 * 2
def baseEnd_7139563 : Nat := 45259598543903150131213

theorem tailTrace_7139563 : CollatzResearch.WordTrace tailWord_7139563 prefixEnd_7139563 45259598543903150131213 := by
  unfold tailWord_7139563
  simp only [CollatzResearch.WordTrace]
  refine ⟨260401255433590066128871343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173600836955726710752580895 260401255433590066128871343)
  ·
    refine ⟨390601883150385099193307015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260401255433590066128871343 390601883150385099193307015)
    ·
      refine ⟨585902824725577648789960523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390601883150385099193307015 585902824725577648789960523)
      ·
        refine ⟨878854237088366473184940785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585902824725577648789960523 878854237088366473184940785)
        ·
          refine ⟨659140677816274854888705589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878854237088366473184940785 659140677816274854888705589)
          ·
            refine ⟨61794438545275767645816149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 659140677816274854888705589 61794438545275767645816149)
            ·
              refine ⟨45259598543903150131213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 61794438545275767645816149 45259598543903150131213)
              ·
                rfl

theorem cell23_7139563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 12].length) (baseStart_7139563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139563 prefixEnd_7139563 := by exact prefixLift 7139563
  have htrace : WordTrace (prefixWord ++ tailWord_7139563) baseStart_7139563 baseEnd_7139563 := by
    simpa [prefixWord, tailWord_7139563, baseEnd_7139563] using wordTrace_append hprefix tailTrace_7139563
  have hstable : (prefixWord ++ tailWord_7139563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139563).length < 2 ^ (prefixWord ++ tailWord_7139563).sum := by decide
  have hdescent : baseEnd_7139563 < baseStart_7139563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139567 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 4, 4]
def baseStart_7139567 : Nat := 118140960795 + 7139567 * 2 ^ 59
def prefixEnd_7139567 : Nat := 4983230072969 + 3 ^ 40 * 7139567 * 2
def baseEnd_7139567 : Nat := 1222009845326257714992745

theorem tailTrace_7139567 : CollatzResearch.WordTrace tailWord_7139567 prefixEnd_7139567 1222009845326257714992745 := by
  unfold tailWord_7139567
  simp only [CollatzResearch.WordTrace]
  refine ⟨260401401325575574812016955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173600934217050383208011303 260401401325575574812016955)
  ·
    refine ⟨390602101988363362218025433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260401401325575574812016955 390602101988363362218025433)
    ·
      refine ⟨292951576491272521663519075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390602101988363362218025433 292951576491272521663519075)
      ·
        refine ⟨439427364736908782495278613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292951576491272521663519075 439427364736908782495278613)
        ·
          refine ⟨20598157722042599179466185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 439427364736908782495278613 20598157722042599179466185)
          ·
            refine ⟨15448618291531949384599639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20598157722042599179466185 15448618291531949384599639)
            ·
              refine ⟨23172927437297924076899459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15448618291531949384599639 23172927437297924076899459)
              ·
                refine ⟨34759391155946886115349189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23172927437297924076899459 34759391155946886115349189)
                ·
                  refine ⟨6517385841740041146627973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34759391155946886115349189 6517385841740041146627973)
                  ·
                    refine ⟨1222009845326257714992745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6517385841740041146627973 1222009845326257714992745)
                    ·
                      rfl

theorem cell23_7139567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_7139567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139567 prefixEnd_7139567 := by exact prefixLift 7139567
  have htrace : WordTrace (prefixWord ++ tailWord_7139567) baseStart_7139567 baseEnd_7139567 := by
    simpa [prefixWord, tailWord_7139567, baseEnd_7139567] using wordTrace_append hprefix tailTrace_7139567
  have hstable : (prefixWord ++ tailWord_7139567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139567).length < 2 ^ (prefixWord ++ tailWord_7139567).sum := by decide
  have hdescent : baseEnd_7139567 < baseStart_7139567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139591 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7139591 : Nat := 118140960795 + 7139591 * 2 ^ 59
def prefixEnd_7139591 : Nat := 4983230072969 + 3 ^ 40 * 7139591 * 2
def baseEnd_7139591 : Nat := 3666041859514481051078125

theorem tailTrace_7139591 : CollatzResearch.WordTrace tailWord_7139591 prefixEnd_7139591 3666041859514481051078125 := by
  unfold tailWord_7139591
  simp only [CollatzResearch.WordTrace]
  refine ⟨260402276677488626910890627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173601517784992417940593751 260402276677488626910890627)
  ·
    refine ⟨390603415016232940366335941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260402276677488626910890627 390603415016232940366335941)
    ·
      refine ⟨73238140315543676318687989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390603415016232940366335941 73238140315543676318687989)
      ·
        refine ⟨6866075654582219654876999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73238140315543676318687989 6866075654582219654876999)
        ·
          refine ⟨10299113481873329482315499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866075654582219654876999 10299113481873329482315499)
          ·
            refine ⟨15448670222809994223473249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10299113481873329482315499 15448670222809994223473249)
            ·
              refine ⟨11586502667107495667604937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15448670222809994223473249 11586502667107495667604937)
              ·
                refine ⟨8689877000330621750703703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11586502667107495667604937 8689877000330621750703703)
                ·
                  refine ⟨13034815500495932626055555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8689877000330621750703703 13034815500495932626055555)
                  ·
                    refine ⟨19552223250743898939083333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13034815500495932626055555 19552223250743898939083333)
                    ·
                      refine ⟨3666041859514481051078125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19552223250743898939083333 3666041859514481051078125)
                      ·
                        rfl

theorem cell23_7139591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7139591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139591 prefixEnd_7139591 := by exact prefixLift 7139591
  have htrace : WordTrace (prefixWord ++ tailWord_7139591) baseStart_7139591 baseEnd_7139591 := by
    simpa [prefixWord, tailWord_7139591, baseEnd_7139591] using wordTrace_append hprefix tailTrace_7139591
  have hstable : (prefixWord ++ tailWord_7139591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139591).length < 2 ^ (prefixWord ++ tailWord_7139591).sum := by decide
  have hdescent : baseEnd_7139591 < baseStart_7139591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139614 : List Nat := [4, 3, 2, 1, 1, 3, 9]
def baseStart_7139614 : Nat := 118140960795 + 7139614 * 2 ^ 59
def prefixEnd_7139614 : Nat := 4983230072969 + 3 ^ 40 * 7139614 * 2
def baseEnd_7139614 : Nat := 45259921846537462482599

theorem tailTrace_7139614 : CollatzResearch.WordTrace tailWord_7139614 prefixEnd_7139614 45259921846537462482599 := by
  unfold tailWord_7139614
  simp only [CollatzResearch.WordTrace]
  refine ⟨32550389444550662729872237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173602077037603534559318597 32550389444550662729872237)
  ·
    refine ⟨12206396041706498523702089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32550389444550662729872237 12206396041706498523702089)
    ·
      refine ⟨9154797031279873892776567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12206396041706498523702089 9154797031279873892776567)
      ·
        refine ⟨13732195546919810839164851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9154797031279873892776567 13732195546919810839164851)
        ·
          refine ⟨20598293320379716258747277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13732195546919810839164851 20598293320379716258747277)
          ·
            refine ⟨7724359995142393597030229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20598293320379716258747277 7724359995142393597030229)
            ·
              refine ⟨45259921846537462482599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7724359995142393597030229 45259921846537462482599)
              ·
                rfl

theorem cell23_7139614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 9].length) (baseStart_7139614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139614 prefixEnd_7139614 := by exact prefixLift 7139614
  have htrace : WordTrace (prefixWord ++ tailWord_7139614) baseStart_7139614 baseEnd_7139614 := by
    simpa [prefixWord, tailWord_7139614, baseEnd_7139614] using wordTrace_append hprefix tailTrace_7139614
  have hstable : (prefixWord ++ tailWord_7139614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139614).length < 2 ^ (prefixWord ++ tailWord_7139614).sum := by decide
  have hdescent : baseEnd_7139614 < baseStart_7139614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139640 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_7139640 : Nat := 118140960795 + 7139640 * 2 ^ 59
def prefixEnd_7139640 : Nat := 4983230072969 + 3 ^ 40 * 7139640 * 2
def baseEnd_7139640 : Nat := 1222022340022183786455133

theorem tailTrace_7139640 : CollatzResearch.WordTrace tailWord_7139640 prefixEnd_7139640 1222022340022183786455133 := by
  unfold tailWord_7139640
  simp only [CollatzResearch.WordTrace]
  refine ⟨130202031927155554139712187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173602709236207405519616249 130202031927155554139712187)
  ·
    refine ⟨195303047890733331209568281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130202031927155554139712187 195303047890733331209568281)
    ·
      refine ⟨146477285918049998407176211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195303047890733331209568281 146477285918049998407176211)
      ·
        refine ⟨219715928877074997610764317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146477285918049998407176211 219715928877074997610764317)
        ·
          refine ⟨82393473328903124104036619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219715928877074997610764317 82393473328903124104036619)
          ·
            refine ⟨123590209993354686156054929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82393473328903124104036619 123590209993354686156054929)
            ·
              refine ⟨92692657495016014617041197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123590209993354686156054929 92692657495016014617041197)
              ·
                refine ⟨34759746560631005481390449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92692657495016014617041197 34759746560631005481390449)
                ·
                  refine ⟨26069809920473254111042837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34759746560631005481390449 26069809920473254111042837)
                  ·
                    refine ⟨1222022340022183786455133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26069809920473254111042837 1222022340022183786455133)
                    ·
                      rfl

theorem cell23_7139640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_7139640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139640 prefixEnd_7139640 := by exact prefixLift 7139640
  have htrace : WordTrace (prefixWord ++ tailWord_7139640) baseStart_7139640 baseEnd_7139640 := by
    simpa [prefixWord, tailWord_7139640, baseEnd_7139640] using wordTrace_append hprefix tailTrace_7139640
  have hstable : (prefixWord ++ tailWord_7139640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139640).length < 2 ^ (prefixWord ++ tailWord_7139640).sum := by decide
  have hdescent : baseEnd_7139640 < baseStart_7139640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139641 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7139641 : Nat := 118140960795 + 7139641 * 2 ^ 59
def prefixEnd_7139641 : Nat := 4983230072969 + 3 ^ 40 * 7139641 * 2
def baseEnd_7139641 : Nat := 3666067533547205855452895

theorem tailTrace_7139641 : CollatzResearch.WordTrace tailWord_7139641 prefixEnd_7139641 3666067533547205855452895 := by
  unfold tailWord_7139641
  simp only [CollatzResearch.WordTrace]
  refine ⟨260404100327307485450210777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173602733551538323633473851 260404100327307485450210777)
  ·
    refine ⟨195303075245480614087658083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260404100327307485450210777 195303075245480614087658083)
    ·
      refine ⟨292954612868220921131487125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195303075245480614087658083 292954612868220921131487125)
      ·
        refine ⟨13732247478197855678038459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 292954612868220921131487125 13732247478197855678038459)
        ·
          refine ⟨20598371217296783517057689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13732247478197855678038459 20598371217296783517057689)
          ·
            refine ⟨15448778412972587637793267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20598371217296783517057689 15448778412972587637793267)
            ·
              refine ⟨23173167619458881456689901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15448778412972587637793267 23173167619458881456689901)
              ·
                refine ⟨8689937857297080546258713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23173167619458881456689901 8689937857297080546258713)
                ·
                  refine ⟨6517453392972810409694035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8689937857297080546258713 6517453392972810409694035)
                  ·
                    refine ⟨9776180089459215614541053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6517453392972810409694035 9776180089459215614541053)
                    ·
                      refine ⟨3666067533547205855452895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9776180089459215614541053 3666067533547205855452895)
                      ·
                        rfl

theorem cell23_7139641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7139641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139641 prefixEnd_7139641 := by exact prefixLift 7139641
  have htrace : WordTrace (prefixWord ++ tailWord_7139641) baseStart_7139641 baseEnd_7139641 := by
    simpa [prefixWord, tailWord_7139641, baseEnd_7139641] using wordTrace_append hprefix tailTrace_7139641
  have hstable : (prefixWord ++ tailWord_7139641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139641).length < 2 ^ (prefixWord ++ tailWord_7139641).sum := by decide
  have hdescent : baseEnd_7139641 < baseStart_7139641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139664 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 1, 4, 2]
def baseStart_7139664 : Nat := 118140960795 + 7139664 * 2 ^ 59
def prefixEnd_7139664 : Nat := 4983230072969 + 3 ^ 40 * 7139664 * 2
def baseEnd_7139664 : Nat := 3666079343602259265465289

theorem tailTrace_7139664 : CollatzResearch.WordTrace tailWord_7139664 prefixEnd_7139664 3666079343602259265465289 := by
  unfold tailWord_7139664
  simp only [CollatzResearch.WordTrace]
  refine ⟨130202469603112080189149023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173603292804149440252198697 130202469603112080189149023)
  ·
    refine ⟨195303704404668120283723535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130202469603112080189149023 195303704404668120283723535)
    ·
      refine ⟨292955556607002180425585303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195303704404668120283723535 292955556607002180425585303)
      ·
        refine ⟨439433334910503270638377955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292955556607002180425585303 439433334910503270638377955)
        ·
          refine ⟨659150002365754905957566933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439433334910503270638377955 659150002365754905957566933)
          ·
            refine ⟨15448828180447380608380475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 659150002365754905957566933 15448828180447380608380475)
            ·
              refine ⟨23173242270671070912570713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15448828180447380608380475 23173242270671070912570713)
              ·
                refine ⟨17379931703003303184428035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23173242270671070912570713 17379931703003303184428035)
                ·
                  refine ⟨26069897554504954776642053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17379931703003303184428035 26069897554504954776642053)
                  ·
                    refine ⟨4888105791469679020620385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26069897554504954776642053 4888105791469679020620385)
                    ·
                      refine ⟨3666079343602259265465289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888105791469679020620385 3666079343602259265465289)
                      ·
                        rfl

theorem cell23_7139664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 4, 2].length) (baseStart_7139664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139664 prefixEnd_7139664 := by exact prefixLift 7139664
  have htrace : WordTrace (prefixWord ++ tailWord_7139664) baseStart_7139664 baseEnd_7139664 := by
    simpa [prefixWord, tailWord_7139664, baseEnd_7139664] using wordTrace_append hprefix tailTrace_7139664
  have hstable : (prefixWord ++ tailWord_7139664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139664).length < 2 ^ (prefixWord ++ tailWord_7139664).sum := by decide
  have hdescent : baseEnd_7139664 < baseStart_7139664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139668 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_7139668 : Nat := 118140960795 + 7139668 * 2 ^ 59
def prefixEnd_7139668 : Nat := 4983230072969 + 3 ^ 40 * 7139668 * 2
def baseEnd_7139668 : Nat := 3666081397524877249815271

theorem tailTrace_7139668 : CollatzResearch.WordTrace tailWord_7139668 prefixEnd_7139668 3666081397524877249815271 := by
  unfold tailWord_7139668
  simp only [CollatzResearch.WordTrace]
  refine ⟨130202542549104834530721829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173603390065473112707629105 130202542549104834530721829)
  ·
    refine ⟨24412976727957156474510343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130202542549104834530721829 24412976727957156474510343)
    ·
      refine ⟨36619465091935734711765515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24412976727957156474510343 36619465091935734711765515)
      ·
        refine ⟨54929197637903602067648273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36619465091935734711765515 54929197637903602067648273)
        ·
          refine ⟨41196898228427701550736205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54929197637903602067648273 41196898228427701550736205)
          ·
            refine ⟨15448836835660388081526077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41196898228427701550736205 15448836835660388081526077)
            ·
              refine ⟨5793313813372645530572279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15448836835660388081526077 5793313813372645530572279)
              ·
                refine ⟨8689970720058968295858419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793313813372645530572279 8689970720058968295858419)
                ·
                  refine ⟨13034956080088452443787629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8689970720058968295858419 13034956080088452443787629)
                  ·
                    refine ⟨4888108530033169666420361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13034956080088452443787629 4888108530033169666420361)
                    ·
                      refine ⟨3666081397524877249815271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888108530033169666420361 3666081397524877249815271)
                      ·
                        rfl

theorem cell23_7139668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_7139668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139668 prefixEnd_7139668 := by exact prefixLift 7139668
  have htrace : WordTrace (prefixWord ++ tailWord_7139668) baseStart_7139668 baseEnd_7139668 := by
    simpa [prefixWord, tailWord_7139668, baseEnd_7139668] using wordTrace_append hprefix tailTrace_7139668
  have hstable : (prefixWord ++ tailWord_7139668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139668).length < 2 ^ (prefixWord ++ tailWord_7139668).sum := by decide
  have hdescent : baseEnd_7139668 < baseStart_7139668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139732 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_7139732 : Nat := 118140960795 + 7139732 * 2 ^ 59
def prefixEnd_7139732 : Nat := 4983230072969 + 3 ^ 40 * 7139732 * 2
def baseEnd_7139732 : Nat := 3666114260286764999414977

theorem tailTrace_7139732 : CollatzResearch.WordTrace tailWord_7139732 prefixEnd_7139732 3666114260286764999414977 := by
  unfold tailWord_7139732
  simp only [CollatzResearch.WordTrace]
  refine ⟨130203709684988903995886725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173604946246651871994515633 130203709684988903995886725)
  ·
    refine ⟨24413195565935419499228761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130203709684988903995886725 24413195565935419499228761)
    ·
      refine ⟨18309896674451564624421571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24413195565935419499228761 18309896674451564624421571)
      ·
        refine ⟨27464845011677346936632357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18309896674451564624421571 27464845011677346936632357)
        ·
          refine ⟨5149658439689502550618567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27464845011677346936632357 5149658439689502550618567)
          ·
            refine ⟨7724487659534253825927851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149658439689502550618567 7724487659534253825927851)
            ·
              refine ⟨11586731489301380738891777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724487659534253825927851 11586731489301380738891777)
              ·
                refine ⟨8690048616976035554168833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11586731489301380738891777 8690048616976035554168833)
                ·
                  refine ⟨6517536462732026665626625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8690048616976035554168833 6517536462732026665626625)
                  ·
                    refine ⟨4888152347049019999219969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6517536462732026665626625 4888152347049019999219969)
                    ·
                      refine ⟨3666114260286764999414977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888152347049019999219969 3666114260286764999414977)
                      ·
                        rfl

theorem cell23_7139732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_7139732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139732 prefixEnd_7139732 := by exact prefixLift 7139732
  have htrace : WordTrace (prefixWord ++ tailWord_7139732) baseStart_7139732 baseEnd_7139732 := by
    simpa [prefixWord, tailWord_7139732, baseEnd_7139732] using wordTrace_append hprefix tailTrace_7139732
  have hstable : (prefixWord ++ tailWord_7139732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139732).length < 2 ^ (prefixWord ++ tailWord_7139732).sum := by decide
  have hdescent : baseEnd_7139732 < baseStart_7139732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139737 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_7139737 : Nat := 118140960795 + 7139737 * 2 ^ 59
def prefixEnd_7139737 : Nat := 4983230072969 + 3 ^ 40 * 7139737 * 2
def baseEnd_7139737 : Nat := 3666116827690037479852453

theorem tailTrace_7139737 : CollatzResearch.WordTrace tailWord_7139737 prefixEnd_7139737 3666116827690037479852453 := by
  unfold tailWord_7139737
  simp only [CollatzResearch.WordTrace]
  refine ⟨260407601734959693845705465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173605067823306462563803643 260407601734959693845705465)
  ·
    refine ⟨195305701301219770384279099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260407601734959693845705465 195305701301219770384279099)
    ·
      refine ⟨292958551951829655576418649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195305701301219770384279099 292958551951829655576418649)
      ·
        refine ⟨219718913963872241682313987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292958551951829655576418649 219718913963872241682313987)
        ·
          refine ⟨329578370945808362523470981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219718913963872241682313987 329578370945808362523470981)
          ·
            refine ⟨61795944552339067973150809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329578370945808362523470981 61795944552339067973150809)
            ·
              refine ⟨46346958414254300979863107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61795944552339067973150809 46346958414254300979863107)
              ·
                refine ⟨69520437621381451469794661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46346958414254300979863107 69520437621381451469794661)
                ·
                  refine ⟨13035082054009022150586499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69520437621381451469794661 13035082054009022150586499)
                  ·
                    refine ⟨19552623081013533225879749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13035082054009022150586499 19552623081013533225879749)
                    ·
                      refine ⟨3666116827690037479852453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19552623081013533225879749 3666116827690037479852453)
                      ·
                        rfl

theorem cell23_7139737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_7139737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139737 prefixEnd_7139737 := by exact prefixLift 7139737
  have htrace : WordTrace (prefixWord ++ tailWord_7139737) baseStart_7139737 baseEnd_7139737 := by
    simpa [prefixWord, tailWord_7139737, baseEnd_7139737] using wordTrace_append hprefix tailTrace_7139737
  have hstable : (prefixWord ++ tailWord_7139737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139737).length < 2 ^ (prefixWord ++ tailWord_7139737).sum := by decide
  have hdescent : baseEnd_7139737 < baseStart_7139737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139774 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_7139774 : Nat := 118140960795 + 7139774 * 2 ^ 59
def prefixEnd_7139774 : Nat := 4983230072969 + 3 ^ 40 * 7139774 * 2
def baseEnd_7139774 : Nat := 3666135826474253835089783

theorem tailTrace_7139774 : CollatzResearch.WordTrace tailWord_7139774 prefixEnd_7139774 3666135826474253835089783 := by
  unfold tailWord_7139774
  simp only [CollatzResearch.WordTrace]
  refine ⟨32551118904478206145600297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173605967490550432776534917 32551118904478206145600297)
  ·
    refine ⟨24413339178358654609200223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32551118904478206145600297 24413339178358654609200223)
    ·
      refine ⟨36620008767537981913800335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24413339178358654609200223 36620008767537981913800335)
      ·
        refine ⟨54930013151306972870700503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36620008767537981913800335 54930013151306972870700503)
        ·
          refine ⟨82395019726960459306050755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54930013151306972870700503 82395019726960459306050755)
          ·
            refine ⟨123592529590440688959076133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82395019726960459306050755 123592529590440688959076133)
            ·
              refine ⟨23173599298207629179826775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123592529590440688959076133 23173599298207629179826775)
              ·
                refine ⟨34760398947311443769740163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23173599298207629179826775 34760398947311443769740163)
                ·
                  refine ⟨52140598420967165654610245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34760398947311443769740163 52140598420967165654610245)
                  ·
                    refine ⟨9776362203931343560239421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52140598420967165654610245 9776362203931343560239421)
                    ·
                      refine ⟨3666135826474253835089783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9776362203931343560239421 3666135826474253835089783)
                      ·
                        rfl

theorem cell23_7139774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_7139774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139774 prefixEnd_7139774 := by exact prefixLift 7139774
  have htrace : WordTrace (prefixWord ++ tailWord_7139774) baseStart_7139774 baseEnd_7139774 := by
    simpa [prefixWord, tailWord_7139774, baseEnd_7139774] using wordTrace_append hprefix tailTrace_7139774
  have hstable : (prefixWord ++ tailWord_7139774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139774).length < 2 ^ (prefixWord ++ tailWord_7139774).sum := by decide
  have hdescent : baseEnd_7139774 < baseStart_7139774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139857 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_7139857 : Nat := 118140960795 + 7139857 * 2 ^ 59
def prefixEnd_7139857 : Nat := 4983230072969 + 3 ^ 40 * 7139857 * 2
def baseEnd_7139857 : Nat := 3666178445368577010351901

theorem tailTrace_7139857 : CollatzResearch.WordTrace tailWord_7139857 prefixEnd_7139857 3666178445368577010351901 := by
  unfold tailWord_7139857
  simp only [CollatzResearch.WordTrace]
  refine ⟨260411978494524954340073825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173607985663016636226715883 260411978494524954340073825)
  ·
    refine ⟨195308983870893715755055369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260411978494524954340073825 195308983870893715755055369)
    ·
      refine ⟨146481737903170286816291527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195308983870893715755055369 146481737903170286816291527)
      ·
        refine ⟨219722606854755430224437291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146481737903170286816291527 219722606854755430224437291)
        ·
          refine ⟨329583910282133145336655937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219722606854755430224437291 329583910282133145336655937)
          ·
            refine ⟨247187932711599859002491953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329583910282133145336655937 247187932711599859002491953)
            ·
              refine ⟨185390949533699894251868965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247187932711599859002491953 185390949533699894251868965)
              ·
                refine ⟨34760803037568730172225431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185390949533699894251868965 34760803037568730172225431)
                ·
                  refine ⟨52141204556353095258338147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34760803037568730172225431 52141204556353095258338147)
                  ·
                    refine ⟨78211806834529642887507221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52141204556353095258338147 78211806834529642887507221)
                    ·
                      refine ⟨3666178445368577010351901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78211806834529642887507221 3666178445368577010351901)
                      ·
                        rfl

theorem cell23_7139857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_7139857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139857 prefixEnd_7139857 := by exact prefixLift 7139857
  have htrace : WordTrace (prefixWord ++ tailWord_7139857) baseStart_7139857 baseEnd_7139857 := by
    simpa [prefixWord, tailWord_7139857, baseEnd_7139857] using wordTrace_append hprefix tailTrace_7139857
  have hstable : (prefixWord ++ tailWord_7139857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139857).length < 2 ^ (prefixWord ++ tailWord_7139857).sum := by decide
  have hdescent : baseEnd_7139857 < baseStart_7139857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139892 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_7139892 : Nat := 118140960795 + 7139892 * 2 ^ 59
def prefixEnd_7139892 : Nat := 4983230072969 + 3 ^ 40 * 7139892 * 2
def baseEnd_7139892 : Nat := 1222065472397161457804747

theorem tailTrace_7139892 : CollatzResearch.WordTrace tailWord_7139892 prefixEnd_7139892 1222065472397161457804747 := by
  unfold tailWord_7139892
  simp only [CollatzResearch.WordTrace]
  refine ⟨130206627524699077658798965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173608836699598770211731953 130206627524699077658798965)
  ·
    refine ⟨12206871330440538530512403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130206627524699077658798965 12206871330440538530512403)
    ·
      refine ⟨18310306995660807795768605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12206871330440538530512403 18310306995660807795768605)
      ·
        refine ⟨6866365123372802923413227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18310306995660807795768605 6866365123372802923413227)
        ·
          refine ⟨10299547685059204385119841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866365123372802923413227 10299547685059204385119841)
          ·
            refine ⟨7724660763794403288839881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10299547685059204385119841 7724660763794403288839881)
            ·
              refine ⟨5793495572845802466629911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7724660763794403288839881 5793495572845802466629911)
              ·
                refine ⟨8690243359268703699944867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793495572845802466629911 8690243359268703699944867)
                ·
                  refine ⟨13035365038903055549917301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690243359268703699944867 13035365038903055549917301)
                  ·
                    refine ⟨1222065472397161457804747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13035365038903055549917301 1222065472397161457804747)
                    ·
                      rfl

theorem cell23_7139892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_7139892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139892 prefixEnd_7139892 := by exact prefixLift 7139892
  have htrace : WordTrace (prefixWord ++ tailWord_7139892) baseStart_7139892 baseEnd_7139892 := by
    simpa [prefixWord, tailWord_7139892, baseEnd_7139892] using wordTrace_append hprefix tailTrace_7139892
  have hstable : (prefixWord ++ tailWord_7139892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139892).length < 2 ^ (prefixWord ++ tailWord_7139892).sum := by decide
  have hdescent : baseEnd_7139892 < baseStart_7139892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139895 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 1, 2, 2]
def baseStart_7139895 : Nat := 118140960795 + 7139895 * 2 ^ 59
def prefixEnd_7139895 : Nat := 4983230072969 + 3 ^ 40 * 7139895 * 2
def baseEnd_7139895 : Nat := 3666197957633447861676727

theorem tailTrace_7139895 : CollatzResearch.WordTrace tailWord_7139895 prefixEnd_7139895 3666197957633447861676727 := by
  unfold tailWord_7139895
  simp only [CollatzResearch.WordTrace]
  refine ⟨260413364468387286829957139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173608909645591524553304759 260413364468387286829957139)
  ·
    refine ⟨390620046702580930244935709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260413364468387286829957139 390620046702580930244935709)
    ·
      refine ⟨146482517513467848841850891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390620046702580930244935709 146482517513467848841850891)
      ·
        refine ⟨219723776270201773262776337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146482517513467848841850891 219723776270201773262776337)
        ·
          refine ⟨164792832202651329947082253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219723776270201773262776337 164792832202651329947082253)
          ·
            refine ⟨61797312075994248730155845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164792832202651329947082253 61797312075994248730155845)
            ·
              refine ⟨11586996014248921636904221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61797312075994248730155845 11586996014248921636904221)
              ·
                refine ⟨4345123505343345613839083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11586996014248921636904221 4345123505343345613839083)
                ·
                  refine ⟨6517685258015018420758625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345123505343345613839083 6517685258015018420758625)
                  ·
                    refine ⟨4888263943511263815568969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6517685258015018420758625 4888263943511263815568969)
                    ·
                      refine ⟨3666197957633447861676727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888263943511263815568969 3666197957633447861676727)
                      ·
                        rfl

theorem cell23_7139895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_7139895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139895 prefixEnd_7139895 := by exact prefixLift 7139895
  have htrace : WordTrace (prefixWord ++ tailWord_7139895) baseStart_7139895 baseEnd_7139895 := by
    simpa [prefixWord, tailWord_7139895, baseEnd_7139895] using wordTrace_append hprefix tailTrace_7139895
  have hstable : (prefixWord ++ tailWord_7139895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139895).length < 2 ^ (prefixWord ++ tailWord_7139895).sum := by decide
  have hdescent : baseEnd_7139895 < baseStart_7139895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139898 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3]
def baseStart_7139898 : Nat := 118140960795 + 7139898 * 2 ^ 59
def prefixEnd_7139898 : Nat := 4983230072969 + 3 ^ 40 * 7139898 * 2
def baseEnd_7139898 : Nat := 3666199498075411349939213

theorem tailTrace_7139898 : CollatzResearch.WordTrace tailWord_7139898 prefixEnd_7139898 3666199498075411349939213 := by
  unfold tailWord_7139898
  simp only [CollatzResearch.WordTrace]
  refine ⟨65103368471844104585579087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173608982591584278894877565 65103368471844104585579087)
  ·
    refine ⟨97655052707766156878368631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65103368471844104585579087 97655052707766156878368631)
    ·
      refine ⟨146482579061649235317552947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97655052707766156878368631 146482579061649235317552947)
      ·
        refine ⟨219723868592473852976329421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146482579061649235317552947 219723868592473852976329421)
        ·
          refine ⟨82396450722177694866123533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219723868592473852976329421 82396450722177694866123533)
          ·
            refine ⟨30898669020816635574796325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82396450722177694866123533 30898669020816635574796325)
            ·
              refine ⟨5793500441403119170274311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30898669020816635574796325 5793500441403119170274311)
              ·
                refine ⟨8690250662104678755411467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793500441403119170274311 8690250662104678755411467)
                ·
                  refine ⟨13035375993157018133117201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690250662104678755411467 13035375993157018133117201)
                  ·
                    refine ⟨9776531994867763599837901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13035375993157018133117201 9776531994867763599837901)
                    ·
                      refine ⟨3666199498075411349939213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9776531994867763599837901 3666199498075411349939213)
                      ·
                        rfl

theorem cell23_7139898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_7139898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139898 prefixEnd_7139898 := by exact prefixLift 7139898
  have htrace : WordTrace (prefixWord ++ tailWord_7139898) baseStart_7139898 baseEnd_7139898 := by
    simpa [prefixWord, tailWord_7139898, baseEnd_7139898] using wordTrace_append hprefix tailTrace_7139898
  have hstable : (prefixWord ++ tailWord_7139898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139898).length < 2 ^ (prefixWord ++ tailWord_7139898).sum := by decide
  have hdescent : baseEnd_7139898 < baseStart_7139898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139951 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 1, 4, 2]
def baseStart_7139951 : Nat := 118140960795 + 7139951 * 2 ^ 59
def prefixEnd_7139951 : Nat := 4983230072969 + 3 ^ 40 * 7139951 * 2
def baseEnd_7139951 : Nat := 3666226712550099642576469

theorem tailTrace_7139951 : CollatzResearch.WordTrace tailWord_7139951 prefixEnd_7139951 3666226712550099642576469 := by
  unfold tailWord_7139951
  simp only [CollatzResearch.WordTrace]
  refine ⟨260415406956184408393995707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173610271304122938929330471 260415406956184408393995707)
  ·
    refine ⟨390623110434276612590993561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260415406956184408393995707 390623110434276612590993561)
    ·
      refine ⟨292967332825707459443245171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390623110434276612590993561 292967332825707459443245171)
      ·
        refine ⟨439450999238561189164867757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292967332825707459443245171 439450999238561189164867757)
        ·
          refine ⟨164794124714460445936825409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439450999238561189164867757 164794124714460445936825409)
          ·
            refine ⟨123595593535845334452619057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164794124714460445936825409 123595593535845334452619057)
            ·
              refine ⟨92696695151884000839464293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123595593535845334452619057 92696695151884000839464293)
              ·
                refine ⟨17380630340978250157399555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92696695151884000839464293 17380630340978250157399555)
                ·
                  refine ⟨26070945511467375236099333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17380630340978250157399555 26070945511467375236099333)
                  ·
                    refine ⟨4888302283400132856768625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26070945511467375236099333 4888302283400132856768625)
                    ·
                      refine ⟨3666226712550099642576469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888302283400132856768625 3666226712550099642576469)
                      ·
                        rfl

theorem cell23_7139951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4, 2].length) (baseStart_7139951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139951 prefixEnd_7139951 := by exact prefixLift 7139951
  have htrace : WordTrace (prefixWord ++ tailWord_7139951) baseStart_7139951 baseEnd_7139951 := by
    simpa [prefixWord, tailWord_7139951, baseEnd_7139951] using wordTrace_append hprefix tailTrace_7139951
  have hstable : (prefixWord ++ tailWord_7139951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139951).length < 2 ^ (prefixWord ++ tailWord_7139951).sum := by decide
  have hdescent : baseEnd_7139951 < baseStart_7139951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139964 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_7139964 : Nat := 118140960795 + 7139964 * 2 ^ 59
def prefixEnd_7139964 : Nat := 4983230072969 + 3 ^ 40 * 7139964 * 2
def baseEnd_7139964 : Nat := 3666233387798608091713909

theorem tailTrace_7139964 : CollatzResearch.WordTrace tailWord_7139964 prefixEnd_7139964 3666233387798608091713909 := by
  unfold tailWord_7139964
  simp only [CollatzResearch.WordTrace]
  refine ⟨130207940552568655807109473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173610587403424874409479297 130207940552568655807109473)
  ·
    refine ⟨97655955414426491855332105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130207940552568655807109473 97655955414426491855332105)
    ·
      refine ⟨73241966560819868891499079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97655955414426491855332105 73241966560819868891499079)
      ·
        refine ⟨109862949841229803337248619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73241966560819868891499079 109862949841229803337248619)
        ·
          refine ⟨164794424761844705005872929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109862949841229803337248619 164794424761844705005872929)
          ·
            refine ⟨123595818571383528754404697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164794424761844705005872929 123595818571383528754404697)
            ·
              refine ⟨92696863928537646565803523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123595818571383528754404697 92696863928537646565803523)
              ·
                refine ⟨139045295892806469848705285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92696863928537646565803523 139045295892806469848705285)
                ·
                  refine ⟨26070992979901213096632241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139045295892806469848705285 26070992979901213096632241)
                  ·
                    refine ⟨19553244734925909822474181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26070992979901213096632241 19553244734925909822474181)
                    ·
                      refine ⟨3666233387798608091713909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19553244734925909822474181 3666233387798608091713909)
                      ·
                        rfl

theorem cell23_7139964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_7139964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139964 prefixEnd_7139964 := by exact prefixLift 7139964
  have htrace : WordTrace (prefixWord ++ tailWord_7139964) baseStart_7139964 baseEnd_7139964 := by
    simpa [prefixWord, tailWord_7139964, baseEnd_7139964] using wordTrace_append hprefix tailTrace_7139964
  have hstable : (prefixWord ++ tailWord_7139964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139964).length < 2 ^ (prefixWord ++ tailWord_7139964).sum := by decide
  have hdescent : baseEnd_7139964 < baseStart_7139964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7139968 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 4, 2, 2]
def baseStart_7139968 : Nat := 118140960795 + 7139968 * 2 ^ 59
def prefixEnd_7139968 : Nat := 4983230072969 + 3 ^ 40 * 7139968 * 2
def baseEnd_7139968 : Nat := 3666235441721226076063891

theorem tailTrace_7139968 : CollatzResearch.WordTrace tailWord_7139968 prefixEnd_7139968 3666235441721226076063891 := by
  unfold tailWord_7139968
  simp only [CollatzResearch.WordTrace]
  refine ⟨130208013498561410148682279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173610684664748546864909705 130208013498561410148682279)
  ·
    refine ⟨195312020247842115223023419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130208013498561410148682279 195312020247842115223023419)
    ·
      refine ⟨292968030371763172834535129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195312020247842115223023419 292968030371763172834535129)
      ·
        refine ⟨219726022778822379625901347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292968030371763172834535129 219726022778822379625901347)
        ·
          refine ⟨329589034168233569438852021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219726022778822379625901347 329589034168233569438852021)
          ·
            refine ⟨30898971953271897134892377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 329589034168233569438852021 30898971953271897134892377)
            ·
              refine ⟨23174228964953922851169283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30898971953271897134892377 23174228964953922851169283)
              ·
                refine ⟨34761343447430884276753925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23174228964953922851169283 34761343447430884276753925)
                ·
                  refine ⟨6517751896393290801891361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34761343447430884276753925 6517751896393290801891361)
                  ·
                    refine ⟨4888313922294968101418521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6517751896393290801891361 4888313922294968101418521)
                    ·
                      refine ⟨3666235441721226076063891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888313922294968101418521 3666235441721226076063891)
                      ·
                        rfl

theorem cell23_7139968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_7139968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7139968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7139968 prefixEnd_7139968 := by exact prefixLift 7139968
  have htrace : WordTrace (prefixWord ++ tailWord_7139968) baseStart_7139968 baseEnd_7139968 := by
    simpa [prefixWord, tailWord_7139968, baseEnd_7139968] using wordTrace_append hprefix tailTrace_7139968
  have hstable : (prefixWord ++ tailWord_7139968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7139968).length < 2 ^ (prefixWord ++ tailWord_7139968).sum := by decide
  have hdescent : baseEnd_7139968 < baseStart_7139968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7139968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140024 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_7140024 : Nat := 118140960795 + 7140024 * 2 ^ 59
def prefixEnd_7140024 : Nat := 4983230072969 + 3 ^ 40 * 7140024 * 2
def baseEnd_7140024 : Nat := 3666264196637877856963633

theorem tailTrace_7140024 : CollatzResearch.WordTrace tailWord_7140024 prefixEnd_7140024 3666264196637877856963633 := by
  unfold tailWord_7140024
  simp only [CollatzResearch.WordTrace]
  refine ⟨130209034742459970930701563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173612046323279961240935417 130209034742459970930701563)
  ·
    refine ⟨195313552113689956396052345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130209034742459970930701563 195313552113689956396052345)
    ·
      refine ⟨146485164085267467297039259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195313552113689956396052345 146485164085267467297039259)
      ·
        refine ⟨219727746127901200945558889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146485164085267467297039259 219727746127901200945558889)
        ·
          refine ⟨164795809595925900709169167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219727746127901200945558889 164795809595925900709169167)
          ·
            refine ⟨247193714393888851063753751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164795809595925900709169167 247193714393888851063753751)
            ·
              refine ⟨370790571590833276595630627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247193714393888851063753751 370790571590833276595630627)
              ·
                refine ⟨556185857386249914893445941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370790571590833276595630627 556185857386249914893445941)
                ·
                  refine ⟨52142424129960929521260557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556185857386249914893445941 52142424129960929521260557)
                  ·
                    refine ⟨19553409048735348570472709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52142424129960929521260557 19553409048735348570472709)
                    ·
                      refine ⟨3666264196637877856963633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19553409048735348570472709 3666264196637877856963633)
                      ·
                        rfl

theorem cell23_7140024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_7140024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140024 prefixEnd_7140024 := by exact prefixLift 7140024
  have htrace : WordTrace (prefixWord ++ tailWord_7140024) baseStart_7140024 baseEnd_7140024 := by
    simpa [prefixWord, tailWord_7140024, baseEnd_7140024] using wordTrace_append hprefix tailTrace_7140024
  have hstable : (prefixWord ++ tailWord_7140024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140024).length < 2 ^ (prefixWord ++ tailWord_7140024).sum := by decide
  have hdescent : baseEnd_7140024 < baseStart_7140024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140064 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 8]
def baseStart_7140064 : Nat := 118140960795 + 7140064 * 2 ^ 59
def prefixEnd_7140064 : Nat := 4983230072969 + 3 ^ 40 * 7140064 * 2
def baseEnd_7140064 : Nat := 407364970651561966718161

theorem tailTrace_7140064 : CollatzResearch.WordTrace tailWord_7140064 prefixEnd_7140064 407364970651561966718161 := by
  unfold tailWord_7140064
  simp only [CollatzResearch.WordTrace]
  refine ⟨130209764202387514346429623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173613018936516685795239497 130209764202387514346429623)
  ·
    refine ⟨195314646303581271519644435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130209764202387514346429623 195314646303581271519644435)
    ·
      refine ⟨292971969455371907279466653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195314646303581271519644435 292971969455371907279466653)
      ·
        refine ⟨109864488545764465229799995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292971969455371907279466653 109864488545764465229799995)
        ·
          refine ⟨164796732818646697844699993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109864488545764465229799995 164796732818646697844699993)
          ·
            refine ⟨123597549613985023383524995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164796732818646697844699993 123597549613985023383524995)
            ·
              refine ⟨185396324420977535075287493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123597549613985023383524995 185396324420977535075287493)
              ·
                refine ⟨34761810828933287826616405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185396324420977535075287493 34761810828933287826616405)
                ·
                  refine ⟨407364970651561966718161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34761810828933287826616405 407364970651561966718161)
                  ·
                    rfl

theorem cell23_7140064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_7140064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140064 prefixEnd_7140064 := by exact prefixLift 7140064
  have htrace : WordTrace (prefixWord ++ tailWord_7140064) baseStart_7140064 baseEnd_7140064 := by
    simpa [prefixWord, tailWord_7140064, baseEnd_7140064] using wordTrace_append hprefix tailTrace_7140064
  have hstable : (prefixWord ++ tailWord_7140064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140064).length < 2 ^ (prefixWord ++ tailWord_7140064).sum := by decide
  have hdescent : baseEnd_7140064 < baseStart_7140064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140119 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 1, 4]
def baseStart_7140119 : Nat := 118140960795 + 7140119 * 2 ^ 59
def prefixEnd_7140119 : Nat := 4983230072969 + 3 ^ 40 * 7140119 * 2
def baseEnd_7140119 : Nat := 1222104325766684995091899

theorem tailTrace_7140119 : CollatzResearch.WordTrace tailWord_7140119 prefixEnd_7140119 1222104325766684995091899 := by
  unfold tailWord_7140119
  simp only [CollatzResearch.WordTrace]
  refine ⟨260421534419575773086111411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173614356279717182057407607 260421534419575773086111411)
  ·
    refine ⟨390632301629363659629167117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260421534419575773086111411 390632301629363659629167117)
    ·
      refine ⟨146487113111011372360937669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390632301629363659629167117 146487113111011372360937669)
      ·
        refine ⟨27466333708314632317675813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146487113111011372360937669 27466333708314632317675813)
        ·
          refine ⟨5149937570308993559564215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27466333708314632317675813 5149937570308993559564215)
          ·
            refine ⟨7724906355463490339346323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149937570308993559564215 7724906355463490339346323)
            ·
              refine ⟨11587359533195235509019485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724906355463490339346323 11587359533195235509019485)
              ·
                refine ⟨4345259824948213315882307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11587359533195235509019485 4345259824948213315882307)
                ·
                  refine ⟨6517889737422319973823461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345259824948213315882307 6517889737422319973823461)
                  ·
                    refine ⟨1222104325766684995091899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6517889737422319973823461 1222104325766684995091899)
                    ·
                      rfl

theorem cell23_7140119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_7140119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140119 prefixEnd_7140119 := by exact prefixLift 7140119
  have htrace : WordTrace (prefixWord ++ tailWord_7140119) baseStart_7140119 baseEnd_7140119 := by
    simpa [prefixWord, tailWord_7140119, baseEnd_7140119] using wordTrace_append hprefix tailTrace_7140119
  have hstable : (prefixWord ++ tailWord_7140119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140119).length < 2 ^ (prefixWord ++ tailWord_7140119).sum := by decide
  have hdescent : baseEnd_7140119 < baseStart_7140119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140128 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 1, 5]
def baseStart_7140128 : Nat := 118140960795 + 7140128 * 2 ^ 59
def prefixEnd_7140128 : Nat := 4983230072969 + 3 ^ 40 * 7140128 * 2
def baseEnd_7140128 : Nat := 1222105866208648483354385

theorem tailTrace_7140128 : CollatzResearch.WordTrace tailWord_7140128 prefixEnd_7140128 1222105866208648483354385 := by
  unfold tailWord_7140128
  simp only [CollatzResearch.WordTrace]
  refine ⟨130210931338271583811594519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173614575117695445082126025 130210931338271583811594519)
  ·
    refine ⟨195316397007407375717391779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130210931338271583811594519 195316397007407375717391779)
    ·
      refine ⟨292974595511111063576087669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195316397007407375717391779 292974595511111063576087669)
      ·
        refine ⟨27466368329166662210258219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292974595511111063576087669 27466368329166662210258219)
        ·
          refine ⟨41199552493749993315387329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27466368329166662210258219 41199552493749993315387329)
          ·
            refine ⟨30899664370312494986540497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41199552493749993315387329 30899664370312494986540497)
            ·
              refine ⟨23174748277734371239905373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30899664370312494986540497 23174748277734371239905373)
              ·
                refine ⟨8690530604150389214964515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23174748277734371239905373 8690530604150389214964515)
                ·
                  refine ⟨13035795906225583822446773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690530604150389214964515 13035795906225583822446773)
                  ·
                    refine ⟨1222105866208648483354385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13035795906225583822446773 1222105866208648483354385)
                    ·
                      rfl

theorem cell23_7140128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_7140128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140128 prefixEnd_7140128 := by exact prefixLift 7140128
  have htrace : WordTrace (prefixWord ++ tailWord_7140128) baseStart_7140128 baseEnd_7140128 := by
    simpa [prefixWord, tailWord_7140128, baseEnd_7140128] using wordTrace_append hprefix tailTrace_7140128
  have hstable : (prefixWord ++ tailWord_7140128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140128).length < 2 ^ (prefixWord ++ tailWord_7140128).sum := by decide
  have hdescent : baseEnd_7140128 < baseStart_7140128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140131 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 4]
def baseStart_7140131 : Nat := 118140960795 + 7140131 * 2 ^ 59
def prefixEnd_7140131 : Nat := 4983230072969 + 3 ^ 40 * 7140131 * 2
def baseEnd_7140131 : Nat := 3666319139067908938325641

theorem tailTrace_7140131 : CollatzResearch.WordTrace tailWord_7140131 prefixEnd_7140131 3666319139067908938325641 := by
  unfold tailWord_7140131
  simp only [CollatzResearch.WordTrace]
  refine ⟨260421972095532299135548247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173614648063688199423698831 260421972095532299135548247)
  ·
    refine ⟨390632958143298448703322371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260421972095532299135548247 390632958143298448703322371)
    ·
      refine ⟨585949437214947673054983557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390632958143298448703322371 585949437214947673054983557)
      ·
        refine ⟨109865519477802688697809417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 585949437214947673054983557 109865519477802688697809417)
        ·
          refine ⟨82399139608352016523357063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109865519477802688697809417 82399139608352016523357063)
          ·
            refine ⟨123598709412528024785035595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82399139608352016523357063 123598709412528024785035595)
            ·
              refine ⟨185398064118792037177553393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123598709412528024785035595 185398064118792037177553393)
              ·
                refine ⟨139048548089094027883165045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185398064118792037177553393 139048548089094027883165045)
                ·
                  refine ⟨13035801383352565114046723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139048548089094027883165045 13035801383352565114046723)
                  ·
                    refine ⟨19553702075028847671070085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13035801383352565114046723 19553702075028847671070085)
                    ·
                      refine ⟨3666319139067908938325641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19553702075028847671070085 3666319139067908938325641)
                      ·
                        rfl

theorem cell23_7140131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_7140131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140131 prefixEnd_7140131 := by exact prefixLift 7140131
  have htrace : WordTrace (prefixWord ++ tailWord_7140131) baseStart_7140131 baseEnd_7140131 := by
    simpa [prefixWord, tailWord_7140131, baseEnd_7140131] using wordTrace_append hprefix tailTrace_7140131
  have hstable : (prefixWord ++ tailWord_7140131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140131).length < 2 ^ (prefixWord ++ tailWord_7140131).sum := by decide
  have hdescent : baseEnd_7140131 < baseStart_7140131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140142 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7140142 : Nat := 118140960795 + 7140142 * 2 ^ 59
def prefixEnd_7140142 : Nat := 4983230072969 + 3 ^ 40 * 7140142 * 2
def baseEnd_7140142 : Nat := 3666324787355108395288091

theorem tailTrace_7140142 : CollatzResearch.WordTrace tailWord_7140142 prefixEnd_7140142 3666324787355108395288091 := by
  unfold tailWord_7140142
  simp only [CollatzResearch.WordTrace]
  refine ⟨32552796662311556001774835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173614915532328298676132453 32552796662311556001774835)
  ·
    refine ⟨48829194993467334002662253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32552796662311556001774835 48829194993467334002662253)
    ·
      refine ⟨18310948122550250250998345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48829194993467334002662253 18310948122550250250998345)
      ·
        refine ⟨13733211091912687688248759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18310948122550250250998345 13733211091912687688248759)
        ·
          refine ⟨20599816637869031532373139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13733211091912687688248759 20599816637869031532373139)
          ·
            refine ⟨30899724956803547298559709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20599816637869031532373139 30899724956803547298559709)
            ·
              refine ⟨11587396858801330236959891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30899724956803547298559709 11587396858801330236959891)
              ·
                refine ⟨17381095288201995355439837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11587396858801330236959891 17381095288201995355439837)
                ·
                  refine ⟨6517910733075748258289939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17381095288201995355439837 6517910733075748258289939)
                  ·
                    refine ⟨9776866099613622387434909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6517910733075748258289939 9776866099613622387434909)
                    ·
                      refine ⟨3666324787355108395288091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9776866099613622387434909 3666324787355108395288091)
                      ·
                        rfl

theorem cell23_7140142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7140142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140142 prefixEnd_7140142 := by exact prefixLift 7140142
  have htrace : WordTrace (prefixWord ++ tailWord_7140142) baseStart_7140142 baseEnd_7140142 := by
    simpa [prefixWord, tailWord_7140142, baseEnd_7140142] using wordTrace_append hprefix tailTrace_7140142
  have hstable : (prefixWord ++ tailWord_7140142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140142).length < 2 ^ (prefixWord ++ tailWord_7140142).sum := by decide
  have hdescent : baseEnd_7140142 < baseStart_7140142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140151 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_7140151 : Nat := 118140960795 + 7140151 * 2 ^ 59
def prefixEnd_7140151 : Nat := 4983230072969 + 3 ^ 40 * 7140151 * 2
def baseEnd_7140151 : Nat := 3666329408680998860075549

theorem tailTrace_7140151 : CollatzResearch.WordTrace tailWord_7140151 prefixEnd_7140151 3666329408680998860075549 := by
  unfold tailWord_7140151
  simp only [CollatzResearch.WordTrace]
  refine ⟨260422701555459842551276307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173615134370306561700850871 260422701555459842551276307)
  ·
    refine ⟨390634052333189763826914461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260422701555459842551276307 390634052333189763826914461)
    ·
      refine ⟨146487769624946161435092923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390634052333189763826914461 146487769624946161435092923)
      ·
        refine ⟨219731654437419242152639385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146487769624946161435092923 219731654437419242152639385)
        ·
          refine ⟨164798740828064431614479539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219731654437419242152639385 164798740828064431614479539)
          ·
            refine ⟨247198111242096647421719309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164798740828064431614479539 247198111242096647421719309)
            ·
              refine ⟨92699291715786242783144741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247198111242096647421719309 92699291715786242783144741)
              ·
                refine ⟨17381117196709920521839639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92699291715786242783144741 17381117196709920521839639)
                ·
                  refine ⟨26071675795064880782759459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17381117196709920521839639 26071675795064880782759459)
                  ·
                    refine ⟨39107513692597321174139189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26071675795064880782759459 39107513692597321174139189)
                    ·
                      refine ⟨3666329408680998860075549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39107513692597321174139189 3666329408680998860075549)
                      ·
                        rfl

theorem cell23_7140151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_7140151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140151 prefixEnd_7140151 := by exact prefixLift 7140151
  have htrace : WordTrace (prefixWord ++ tailWord_7140151) baseStart_7140151 baseEnd_7140151 := by
    simpa [prefixWord, tailWord_7140151, baseEnd_7140151] using wordTrace_append hprefix tailTrace_7140151
  have hstable : (prefixWord ++ tailWord_7140151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140151).length < 2 ^ (prefixWord ++ tailWord_7140151).sum := by decide
  have hdescent : baseEnd_7140151 < baseStart_7140151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140168 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_7140168 : Nat := 118140960795 + 7140168 * 2 ^ 59
def prefixEnd_7140168 : Nat := 4983230072969 + 3 ^ 40 * 7140168 * 2
def baseEnd_7140168 : Nat := 3666338137852125293562971

theorem tailTrace_7140168 : CollatzResearch.WordTrace tailWord_7140168 prefixEnd_7140168 3666338137852125293562971 := by
  unfold tailWord_7140168
  simp only [CollatzResearch.WordTrace]
  refine ⟨130211660798199127227322579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173615547730932169636430105 130211660798199127227322579)
  ·
    refine ⟨195317491197298690840983869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130211660798199127227322579 195317491197298690840983869)
    ·
      refine ⟨73244059198987009065368951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195317491197298690840983869 73244059198987009065368951)
      ·
        refine ⟨109866088798480513598053427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73244059198987009065368951 109866088798480513598053427)
        ·
          refine ⟨164799133197720770397080141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109866088798480513598053427 164799133197720770397080141)
          ·
            refine ⟨61799674949145288898905053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164799133197720770397080141 61799674949145288898905053)
            ·
              refine ⟨23174878105929483337089395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61799674949145288898905053 23174878105929483337089395)
              ·
                refine ⟨34762317158894225005634093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23174878105929483337089395 34762317158894225005634093)
                ·
                  refine ⟨13035868934585334377112785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34762317158894225005634093 13035868934585334377112785)
                  ·
                    refine ⟨9776901700939000782834589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13035868934585334377112785 9776901700939000782834589)
                    ·
                      refine ⟨3666338137852125293562971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9776901700939000782834589 3666338137852125293562971)
                      ·
                        rfl

theorem cell23_7140168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_7140168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140168 prefixEnd_7140168 := by exact prefixLift 7140168
  have htrace : WordTrace (prefixWord ++ tailWord_7140168) baseStart_7140168 baseEnd_7140168 := by
    simpa [prefixWord, tailWord_7140168, baseEnd_7140168] using wordTrace_append hprefix tailTrace_7140168
  have hstable : (prefixWord ++ tailWord_7140168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140168).length < 2 ^ (prefixWord ++ tailWord_7140168).sum := by decide
  have hdescent : baseEnd_7140168 < baseStart_7140168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140178 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_7140178 : Nat := 118140960795 + 7140178 * 2 ^ 59
def prefixEnd_7140178 : Nat := 4983230072969 + 3 ^ 40 * 7140178 * 2
def baseEnd_7140178 : Nat := 3666343272658670254437925

theorem tailTrace_7140178 : CollatzResearch.WordTrace tailWord_7140178 prefixEnd_7140178 3666343272658670254437925 := by
  unfold tailWord_7140178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65105921581590506540627297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173615790884241350775006125 65105921581590506540627297)
  ·
    refine ⟨48829441186192879905470473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65105921581590506540627297 48829441186192879905470473)
    ·
      refine ⟨36622080889644659929102855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48829441186192879905470473 36622080889644659929102855)
      ·
        refine ⟨54933121334466989893654283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36622080889644659929102855 54933121334466989893654283)
        ·
          refine ⟨82399682001700484840481425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54933121334466989893654283 82399682001700484840481425)
          ·
            refine ⟨61799761501275363630361069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82399682001700484840481425 61799761501275363630361069)
            ·
              refine ⟨23174910562978261361385401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61799761501275363630361069 23174910562978261361385401)
              ·
                refine ⟨17381182922233696021039051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23174910562978261361385401 17381182922233696021039051)
                ·
                  refine ⟨26071774383350544031558577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17381182922233696021039051 26071774383350544031558577)
                  ·
                    refine ⟨19553830787512908023668933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26071774383350544031558577 19553830787512908023668933)
                    ·
                      refine ⟨3666343272658670254437925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19553830787512908023668933 3666343272658670254437925)
                      ·
                        rfl

theorem cell23_7140178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_7140178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140178 prefixEnd_7140178 := by exact prefixLift 7140178
  have htrace : WordTrace (prefixWord ++ tailWord_7140178) baseStart_7140178 baseEnd_7140178 := by
    simpa [prefixWord, tailWord_7140178, baseEnd_7140178] using wordTrace_append hprefix tailTrace_7140178
  have hstable : (prefixWord ++ tailWord_7140178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140178).length < 2 ^ (prefixWord ++ tailWord_7140178).sum := by decide
  have hdescent : baseEnd_7140178 < baseStart_7140178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140199 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_7140199 : Nat := 118140960795 + 7140199 * 2 ^ 59
def prefixEnd_7140199 : Nat := 4983230072969 + 3 ^ 40 * 7140199 * 2
def baseEnd_7140199 : Nat := 3666354055752414672275329

theorem tailTrace_7140199 : CollatzResearch.WordTrace tailWord_7140199 prefixEnd_7140199 3666354055752414672275329 := by
  unfold tailWord_7140199
  simp only [CollatzResearch.WordTrace]
  refine ⟨260424452259285946749023651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173616301506190631166015767 260424452259285946749023651)
  ·
    refine ⟨390636678388928920123535477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260424452259285946749023651 390636678388928920123535477)
    ·
      refine ⟨36622188598962086261581451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 390636678388928920123535477 36622188598962086261581451)
      ·
        refine ⟨54933282898443129392372177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36622188598962086261581451 54933282898443129392372177)
        ·
          refine ⟨41199962173832347044279133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54933282898443129392372177 41199962173832347044279133)
          ·
            refine ⟨15449985815187130141604675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41199962173832347044279133 15449985815187130141604675)
            ·
              refine ⟨23174978722780695212407013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15449985815187130141604675 23174978722780695212407013)
              ·
                refine ⟨4345308510521380352326315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23174978722780695212407013 4345308510521380352326315)
                ·
                  refine ⟨6517962765782070528489473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345308510521380352326315 6517962765782070528489473)
                  ·
                    refine ⟨4888472074336552896367105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6517962765782070528489473 4888472074336552896367105)
                    ·
                      refine ⟨3666354055752414672275329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888472074336552896367105 3666354055752414672275329)
                      ·
                        rfl

theorem cell23_7140199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_7140199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140199 prefixEnd_7140199 := by exact prefixLift 7140199
  have htrace : WordTrace (prefixWord ++ tailWord_7140199) baseStart_7140199 baseEnd_7140199 := by
    simpa [prefixWord, tailWord_7140199, baseEnd_7140199] using wordTrace_append hprefix tailTrace_7140199
  have hstable : (prefixWord ++ tailWord_7140199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140199).length < 2 ^ (prefixWord ++ tailWord_7140199).sum := by decide
  have hdescent : baseEnd_7140199 < baseStart_7140199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140222 : List Nat := [4, 2, 3, 1, 2, 1, 3, 7]
def baseStart_7140222 : Nat := 118140960795 + 7140222 * 2 ^ 59
def prefixEnd_7140222 : Nat := 4983230072969 + 3 ^ 40 * 7140222 * 2
def baseEnd_7140222 : Nat := 135791328363239558603249

theorem tailTrace_7140222 : CollatzResearch.WordTrace tailWord_7140222 prefixEnd_7140222 135791328363239558603249 := by
  unfold tailWord_7140222
  simp only [CollatzResearch.WordTrace]
  refine ⟨32553161392275327709638865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173616860758801747784740613 32553161392275327709638865)
  ·
    refine ⟨24414871044206495782229149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32553161392275327709638865 24414871044206495782229149)
    ·
      refine ⟨9155576641577435918335931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24414871044206495782229149 9155576641577435918335931)
      ·
        refine ⟨13733364962366153877503897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155576641577435918335931 13733364962366153877503897)
        ·
          refine ⟨10300023721774615408127923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13733364962366153877503897 10300023721774615408127923)
          ·
            refine ⟨15450035582661923112191885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10300023721774615408127923 15450035582661923112191885)
            ·
              refine ⟨5793763343498221167071957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15450035582661923112191885 5793763343498221167071957)
              ·
                refine ⟨135791328363239558603249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5793763343498221167071957 135791328363239558603249)
                ·
                  rfl

theorem cell23_7140222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_7140222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140222 prefixEnd_7140222 := by exact prefixLift 7140222
  have htrace : WordTrace (prefixWord ++ tailWord_7140222) baseStart_7140222 baseEnd_7140222 := by
    simpa [prefixWord, tailWord_7140222, baseEnd_7140222] using wordTrace_append hprefix tailTrace_7140222
  have hstable : (prefixWord ++ tailWord_7140222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140222).length < 2 ^ (prefixWord ++ tailWord_7140222).sum := by decide
  have hdescent : baseEnd_7140222 < baseStart_7140222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140241 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_7140241 : Nat := 118140960795 + 7140241 * 2 ^ 59
def prefixEnd_7140241 : Nat := 4983230072969 + 3 ^ 40 * 7140241 * 2
def baseEnd_7140241 : Nat := 3666375621939903507950135

theorem tailTrace_7140241 : CollatzResearch.WordTrace tailWord_7140241 prefixEnd_7140241 3666375621939903507950135 := by
  unfold tailWord_7140241
  simp only [CollatzResearch.WordTrace]
  refine ⟨260425984125133787922052577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173617322750089191948035051 260425984125133787922052577)
  ·
    refine ⟨195319488093850340941539433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260425984125133787922052577 195319488093850340941539433)
    ·
      refine ⟨146489616070387755706154575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195319488093850340941539433 146489616070387755706154575)
      ·
        refine ⟨219734424105581633559231863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146489616070387755706154575 219734424105581633559231863)
        ·
          refine ⟨329601636158372450338847795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219734424105581633559231863 329601636158372450338847795)
          ·
            refine ⟨494402454237558675508271693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329601636158372450338847795 494402454237558675508271693)
            ·
              refine ⟨185400920339084503315601885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494402454237558675508271693 185400920339084503315601885)
              ·
                refine ⟨69525345127156688743350707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185400920339084503315601885 69525345127156688743350707)
                ·
                  refine ⟨104288017690735033115026061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69525345127156688743350707 104288017690735033115026061)
                  ·
                    refine ⟨39108006634025637418134773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104288017690735033115026061 39108006634025637418134773)
                    ·
                      refine ⟨3666375621939903507950135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39108006634025637418134773 3666375621939903507950135)
                      ·
                        rfl

theorem cell23_7140241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_7140241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140241 prefixEnd_7140241 := by exact prefixLift 7140241
  have htrace : WordTrace (prefixWord ++ tailWord_7140241) baseStart_7140241 baseEnd_7140241 := by
    simpa [prefixWord, tailWord_7140241, baseEnd_7140241] using wordTrace_append hprefix tailTrace_7140241
  have hstable : (prefixWord ++ tailWord_7140241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140241).length < 2 ^ (prefixWord ++ tailWord_7140241).sum := by decide
  have hdescent : baseEnd_7140241 < baseStart_7140241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140276 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7140276 : Nat := 118140960795 + 7140276 * 2 ^ 59
def prefixEnd_7140276 : Nat := 4983230072969 + 3 ^ 40 * 7140276 * 2
def baseEnd_7140276 : Nat := 3666393593762810871012475

theorem tailTrace_7140276 : CollatzResearch.WordTrace tailWord_7140276 prefixEnd_7140276 3666393593762810871012475 := by
  unfold tailWord_7140276
  simp only [CollatzResearch.WordTrace]
  refine ⟨130213630340003494449788341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173618173786671325933051121 130213630340003494449788341)
  ·
    refine ⟨12207527844375327604667657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130213630340003494449788341 12207527844375327604667657)
    ·
      refine ⟨9155645883281495703500743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12207527844375327604667657 9155645883281495703500743)
      ·
        refine ⟨13733468824922243555251115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155645883281495703500743 13733468824922243555251115)
        ·
          refine ⟨20600203237383365332876673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13733468824922243555251115 20600203237383365332876673)
          ·
            refine ⟨15450152428037523999657505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20600203237383365332876673 15450152428037523999657505)
            ·
              refine ⟨11587614321028142999743129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15450152428037523999657505 11587614321028142999743129)
              ·
                refine ⟨8690710740771107249807347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11587614321028142999743129 8690710740771107249807347)
                ·
                  refine ⟨13036066111156660874711021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690710740771107249807347 13036066111156660874711021)
                  ·
                    refine ⟨4888524791683747828016633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13036066111156660874711021 4888524791683747828016633)
                    ·
                      refine ⟨3666393593762810871012475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888524791683747828016633 3666393593762810871012475)
                      ·
                        rfl

theorem cell23_7140276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7140276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140276 prefixEnd_7140276 := by exact prefixLift 7140276
  have htrace : WordTrace (prefixWord ++ tailWord_7140276) baseStart_7140276 baseEnd_7140276 := by
    simpa [prefixWord, tailWord_7140276, baseEnd_7140276] using wordTrace_append hprefix tailTrace_7140276
  have hstable : (prefixWord ++ tailWord_7140276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140276).length < 2 ^ (prefixWord ++ tailWord_7140276).sum := by decide
  have hdescent : baseEnd_7140276 < baseStart_7140276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140292 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7140292 : Nat := 118140960795 + 7140292 * 2 ^ 59
def prefixEnd_7140292 : Nat := 4983230072969 + 3 ^ 40 * 7140292 * 2
def baseEnd_7140292 : Nat := 3666401809453282808412401

theorem tailTrace_7140292 : CollatzResearch.WordTrace tailWord_7140292 prefixEnd_7140292 3666401809453282808412401 := by
  unfold tailWord_7140292
  simp only [CollatzResearch.WordTrace]
  refine ⟨130213922123974511816079565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173618562831966015754772753 130213922123974511816079565)
  ·
    refine ⟨48830220796490441931029837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130213922123974511816079565 48830220796490441931029837)
    ·
      refine ⟨18311332798683915724136189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48830220796490441931029837 18311332798683915724136189)
      ·
        refine ⟨6866749799506468396551071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18311332798683915724136189 6866749799506468396551071)
        ·
          refine ⟨10300124699259702594826607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866749799506468396551071 10300124699259702594826607)
          ·
            refine ⟨15450187048889553892239911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10300124699259702594826607 15450187048889553892239911)
            ·
              refine ⟨23175280573334330838359867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15450187048889553892239911 23175280573334330838359867)
              ·
                refine ⟨34762920860001496257539801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23175280573334330838359867 34762920860001496257539801)
                ·
                  refine ⟨26072190645001122193154851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34762920860001496257539801 26072190645001122193154851)
                  ·
                    refine ⟨39108285967501683289732277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26072190645001122193154851 39108285967501683289732277)
                    ·
                      refine ⟨3666401809453282808412401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39108285967501683289732277 3666401809453282808412401)
                      ·
                        rfl

theorem cell23_7140292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7140292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140292 prefixEnd_7140292 := by exact prefixLift 7140292
  have htrace : WordTrace (prefixWord ++ tailWord_7140292) baseStart_7140292 baseEnd_7140292 := by
    simpa [prefixWord, tailWord_7140292, baseEnd_7140292] using wordTrace_append hprefix tailTrace_7140292
  have hstable : (prefixWord ++ tailWord_7140292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140292).length < 2 ^ (prefixWord ++ tailWord_7140292).sum := by decide
  have hdescent : baseEnd_7140292 < baseStart_7140292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140295 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 5]
def baseStart_7140295 : Nat := 118140960795 + 7140295 * 2 ^ 59
def prefixEnd_7140295 : Nat := 4983230072969 + 3 ^ 40 * 7140295 * 2
def baseEnd_7140295 : Nat := 407378149988360699630543

theorem tailTrace_7140295 : CollatzResearch.WordTrace tailWord_7140295 prefixEnd_7140295 407378149988360699630543 := by
  unfold tailWord_7140295
  simp only [CollatzResearch.WordTrace]
  refine ⟨260427953666938155144518339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173618635777958770096345559 260427953666938155144518339)
  ·
    refine ⟨390641930500407232716777509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260427953666938155144518339 390641930500407232716777509)
    ·
      refine ⟨73245361968826356134395783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390641930500407232716777509 73245361968826356134395783)
      ·
        refine ⟨109868042953239534201593675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73245361968826356134395783 109868042953239534201593675)
        ·
          refine ⟨164802064429859301302390513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109868042953239534201593675 164802064429859301302390513)
          ·
            refine ⟨123601548322394475976792885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164802064429859301302390513 123601548322394475976792885)
            ·
              refine ⟨11587645155224482122824333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123601548322394475976792885 11587645155224482122824333)
              ·
                refine ⟨4345366933209180796059125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11587645155224482122824333 4345366933209180796059125)
                ·
                  refine ⟨407378149988360699630543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4345366933209180796059125 407378149988360699630543)
                  ·
                    rfl

theorem cell23_7140295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 5].length) (baseStart_7140295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140295 prefixEnd_7140295 := by exact prefixLift 7140295
  have htrace : WordTrace (prefixWord ++ tailWord_7140295) baseStart_7140295 baseEnd_7140295 := by
    simpa [prefixWord, tailWord_7140295, baseEnd_7140295] using wordTrace_append hprefix tailTrace_7140295
  have hstable : (prefixWord ++ tailWord_7140295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140295).length < 2 ^ (prefixWord ++ tailWord_7140295).sum := by decide
  have hdescent : baseEnd_7140295 < baseStart_7140295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140312 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 5]
def baseStart_7140312 : Nat := 118140960795 + 7140312 * 2 ^ 59
def prefixEnd_7140312 : Nat := 4983230072969 + 3 ^ 40 * 7140312 * 2
def baseEnd_7140312 : Nat := 407379119896263636684701

theorem tailTrace_7140312 : CollatzResearch.WordTrace tailWord_7140312 prefixEnd_7140312 407379119896263636684701 := by
  unfold tailWord_7140312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130214286853938283523943595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173619049138584378031924793 130214286853938283523943595)
  ·
    refine ⟨195321430280907425285915393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130214286853938283523943595 195321430280907425285915393)
    ·
      refine ⟨146491072710680568964436545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195321430280907425285915393 146491072710680568964436545)
      ·
        refine ⟨109868304533010426723327409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146491072710680568964436545 109868304533010426723327409)
        ·
          refine ⟨82401228399757820042495557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109868304533010426723327409 82401228399757820042495557)
          ·
            refine ⟨15450230324954591257967917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82401228399757820042495557 15450230324954591257967917)
            ·
              refine ⟨5793836371857971721737969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15450230324954591257967917 5793836371857971721737969)
              ·
                refine ⟨4345377278893478791303477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793836371857971721737969 4345377278893478791303477)
                ·
                  refine ⟨407379119896263636684701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4345377278893478791303477 407379119896263636684701)
                  ·
                    rfl

theorem cell23_7140312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 5].length) (baseStart_7140312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140312 prefixEnd_7140312 := by exact prefixLift 7140312
  have htrace : WordTrace (prefixWord ++ tailWord_7140312) baseStart_7140312 baseEnd_7140312 := by
    simpa [prefixWord, tailWord_7140312, baseEnd_7140312] using wordTrace_append hprefix tailTrace_7140312
  have hstable : (prefixWord ++ tailWord_7140312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140312).length < 2 ^ (prefixWord ++ tailWord_7140312).sum := by decide
  have hdescent : baseEnd_7140312 < baseStart_7140312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140328 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7140328 : Nat := 118140960795 + 7140328 * 2 ^ 59
def prefixEnd_7140328 : Nat := 4983230072969 + 3 ^ 40 * 7140328 * 2
def baseEnd_7140328 : Nat := 3666420294756844667562235

theorem tailTrace_7140328 : CollatzResearch.WordTrace tailWord_7140328 prefixEnd_7140328 3666420294756844667562235 := by
  unfold tailWord_7140328
  simp only [CollatzResearch.WordTrace]
  refine ⟨130214578637909300890234819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173619438183879067853646425 130214578637909300890234819)
  ·
    refine ⟨195321867956863951335352229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130214578637909300890234819 195321867956863951335352229)
    ·
      refine ⟨36622850241911990875378543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195321867956863951335352229 36622850241911990875378543)
      ·
        refine ⟨54934275362867986313067815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36622850241911990875378543 54934275362867986313067815)
        ·
          refine ⟨82401413044301979469601723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54934275362867986313067815 82401413044301979469601723)
          ·
            refine ⟨123602119566452969204402585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82401413044301979469601723 123602119566452969204402585)
            ·
              refine ⟨92701589674839726903301939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123602119566452969204402585 92701589674839726903301939)
              ·
                refine ⟨139052384512259590354952909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92701589674839726903301939 139052384512259590354952909)
                ·
                  refine ⟨52144644192097346383107341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139052384512259590354952909 52144644192097346383107341)
                  ·
                    refine ⟨19554241572036504893665253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52144644192097346383107341 19554241572036504893665253)
                    ·
                      refine ⟨3666420294756844667562235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19554241572036504893665253 3666420294756844667562235)
                      ·
                        rfl

theorem cell23_7140328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7140328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140328 prefixEnd_7140328 := by exact prefixLift 7140328
  have htrace : WordTrace (prefixWord ++ tailWord_7140328) baseStart_7140328 baseEnd_7140328 := by
    simpa [prefixWord, tailWord_7140328, baseEnd_7140328] using wordTrace_append hprefix tailTrace_7140328
  have hstable : (prefixWord ++ tailWord_7140328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140328).length < 2 ^ (prefixWord ++ tailWord_7140328).sum := by decide
  have hdescent : baseEnd_7140328 < baseStart_7140328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140342 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_7140342 : Nat := 118140960795 + 7140342 * 2 ^ 59
def prefixEnd_7140342 : Nat := 4983230072969 + 3 ^ 40 * 7140342 * 2
def baseEnd_7140342 : Nat := 1222142494495335870929057

theorem tailTrace_7140342 : CollatzResearch.WordTrace tailWord_7140342 prefixEnd_7140342 1222142494495335870929057 := by
  unfold tailWord_7140342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16276854243610492635717455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173619778598511921447652853 16276854243610492635717455)
  ·
    refine ⟨24415281365415738953576183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16276854243610492635717455 24415281365415738953576183)
    ·
      refine ⟨36622922048123608430364275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24415281365415738953576183 36622922048123608430364275)
      ·
        refine ⟨54934383072185412645546413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36622922048123608430364275 54934383072185412645546413)
        ·
          refine ⟨20600393652069529742079905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54934383072185412645546413 20600393652069529742079905)
          ·
            refine ⟨15450295239052147306559929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20600393652069529742079905 15450295239052147306559929)
            ·
              refine ⟨11587721429289110479919947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15450295239052147306559929 11587721429289110479919947)
              ·
                refine ⟨17381582143933665719879921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11587721429289110479919947 17381582143933665719879921)
                ·
                  refine ⟨13036186607950249289909941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17381582143933665719879921 13036186607950249289909941)
                  ·
                    refine ⟨1222142494495335870929057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13036186607950249289909941 1222142494495335870929057)
                    ·
                      rfl

theorem cell23_7140342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_7140342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140342 prefixEnd_7140342 := by exact prefixLift 7140342
  have htrace : WordTrace (prefixWord ++ tailWord_7140342) baseStart_7140342 baseEnd_7140342 := by
    simpa [prefixWord, tailWord_7140342, baseEnd_7140342] using wordTrace_append hprefix tailTrace_7140342
  have hstable : (prefixWord ++ tailWord_7140342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140342).length < 2 ^ (prefixWord ++ tailWord_7140342).sum := by decide
  have hdescent : baseEnd_7140342 < baseStart_7140342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140345 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_7140345 : Nat := 118140960795 + 7140345 * 2 ^ 59
def prefixEnd_7140345 : Nat := 4983230072969 + 3 ^ 40 * 7140345 * 2
def baseEnd_7140345 : Nat := 3666429023927971101049657

theorem tailTrace_7140345 : CollatzResearch.WordTrace tailWord_7140345 prefixEnd_7140345 3666429023927971101049657 := by
  unfold tailWord_7140345
  simp only [CollatzResearch.WordTrace]
  refine ⟨260429777316757013683838489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173619851544504675789225659 260429777316757013683838489)
  ·
    refine ⟨195322332987567760262878867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260429777316757013683838489 195322332987567760262878867)
    ·
      refine ⟨292983499481351640394318301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195322332987567760262878867 292983499481351640394318301)
      ·
        refine ⟨109868812305506865147869363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292983499481351640394318301 109868812305506865147869363)
        ·
          refine ⟨164803218458260297721804045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109868812305506865147869363 164803218458260297721804045)
          ·
            refine ⟨61801206921847611645676517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164803218458260297721804045 61801206921847611645676517)
            ·
              refine ⟨11587726297846427183564347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61801206921847611645676517 11587726297846427183564347)
              ·
                refine ⟨17381589446769640775346521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11587726297846427183564347 17381589446769640775346521)
                ·
                  refine ⟨13036192085077230581509891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17381589446769640775346521 13036192085077230581509891)
                  ·
                    refine ⟨19554288127615845872264837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13036192085077230581509891 19554288127615845872264837)
                    ·
                      refine ⟨3666429023927971101049657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19554288127615845872264837 3666429023927971101049657)
                      ·
                        rfl

theorem cell23_7140345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_7140345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140345 prefixEnd_7140345 := by exact prefixLift 7140345
  have htrace : WordTrace (prefixWord ++ tailWord_7140345) baseStart_7140345 baseEnd_7140345 := by
    simpa [prefixWord, tailWord_7140345, baseEnd_7140345] using wordTrace_append hprefix tailTrace_7140345
  have hstable : (prefixWord ++ tailWord_7140345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140345).length < 2 ^ (prefixWord ++ tailWord_7140345).sum := by decide
  have hdescent : baseEnd_7140345 < baseStart_7140345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140385 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 6]
def baseStart_7140385 : Nat := 118140960795 + 7140385 * 2 ^ 59
def prefixEnd_7140385 : Nat := 4983230072969 + 3 ^ 40 * 7140385 * 2
def baseEnd_7140385 : Nat := 407383284794905660505497

theorem tailTrace_7140385 : CollatzResearch.WordTrace tailWord_7140385 prefixEnd_7140385 407383284794905660505497 := by
  unfold tailWord_7140385
  simp only [CollatzResearch.WordTrace]
  refine ⟨260431236236612100515294609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173620824157741400343529739 260431236236612100515294609)
  ·
    refine ⟨195323427177459075386470957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260431236236612100515294609 195323427177459075386470957)
    ·
      refine ⟨73246285191547153269926609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195323427177459075386470957 73246285191547153269926609)
      ·
        refine ⟨54934713893660364952444957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73246285191547153269926609 54934713893660364952444957)
        ·
          refine ⟨20600517710122636857166859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54934713893660364952444957 20600517710122636857166859)
          ·
            refine ⟨30900776565183955285750289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20600517710122636857166859 30900776565183955285750289)
            ·
              refine ⟨23175582423887966464312717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30900776565183955285750289 23175582423887966464312717)
              ·
                refine ⟨8690843408957987424117269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23175582423887966464312717 8690843408957987424117269)
                ·
                  refine ⟨407383284794905660505497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8690843408957987424117269 407383284794905660505497)
                  ·
                    rfl

theorem cell23_7140385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 6].length) (baseStart_7140385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140385 prefixEnd_7140385 := by exact prefixLift 7140385
  have htrace : WordTrace (prefixWord ++ tailWord_7140385) baseStart_7140385 baseEnd_7140385 := by
    simpa [prefixWord, tailWord_7140385, baseEnd_7140385] using wordTrace_append hprefix tailTrace_7140385
  have hstable : (prefixWord ++ tailWord_7140385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140385).length < 2 ^ (prefixWord ++ tailWord_7140385).sum := by decide
  have hdescent : baseEnd_7140385 < baseStart_7140385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140406 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_7140406 : Nat := 118140960795 + 7140406 * 2 ^ 59
def prefixEnd_7140406 : Nat := 4983230072969 + 3 ^ 40 * 7140406 * 2
def baseEnd_7140406 : Nat := 1222153448749298454128959

theorem tailTrace_7140406 : CollatzResearch.WordTrace tailWord_7140406 prefixEnd_7140406 1222153448749298454128959 := by
  unfold tailWord_7140406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277000135596001318863067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173621334779690680734539381 16277000135596001318863067)
  ·
    refine ⟨24415500203394001978294601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16277000135596001318863067 24415500203394001978294601)
    ·
      refine ⟨18311625152545501483720951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24415500203394001978294601 18311625152545501483720951)
      ·
        refine ⟨27467437728818252225581427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18311625152545501483720951 27467437728818252225581427)
        ·
          refine ⟨41201156593227378338372141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27467437728818252225581427 41201156593227378338372141)
          ·
            refine ⟨15450433722460266876889553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41201156593227378338372141 15450433722460266876889553)
            ·
              refine ⟨11587825291845200157667165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15450433722460266876889553 11587825291845200157667165)
              ·
                refine ⟨4345434484441950059125187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11587825291845200157667165 4345434484441950059125187)
                ·
                  refine ⟨6518151726662925088687781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345434484441950059125187 6518151726662925088687781)
                  ·
                    refine ⟨1222153448749298454128959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6518151726662925088687781 1222153448749298454128959)
                    ·
                      rfl

theorem cell23_7140406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_7140406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140406 prefixEnd_7140406 := by exact prefixLift 7140406
  have htrace : WordTrace (prefixWord ++ tailWord_7140406) baseStart_7140406 baseEnd_7140406 := by
    simpa [prefixWord, tailWord_7140406, baseEnd_7140406] using wordTrace_append hprefix tailTrace_7140406
  have hstable : (prefixWord ++ tailWord_7140406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140406).length < 2 ^ (prefixWord ++ tailWord_7140406).sum := by decide
  have hdescent : baseEnd_7140406 < baseStart_7140406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140422 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7140422 : Nat := 118140960795 + 7140422 * 2 ^ 59
def prefixEnd_7140422 : Nat := 4983230072969 + 3 ^ 40 * 7140422 * 2
def baseEnd_7140422 : Nat := 3666468561938367299786803

theorem tailTrace_7140422 : CollatzResearch.WordTrace tailWord_7140422 prefixEnd_7140422 3666468561938367299786803 := by
  unfold tailWord_7140422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138518304296189244824735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173621723824985370556261013 8138518304296189244824735)
  ·
    refine ⟨12207777456444283867237103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8138518304296189244824735 12207777456444283867237103)
    ·
      refine ⟨18311666184666425800855655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12207777456444283867237103 18311666184666425800855655)
      ·
        refine ⟨27467499276999638701283483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18311666184666425800855655 27467499276999638701283483)
        ·
          refine ⟨41201248915499458051925225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27467499276999638701283483 41201248915499458051925225)
          ·
            refine ⟨30900936686624593538943919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41201248915499458051925225 30900936686624593538943919)
            ·
              refine ⟨46351405029936890308415879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30900936686624593538943919 46351405029936890308415879)
              ·
                refine ⟨69527107544905335462623819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46351405029936890308415879 69527107544905335462623819)
                ·
                  refine ⟨104290661317358003193935729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69527107544905335462623819 104290661317358003193935729)
                  ·
                    refine ⟨78217995988018502395451797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104290661317358003193935729 78217995988018502395451797)
                    ·
                      refine ⟨3666468561938367299786803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78217995988018502395451797 3666468561938367299786803)
                      ·
                        rfl

theorem cell23_7140422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7140422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140422 prefixEnd_7140422 := by exact prefixLift 7140422
  have htrace : WordTrace (prefixWord ++ tailWord_7140422) baseStart_7140422 baseEnd_7140422 := by
    simpa [prefixWord, tailWord_7140422, baseEnd_7140422] using wordTrace_append hprefix tailTrace_7140422
  have hstable : (prefixWord ++ tailWord_7140422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140422).length < 2 ^ (prefixWord ++ tailWord_7140422).sum := by decide
  have hdescent : baseEnd_7140422 < baseStart_7140422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140429 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_7140429 : Nat := 118140960795 + 7140429 * 2 ^ 59
def prefixEnd_7140429 : Nat := 4983230072969 + 3 ^ 40 * 7140429 * 2
def baseEnd_7140429 : Nat := 3666472156302948772399271

theorem tailTrace_7140429 : CollatzResearch.WordTrace tailWord_7140429 prefixEnd_7140429 3666472156302948772399271 := by
  unfold tailWord_7140429
  simp only [CollatzResearch.WordTrace]
  refine ⟨260432841048452696029896341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173621894032301797353264227 260432841048452696029896341)
  ·
    refine ⟨12207789424146220126401391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260432841048452696029896341 12207789424146220126401391)
    ·
      refine ⟨18311684136219330189602087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12207789424146220126401391 18311684136219330189602087)
      ·
        refine ⟨27467526204328995284403131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18311684136219330189602087 27467526204328995284403131)
        ·
          refine ⟨41201289306493492926604697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27467526204328995284403131 41201289306493492926604697)
          ·
            refine ⟨30900966979870119694953523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41201289306493492926604697 30900966979870119694953523)
            ·
              refine ⟨46351450469805179542430285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30900966979870119694953523 46351450469805179542430285)
              ·
                refine ⟨17381793926176942328411357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46351450469805179542430285 17381793926176942328411357)
                ·
                  refine ⟨6518172722316353373154259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17381793926176942328411357 6518172722316353373154259)
                  ·
                    refine ⟨9777259083474530059731389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6518172722316353373154259 9777259083474530059731389)
                    ·
                      refine ⟨3666472156302948772399271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777259083474530059731389 3666472156302948772399271)
                      ·
                        rfl

theorem cell23_7140429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_7140429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140429 prefixEnd_7140429 := by exact prefixLift 7140429
  have htrace : WordTrace (prefixWord ++ tailWord_7140429) baseStart_7140429 baseEnd_7140429 := by
    simpa [prefixWord, tailWord_7140429, baseEnd_7140429] using wordTrace_append hprefix tailTrace_7140429
  have hstable : (prefixWord ++ tailWord_7140429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140429).length < 2 ^ (prefixWord ++ tailWord_7140429).sum := by decide
  have hdescent : baseEnd_7140429 < baseStart_7140429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140435 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 6, 2]
def baseStart_7140435 : Nat := 118140960795 + 7140435 * 2 ^ 59
def prefixEnd_7140435 : Nat := 4983230072969 + 3 ^ 40 * 7140435 * 2
def baseEnd_7140435 : Nat := 3666475237186875748924243

theorem tailTrace_7140435 : CollatzResearch.WordTrace tailWord_7140435 prefixEnd_7140435 3666475237186875748924243 := by
  unfold tailWord_7140435
  simp only [CollatzResearch.WordTrace]
  refine ⟨260433059886430959054614759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173622039924287306036409839 260433059886430959054614759)
  ·
    refine ⟨390649589829646438581922139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260433059886430959054614759 390649589829646438581922139)
    ·
      refine ⟨585974384744469657872883209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390649589829646438581922139 585974384744469657872883209)
      ·
        refine ⟨439480788558352243404662407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585974384744469657872883209 439480788558352243404662407)
        ·
          refine ⟨659221182837528365106993611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439480788558352243404662407 659221182837528365106993611)
          ·
            refine ⟨988831774256292547660490417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659221182837528365106993611 988831774256292547660490417)
            ·
              refine ⟨741623830692219410745367813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988831774256292547660490417 741623830692219410745367813)
              ·
                refine ⟨139054468254791139514756465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741623830692219410745367813 139054468254791139514756465)
                ·
                  refine ⟨104290851191093354636067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139054468254791139514756465 104290851191093354636067349)
                  ·
                    refine ⟨4888633649582500998565657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104290851191093354636067349 4888633649582500998565657)
                    ·
                      refine ⟨3666475237186875748924243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888633649582500998565657 3666475237186875748924243)
                      ·
                        rfl

theorem cell23_7140435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6, 2].length) (baseStart_7140435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140435 prefixEnd_7140435 := by exact prefixLift 7140435
  have htrace : WordTrace (prefixWord ++ tailWord_7140435) baseStart_7140435 baseEnd_7140435 := by
    simpa [prefixWord, tailWord_7140435, baseEnd_7140435] using wordTrace_append hprefix tailTrace_7140435
  have hstable : (prefixWord ++ tailWord_7140435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140435).length < 2 ^ (prefixWord ++ tailWord_7140435).sum := by decide
  have hdescent : baseEnd_7140435 < baseStart_7140435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140462 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_7140462 : Nat := 118140960795 + 7140462 * 2 ^ 59
def prefixEnd_7140462 : Nat := 4983230072969 + 3 ^ 40 * 7140462 * 2
def baseEnd_7140462 : Nat := 1222163033721515714428873

theorem tailTrace_7140462 : CollatzResearch.WordTrace tailWord_7140462 prefixEnd_7140462 1222163033721515714428873 := by
  unfold tailWord_7140462
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554255582166642833230955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173622696438222095110565093 32554255582166642833230955)
  ·
    refine ⟨48831383373249964249846433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32554255582166642833230955 48831383373249964249846433)
    ·
      refine ⟨36623537529937473187384825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48831383373249964249846433 36623537529937473187384825)
      ·
        refine ⟨27467653147453104890538619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36623537529937473187384825 27467653147453104890538619)
        ·
          refine ⟨41201479721179657335807929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27467653147453104890538619 41201479721179657335807929)
          ·
            refine ⟨30901109790884743001855947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41201479721179657335807929 30901109790884743001855947)
            ·
              refine ⟨46351664686327114502783921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30901109790884743001855947 46351664686327114502783921)
              ·
                refine ⟨34763748514745335877087941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46351664686327114502783921 34763748514745335877087941)
                ·
                  refine ⟨6518202846514750476953989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34763748514745335877087941 6518202846514750476953989)
                  ·
                    refine ⟨1222163033721515714428873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6518202846514750476953989 1222163033721515714428873)
                    ·
                      rfl

theorem cell23_7140462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_7140462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140462 prefixEnd_7140462 := by exact prefixLift 7140462
  have htrace : WordTrace (prefixWord ++ tailWord_7140462) baseStart_7140462 baseEnd_7140462 := by
    simpa [prefixWord, tailWord_7140462, baseEnd_7140462] using wordTrace_append hprefix tailTrace_7140462
  have hstable : (prefixWord ++ tailWord_7140462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140462).length < 2 ^ (prefixWord ++ tailWord_7140462).sum := by decide
  have hdescent : baseEnd_7140462 < baseStart_7140462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140472 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_7140472 : Nat := 118140960795 + 7140472 * 2 ^ 59
def prefixEnd_7140472 : Nat := 4983230072969 + 3 ^ 40 * 7140472 * 2
def baseEnd_7140472 : Nat := 3666494235971092104161573

theorem tailTrace_7140472 : CollatzResearch.WordTrace tailWord_7140472 prefixEnd_7140472 3666494235971092104161573 := by
  unfold tailWord_7140472
  simp only [CollatzResearch.WordTrace]
  refine ⟨130217204693648457186855835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173622939591531276249141113 130217204693648457186855835)
  ·
    refine ⟨195325807040472685780283753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130217204693648457186855835 195325807040472685780283753)
    ·
      refine ⟨146494355280354514335212815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195325807040472685780283753 146494355280354514335212815)
      ·
        refine ⟨219741532920531771502819223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146494355280354514335212815 219741532920531771502819223)
        ·
          refine ⟨329612299380797657254228835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219741532920531771502819223 329612299380797657254228835)
          ·
            refine ⟨494418449071196485881343253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329612299380797657254228835 494418449071196485881343253)
            ·
              refine ⟨23175864800212335275687965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 494418449071196485881343253 23175864800212335275687965)
              ·
                refine ⟨8690949300079625728382987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23175864800212335275687965 8690949300079625728382987)
                ·
                  refine ⟨13036423950119438592574481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690949300079625728382987 13036423950119438592574481)
                  ·
                    refine ⟨9777317962589578944430861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13036423950119438592574481 9777317962589578944430861)
                    ·
                      refine ⟨3666494235971092104161573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777317962589578944430861 3666494235971092104161573)
                      ·
                        rfl

theorem cell23_7140472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_7140472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140472 prefixEnd_7140472 := by exact prefixLift 7140472
  have htrace : WordTrace (prefixWord ++ tailWord_7140472) baseStart_7140472 baseEnd_7140472 := by
    simpa [prefixWord, tailWord_7140472, baseEnd_7140472] using wordTrace_append hprefix tailTrace_7140472
  have hstable : (prefixWord ++ tailWord_7140472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140472).length < 2 ^ (prefixWord ++ tailWord_7140472).sum := by decide
  have hdescent : baseEnd_7140472 < baseStart_7140472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140506 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7140506 : Nat := 118140960795 + 7140506 * 2 ^ 59
def prefixEnd_7140506 : Nat := 4983230072969 + 3 ^ 40 * 7140506 * 2
def baseEnd_7140506 : Nat := 3666511694313344971136417

theorem tailTrace_7140506 : CollatzResearch.WordTrace tailWord_7140506 prefixEnd_7140506 3666511694313344971136417 := by
  unfold tailWord_7140506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65108912367293434545112343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173623766312782492120299581 65108912367293434545112343)
  ·
    refine ⟨97663368550940151817668515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65108912367293434545112343 97663368550940151817668515)
    ·
      refine ⟨146495052826410227726502773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97663368550940151817668515 146495052826410227726502773)
      ·
        refine ⟨13733911202475958849359635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146495052826410227726502773 13733911202475958849359635)
        ·
          refine ⟨20600866803713938274039453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13733911202475958849359635 20600866803713938274039453)
          ·
            refine ⟨7725325051392726852764795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20600866803713938274039453 7725325051392726852764795)
            ·
              refine ⟨11587987577089090279147193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725325051392726852764795 11587987577089090279147193)
              ·
                refine ⟨8690990682816817709360395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11587987577089090279147193 8690990682816817709360395)
                ·
                  refine ⟨13036486024225226564040593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690990682816817709360395 13036486024225226564040593)
                  ·
                    refine ⟨9777364518168919923030445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13036486024225226564040593 9777364518168919923030445)
                    ·
                      refine ⟨3666511694313344971136417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777364518168919923030445 3666511694313344971136417)
                      ·
                        rfl

theorem cell23_7140506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7140506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140506 prefixEnd_7140506 := by exact prefixLift 7140506
  have htrace : WordTrace (prefixWord ++ tailWord_7140506) baseStart_7140506 baseEnd_7140506 := by
    simpa [prefixWord, tailWord_7140506, baseEnd_7140506] using wordTrace_append hprefix tailTrace_7140506
  have hstable : (prefixWord ++ tailWord_7140506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140506).length < 2 ^ (prefixWord ++ tailWord_7140506).sum := by decide
  have hdescent : baseEnd_7140506 < baseStart_7140506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140519 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_7140519 : Nat := 118140960795 + 7140519 * 2 ^ 59
def prefixEnd_7140519 : Nat := 4983230072969 + 3 ^ 40 * 7140519 * 2
def baseEnd_7140519 : Nat := 3666518369561853420273857

theorem tailTrace_7140519 : CollatzResearch.WordTrace tailWord_7140519 prefixEnd_7140519 3666518369561853420273857 := by
  unfold tailWord_7140519
  simp only [CollatzResearch.WordTrace]
  refine ⟨260436123618126641400672611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173624082412084427600448407 260436123618126641400672611)
  ·
    refine ⟨390654185427189962101008917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260436123618126641400672611 390654185427189962101008917)
    ·
      refine ⟨18311914941899529473484793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 390654185427189962101008917 18311914941899529473484793)
      ·
        refine ⟨13733936206424647105113595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18311914941899529473484793 13733936206424647105113595)
        ·
          refine ⟨20600904309636970657670393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13733936206424647105113595 20600904309636970657670393)
          ·
            refine ⟨15450678232227727993252795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20600904309636970657670393 15450678232227727993252795)
            ·
              refine ⟨23176017348341591989879193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15450678232227727993252795 23176017348341591989879193)
              ·
                refine ⟨17382013011256193992409395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23176017348341591989879193 17382013011256193992409395)
                ·
                  refine ⟨26073019516884290988614093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17382013011256193992409395 26073019516884290988614093)
                  ·
                    refine ⟨9777382318831609120730285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26073019516884290988614093 9777382318831609120730285)
                    ·
                      refine ⟨3666518369561853420273857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777382318831609120730285 3666518369561853420273857)
                      ·
                        rfl

theorem cell23_7140519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_7140519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140519 prefixEnd_7140519 := by exact prefixLift 7140519
  have htrace : WordTrace (prefixWord ++ tailWord_7140519) baseStart_7140519 baseEnd_7140519 := by
    simpa [prefixWord, tailWord_7140519, baseEnd_7140519] using wordTrace_append hprefix tailTrace_7140519
  have hstable : (prefixWord ++ tailWord_7140519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140519).length < 2 ^ (prefixWord ++ tailWord_7140519).sum := by decide
  have hdescent : baseEnd_7140519 < baseStart_7140519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140535 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 2, 6]
def baseStart_7140535 : Nat := 118140960795 + 7140535 * 2 ^ 59
def prefixEnd_7140535 : Nat := 4983230072969 + 3 ^ 40 * 7140535 * 2
def baseEnd_7140535 : Nat := 1222175528417441785891261

theorem tailTrace_7140535 : CollatzResearch.WordTrace tailWord_7140535 prefixEnd_7140535 1222175528417441785891261 := by
  unfold tailWord_7140535
  simp only [CollatzResearch.WordTrace]
  refine ⟨260436707186068676133255059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173624471457379117422170039 260436707186068676133255059)
  ·
    refine ⟨390655060779103014199882589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260436707186068676133255059 390655060779103014199882589)
    ·
      refine ⟨146495647792163630324955971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390655060779103014199882589 146495647792163630324955971)
      ·
        refine ⟨219743471688245445487433957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146495647792163630324955971 219743471688245445487433957)
        ·
          refine ⟨41201900941546021028893867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219743471688245445487433957 41201900941546021028893867)
          ·
            refine ⟨61802851412319031543340801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41201900941546021028893867 61802851412319031543340801)
            ·
              refine ⟨46352138559239273657505601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61802851412319031543340801 46352138559239273657505601)
              ·
                refine ⟨34764103919429455243129201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46352138559239273657505601 34764103919429455243129201)
                ·
                  refine ⟨26073077939572091432346901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34764103919429455243129201 26073077939572091432346901)
                  ·
                    refine ⟨1222175528417441785891261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26073077939572091432346901 1222175528417441785891261)
                    ·
                      rfl

theorem cell23_7140535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_7140535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140535 prefixEnd_7140535 := by exact prefixLift 7140535
  have htrace : WordTrace (prefixWord ++ tailWord_7140535) baseStart_7140535 baseEnd_7140535 := by
    simpa [prefixWord, tailWord_7140535, baseEnd_7140535] using wordTrace_append hprefix tailTrace_7140535
  have hstable : (prefixWord ++ tailWord_7140535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140535).length < 2 ^ (prefixWord ++ tailWord_7140535).sum := by decide
  have hdescent : baseEnd_7140535 < baseStart_7140535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140542 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_7140542 : Nat := 118140960795 + 7140542 * 2 ^ 59
def prefixEnd_7140542 : Nat := 4983230072969 + 3 ^ 40 * 7140542 * 2
def baseEnd_7140542 : Nat := 3666530179616906830286251

theorem tailTrace_7140542 : CollatzResearch.WordTrace tailWord_7140542 prefixEnd_7140542 3666530179616906830286251 := by
  unfold tailWord_7140542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554620312130414541094985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173624641664695544219173253 32554620312130414541094985)
  ·
    refine ⟨24415965234097810905821239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32554620312130414541094985 24415965234097810905821239)
    ·
      refine ⟨36623947851146716358731859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24415965234097810905821239 36623947851146716358731859)
      ·
        refine ⟨54935921776720074538097789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36623947851146716358731859 54935921776720074538097789)
        ·
          refine ⟨20600970666270027951786671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54935921776720074538097789 20600970666270027951786671)
          ·
            refine ⟨30901455999405041927680007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20600970666270027951786671 30901455999405041927680007)
            ·
              refine ⟨46352183999107562891520011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30901455999405041927680007 46352183999107562891520011)
              ·
                refine ⟨69528275998661344337280017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46352183999107562891520011 69528275998661344337280017)
                ·
                  refine ⟨52146206998996008252960013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69528275998661344337280017 52146206998996008252960013)
                  ·
                    refine ⟨19554827624623503094860005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52146206998996008252960013 19554827624623503094860005)
                    ·
                      refine ⟨3666530179616906830286251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19554827624623503094860005 3666530179616906830286251)
                      ·
                        rfl

theorem cell23_7140542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_7140542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140542 prefixEnd_7140542 := by exact prefixLift 7140542
  have htrace : WordTrace (prefixWord ++ tailWord_7140542) baseStart_7140542 baseEnd_7140542 := by
    simpa [prefixWord, tailWord_7140542, baseEnd_7140542] using wordTrace_append hprefix tailTrace_7140542
  have hstable : (prefixWord ++ tailWord_7140542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140542).length < 2 ^ (prefixWord ++ tailWord_7140542).sum := by decide
  have hdescent : baseEnd_7140542 < baseStart_7140542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140562 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_7140562 : Nat := 118140960795 + 7140562 * 2 ^ 59
def prefixEnd_7140562 : Nat := 4983230072969 + 3 ^ 40 * 7140562 * 2
def baseEnd_7140562 : Nat := 3666540449229996752036159

theorem tailTrace_7140562 : CollatzResearch.WordTrace tailWord_7140562 prefixEnd_7140562 3666540449229996752036159 := by
  unfold tailWord_7140562
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109422989242714936121985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173625127971313906496325293 65109422989242714936121985)
  ·
    refine ⟨48832067241932036202091489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65109422989242714936121985 48832067241932036202091489)
    ·
      refine ⟨36624050431449027151568617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48832067241932036202091489 36624050431449027151568617)
      ·
        refine ⟨27468037823586770363676463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36624050431449027151568617 27468037823586770363676463)
        ·
          refine ⟨41202056735380155545514695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27468037823586770363676463 41202056735380155545514695)
          ·
            refine ⟨61803085103070233318272043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41202056735380155545514695 61803085103070233318272043)
            ·
              refine ⟨92704627654605349977408065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61803085103070233318272043 92704627654605349977408065)
              ·
                refine ⟨69528470740954012483056049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92704627654605349977408065 69528470740954012483056049)
                ·
                  refine ⟨52146353055715509362292037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69528470740954012483056049 52146353055715509362292037)
                  ·
                    refine ⟨9777441197946658005429757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52146353055715509362292037 9777441197946658005429757)
                    ·
                      refine ⟨3666540449229996752036159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777441197946658005429757 3666540449229996752036159)
                      ·
                        rfl

theorem cell23_7140562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_7140562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140562 prefixEnd_7140562 := by exact prefixLift 7140562
  have htrace : WordTrace (prefixWord ++ tailWord_7140562) baseStart_7140562 baseEnd_7140562 := by
    simpa [prefixWord, tailWord_7140562, baseEnd_7140562] using wordTrace_append hprefix tailTrace_7140562
  have hstable : (prefixWord ++ tailWord_7140562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140562).length < 2 ^ (prefixWord ++ tailWord_7140562).sum := by decide
  have hdescent : baseEnd_7140562 < baseStart_7140562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140610 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7140610 : Nat := 118140960795 + 7140610 * 2 ^ 59
def prefixEnd_7140610 : Nat := 4983230072969 + 3 ^ 40 * 7140610 * 2
def baseEnd_7140610 : Nat := 3666565096301412564235939

theorem tailTrace_7140610 : CollatzResearch.WordTrace tailWord_7140610 prefixEnd_7140610 3666565096301412564235939 := by
  unfold tailWord_7140610
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109860665199240985558821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173626295107197975961490189 65109860665199240985558821)
  ·
    refine ⟨12208098874724857684792279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65109860665199240985558821 12208098874724857684792279)
    ·
      refine ⟨18312148312087286527188419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12208098874724857684792279 18312148312087286527188419)
      ·
        refine ⟨27468222468130929790782629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18312148312087286527188419 27468222468130929790782629)
        ·
          refine ⟨5150291712774549335771743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27468222468130929790782629 5150291712774549335771743)
          ·
            refine ⟨7725437569161824003657615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150291712774549335771743 7725437569161824003657615)
            ·
              refine ⟨11588156353742736005486423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725437569161824003657615 11588156353742736005486423)
              ·
                refine ⟨17382234530614104008229635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11588156353742736005486423 17382234530614104008229635)
                ·
                  refine ⟨26073351795921156012344453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17382234530614104008229635 26073351795921156012344453)
                  ·
                    refine ⟨4888753461735216752314585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26073351795921156012344453 4888753461735216752314585)
                    ·
                      refine ⟨3666565096301412564235939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888753461735216752314585 3666565096301412564235939)
                      ·
                        rfl

theorem cell23_7140610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7140610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140610 prefixEnd_7140610 := by exact prefixLift 7140610
  have htrace : WordTrace (prefixWord ++ tailWord_7140610) baseStart_7140610 baseEnd_7140610 := by
    simpa [prefixWord, tailWord_7140610, baseEnd_7140610] using wordTrace_append hprefix tailTrace_7140610
  have hstable : (prefixWord ++ tailWord_7140610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140610).length < 2 ^ (prefixWord ++ tailWord_7140610).sum := by decide
  have hdescent : baseEnd_7140610 < baseStart_7140610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140612 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_7140612 : Nat := 118140960795 + 7140612 * 2 ^ 59
def prefixEnd_7140612 : Nat := 4983230072969 + 3 ^ 40 * 7140612 * 2
def baseEnd_7140612 : Nat := 1222188707754240518803643

theorem tailTrace_7140612 : CollatzResearch.WordTrace tailWord_7140612 prefixEnd_7140612 1222188707754240518803643 := by
  unfold tailWord_7140612
  simp only [CollatzResearch.WordTrace]
  refine ⟨130219757803394859141904045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173626343737859812189205393 130219757803394859141904045)
  ·
    refine ⟨48832409176273072178214017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130219757803394859141904045 48832409176273072178214017)
    ·
      refine ⟨36624306882204804133660513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48832409176273072178214017 36624306882204804133660513)
      ·
        refine ⟨27468230161653603100245385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36624306882204804133660513 27468230161653603100245385)
        ·
          refine ⟨20601172621240202325184039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27468230161653603100245385 20601172621240202325184039)
          ·
            refine ⟨30901758931860303487776059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20601172621240202325184039 30901758931860303487776059)
            ·
              refine ⟨46352638397790455231664089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30901758931860303487776059 46352638397790455231664089)
              ·
                refine ⟨34764478798342841423748067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46352638397790455231664089 34764478798342841423748067)
                ·
                  refine ⟨52146718197514262135622101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34764478798342841423748067 52146718197514262135622101)
                  ·
                    refine ⟨1222188707754240518803643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52146718197514262135622101 1222188707754240518803643)
                    ·
                      rfl

theorem cell23_7140612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_7140612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140612 prefixEnd_7140612 := by exact prefixLift 7140612
  have htrace : WordTrace (prefixWord ++ tailWord_7140612) baseStart_7140612 baseEnd_7140612 := by
    simpa [prefixWord, tailWord_7140612, baseEnd_7140612] using wordTrace_append hprefix tailTrace_7140612
  have hstable : (prefixWord ++ tailWord_7140612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140612).length < 2 ^ (prefixWord ++ tailWord_7140612).sum := by decide
  have hdescent : baseEnd_7140612 < baseStart_7140612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140625 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_7140625 : Nat := 118140960795 + 7140625 * 2 ^ 59
def prefixEnd_7140625 : Nat := 4983230072969 + 3 ^ 40 * 7140625 * 2
def baseEnd_7140625 : Nat := 1222190932837076668516123

theorem tailTrace_7140625 : CollatzResearch.WordTrace tailWord_7140625 prefixEnd_7140625 1222190932837076668516123 := by
  unfold tailWord_7140625
  simp only [CollatzResearch.WordTrace]
  refine ⟨260439989755742621504031329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173626659837161747669354219 260439989755742621504031329)
  ·
    refine ⟨195329992316806966128023497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260439989755742621504031329 195329992316806966128023497)
    ·
      refine ⟨146497494237605224596017623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195329992316806966128023497 146497494237605224596017623)
      ·
        refine ⟨219746241356407836894026435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146497494237605224596017623 219746241356407836894026435)
        ·
          refine ⟨329619362034611755341039653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219746241356407836894026435 329619362034611755341039653)
          ·
            refine ⟨61803630381489704126444935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329619362034611755341039653 61803630381489704126444935)
            ·
              refine ⟨92705445572234556189667403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61803630381489704126444935 92705445572234556189667403)
              ·
                refine ⟨139058168358351834284501105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92705445572234556189667403 139058168358351834284501105)
                ·
                  refine ⟨104293626268763875713375829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139058168358351834284501105 104293626268763875713375829)
                  ·
                    refine ⟨1222190932837076668516123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104293626268763875713375829 1222190932837076668516123)
                    ·
                      rfl

theorem cell23_7140625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_7140625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140625 prefixEnd_7140625 := by exact prefixLift 7140625
  have htrace : WordTrace (prefixWord ++ tailWord_7140625) baseStart_7140625 baseEnd_7140625 := by
    simpa [prefixWord, tailWord_7140625, baseEnd_7140625] using wordTrace_append hprefix tailTrace_7140625
  have hstable : (prefixWord ++ tailWord_7140625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140625).length < 2 ^ (prefixWord ++ tailWord_7140625).sum := by decide
  have hdescent : baseEnd_7140625 < baseStart_7140625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140632 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7140632 : Nat := 118140960795 + 7140632 * 2 ^ 59
def prefixEnd_7140632 : Nat := 4983230072969 + 3 ^ 40 * 7140632 * 2
def baseEnd_7140632 : Nat := 3666576392875811478160837

theorem tailTrace_7140632 : CollatzResearch.WordTrace tailWord_7140632 prefixEnd_7140632 3666576392875811478160837 := by
  unfold tailWord_7140632
  simp only [CollatzResearch.WordTrace]
  refine ⟨130220122533358630849768075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173626830044478174466357433 130220122533358630849768075)
  ·
    refine ⟨195330183800037946274652113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130220122533358630849768075 195330183800037946274652113)
    ·
      refine ⟨146497637850028459705989085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195330183800037946274652113 146497637850028459705989085)
      ·
        refine ⟨54936614193760672389745907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146497637850028459705989085 54936614193760672389745907)
        ·
          refine ⟨82404921290641008584618861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54936614193760672389745907 82404921290641008584618861)
          ·
            refine ⟨30901845483990378219232073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82404921290641008584618861 30901845483990378219232073)
            ·
              refine ⟨23176384112992783664424055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30901845483990378219232073 23176384112992783664424055)
              ·
                refine ⟨34764576169489175496636083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23176384112992783664424055 34764576169489175496636083)
                ·
                  refine ⟨52146864254233763244954125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34764576169489175496636083 52146864254233763244954125)
                  ·
                    refine ⟨19555074095337661216857797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52146864254233763244954125 19555074095337661216857797)
                    ·
                      refine ⟨3666576392875811478160837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19555074095337661216857797 3666576392875811478160837)
                      ·
                        rfl

theorem cell23_7140632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7140632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140632 prefixEnd_7140632 := by exact prefixLift 7140632
  have htrace : WordTrace (prefixWord ++ tailWord_7140632) baseStart_7140632 baseEnd_7140632 := by
    simpa [prefixWord, tailWord_7140632, baseEnd_7140632] using wordTrace_append hprefix tailTrace_7140632
  have hstable : (prefixWord ++ tailWord_7140632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140632).length < 2 ^ (prefixWord ++ tailWord_7140632).sum := by decide
  have hdescent : baseEnd_7140632 < baseStart_7140632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140635 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_7140635 : Nat := 118140960795 + 7140635 * 2 ^ 59
def prefixEnd_7140635 : Nat := 4983230072969 + 3 ^ 40 * 7140635 * 2
def baseEnd_7140635 : Nat := 3666577933317774966423323

theorem tailTrace_7140635 : CollatzResearch.WordTrace tailWord_7140635 prefixEnd_7140635 3666577933317774966423323 := by
  unfold tailWord_7140635
  simp only [CollatzResearch.WordTrace]
  refine ⟨260440354485706393211895359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173626902990470928807930239 260440354485706393211895359)
  ·
    refine ⟨390660531728559589817843039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260440354485706393211895359 390660531728559589817843039)
    ·
      refine ⟨585990797592839384726764559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390660531728559589817843039 585990797592839384726764559)
      ·
        refine ⟨878986196389259077090146839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585990797592839384726764559 878986196389259077090146839)
        ·
          refine ⟨1318479294583888615635220259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878986196389259077090146839 1318479294583888615635220259)
          ·
            refine ⟨1977718941875832923452830389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318479294583888615635220259 1977718941875832923452830389)
            ·
              refine ⟨185411150800859336573702849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1977718941875832923452830389 185411150800859336573702849)
              ·
                refine ⟨139058363100644502430277137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185411150800859336573702849 139058363100644502430277137)
                ·
                  refine ⟨104293772325483376822707853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139058363100644502430277137 104293772325483376822707853)
                  ·
                    refine ⟨39110164622056266308515445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104293772325483376822707853 39110164622056266308515445)
                    ·
                      refine ⟨3666577933317774966423323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39110164622056266308515445 3666577933317774966423323)
                      ·
                        rfl

theorem cell23_7140635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_7140635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140635 prefixEnd_7140635 := by exact prefixLift 7140635
  have htrace : WordTrace (prefixWord ++ tailWord_7140635) baseStart_7140635 baseEnd_7140635 := by
    simpa [prefixWord, tailWord_7140635, baseEnd_7140635] using wordTrace_append hprefix tailTrace_7140635
  have hstable : (prefixWord ++ tailWord_7140635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140635).length < 2 ^ (prefixWord ++ tailWord_7140635).sum := by decide
  have hdescent : baseEnd_7140635 < baseStart_7140635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140659 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 3, 4]
def baseStart_7140659 : Nat := 118140960795 + 7140659 * 2 ^ 59
def prefixEnd_7140659 : Nat := 4983230072969 + 3 ^ 40 * 7140659 * 2
def baseEnd_7140659 : Nat := 1222196752284494290841071

theorem tailTrace_7140659 : CollatzResearch.WordTrace tailWord_7140659 prefixEnd_7140659 1222196752284494290841071 := by
  unfold tailWord_7140659
  simp only [CollatzResearch.WordTrace]
  refine ⟨260441229837619445310769031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173627486558412963540512687 260441229837619445310769031)
  ·
    refine ⟨390661844756429167966153547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260441229837619445310769031 390661844756429167966153547)
    ·
      refine ⟨585992767134643751949230321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390661844756429167966153547 585992767134643751949230321)
      ·
        refine ⟨439494575350982813961922741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585992767134643751949230321 439494575350982813961922741)
        ·
          refine ⟨41202616439154638808930257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 439494575350982813961922741 41202616439154638808930257)
          ·
            refine ⟨30901962329365979106697693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41202616439154638808930257 30901962329365979106697693)
            ·
              refine ⟨11588235873512242165011635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30901962329365979106697693 11588235873512242165011635)
              ·
                refine ⟨17382353810268363247517453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11588235873512242165011635 17382353810268363247517453)
                ·
                  refine ⟨6518382678850636217819045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17382353810268363247517453 6518382678850636217819045)
                  ·
                    refine ⟨1222196752284494290841071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6518382678850636217819045 1222196752284494290841071)
                    ·
                      rfl

theorem cell23_7140659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 4].length) (baseStart_7140659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140659 prefixEnd_7140659 := by exact prefixLift 7140659
  have htrace : WordTrace (prefixWord ++ tailWord_7140659) baseStart_7140659 baseEnd_7140659 := by
    simpa [prefixWord, tailWord_7140659, baseEnd_7140659] using wordTrace_append hprefix tailTrace_7140659
  have hstable : (prefixWord ++ tailWord_7140659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140659).length < 2 ^ (prefixWord ++ tailWord_7140659).sum := by decide
  have hdescent : baseEnd_7140659 < baseStart_7140659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140672 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 6]
def baseStart_7140672 : Nat := 118140960795 + 7140672 * 2 ^ 59
def prefixEnd_7140672 : Nat := 4983230072969 + 3 ^ 40 * 7140672 * 2
def baseEnd_7140672 : Nat := 407399659122443480184517

theorem tailTrace_7140672 : CollatzResearch.WordTrace tailWord_7140672 prefixEnd_7140672 407399659122443480184517 := by
  unfold tailWord_7140672
  simp only [CollatzResearch.WordTrace]
  refine ⟨130220851993286174265496135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173627802657714899020661513 130220851993286174265496135)
  ·
    refine ⟨195331277989929261398244203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130220851993286174265496135 195331277989929261398244203)
    ·
      refine ⟨292996916984893892097366305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195331277989929261398244203 292996916984893892097366305)
      ·
        refine ⟨219747687738670419073024729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292996916984893892097366305 219747687738670419073024729)
        ·
          refine ⟨164810765804002814304768547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219747687738670419073024729 164810765804002814304768547)
          ·
            refine ⟨247216148706004221457152821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164810765804002814304768547 247216148706004221457152821)
            ·
              refine ⟨23176513941187895761608077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247216148706004221457152821 23176513941187895761608077)
              ·
                refine ⟨8691192727945460910603029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23176513941187895761608077 8691192727945460910603029)
                ·
                  refine ⟨407399659122443480184517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8691192727945460910603029 407399659122443480184517)
                  ·
                    rfl

theorem cell23_7140672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_7140672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140672 prefixEnd_7140672 := by exact prefixLift 7140672
  have htrace : WordTrace (prefixWord ++ tailWord_7140672) baseStart_7140672 baseEnd_7140672 := by
    simpa [prefixWord, tailWord_7140672, baseEnd_7140672] using wordTrace_append hprefix tailTrace_7140672
  have hstable : (prefixWord ++ tailWord_7140672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140672).length < 2 ^ (prefixWord ++ tailWord_7140672).sum := by decide
  have hdescent : baseEnd_7140672 < baseStart_7140672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140682 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_7140682 : Nat := 118140960795 + 7140682 * 2 ^ 59
def prefixEnd_7140682 : Nat := 4983230072969 + 3 ^ 40 * 7140682 * 2
def baseEnd_7140682 : Nat := 3666602066908536282535607

theorem tailTrace_7140682 : CollatzResearch.WordTrace tailWord_7140682 prefixEnd_7140682 3666602066908536282535607 := by
  unfold tailWord_7140682
  simp only [CollatzResearch.WordTrace]
  refine ⟨65110517179134030059714075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173628045811024080159237533 65110517179134030059714075)
  ·
    refine ⟨97665775768701045089571113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65110517179134030059714075 97665775768701045089571113)
    ·
      refine ⟨73249331826525783817178335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97665775768701045089571113 73249331826525783817178335)
      ·
        refine ⟨109873997739788675725767503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73249331826525783817178335 109873997739788675725767503)
        ·
          refine ⟨164810996609683013588651255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109873997739788675725767503 164810996609683013588651255)
          ·
            refine ⟨247216494914524520382976883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164810996609683013588651255 247216494914524520382976883)
            ·
              refine ⟨370824742371786780574465325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247216494914524520382976883 370824742371786780574465325)
              ·
                refine ⟨139059278389420042715424497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370824742371786780574465325 139059278389420042715424497)
                ·
                  refine ⟨104294458792065032036568373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139059278389420042715424497 104294458792065032036568373)
                  ·
                    refine ⟨9777605511756096753428285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104294458792065032036568373 9777605511756096753428285)
                    ·
                      refine ⟨3666602066908536282535607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777605511756096753428285 3666602066908536282535607)
                      ·
                        rfl

theorem cell23_7140682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_7140682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140682 prefixEnd_7140682 := by exact prefixLift 7140682
  have htrace : WordTrace (prefixWord ++ tailWord_7140682) baseStart_7140682 baseEnd_7140682 := by
    simpa [prefixWord, tailWord_7140682, baseEnd_7140682] using wordTrace_append hprefix tailTrace_7140682
  have hstable : (prefixWord ++ tailWord_7140682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140682).length < 2 ^ (prefixWord ++ tailWord_7140682).sum := by decide
  have hdescent : baseEnd_7140682 < baseStart_7140682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140739 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 4]
def baseStart_7140739 : Nat := 118140960795 + 7140739 * 2 ^ 59
def prefixEnd_7140739 : Nat := 4983230072969 + 3 ^ 40 * 7140739 * 2
def baseEnd_7140739 : Nat := 3666631335305842559522845

theorem tailTrace_7140739 : CollatzResearch.WordTrace tailWord_7140739 prefixEnd_7140739 3666631335305842559522845 := by
  unfold tailWord_7140739
  simp only [CollatzResearch.WordTrace]
  refine ⟨260444147677329618973681271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173629431784886412649120847 260444147677329618973681271)
  ·
    refine ⟨390666221515994428460521907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260444147677329618973681271 390666221515994428460521907)
    ·
      refine ⟨585999332273991642690782861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390666221515994428460521907 585999332273991642690782861)
      ·
        refine ⟨219749749602746866009043573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585999332273991642690782861 219749749602746866009043573)
        ·
          refine ⟨20601539025257518688347835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219749749602746866009043573 20601539025257518688347835)
          ·
            refine ⟨30902308537886278032521753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20601539025257518688347835 30902308537886278032521753)
            ·
              refine ⟨23176731403414708524391315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30902308537886278032521753 23176731403414708524391315)
              ·
                refine ⟨34765097105122062786586973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23176731403414708524391315 34765097105122062786586973)
                ·
                  refine ⟨13036911414420773544970115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34765097105122062786586973 13036911414420773544970115)
                  ·
                    refine ⟨19555367121631160317455173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13036911414420773544970115 19555367121631160317455173)
                    ·
                      refine ⟨3666631335305842559522845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19555367121631160317455173 3666631335305842559522845)
                      ·
                        rfl

theorem cell23_7140739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_7140739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140739 prefixEnd_7140739 := by exact prefixLift 7140739
  have htrace : WordTrace (prefixWord ++ tailWord_7140739) baseStart_7140739 baseEnd_7140739 := by
    simpa [prefixWord, tailWord_7140739, baseEnd_7140739] using wordTrace_append hprefix tailTrace_7140739
  have hstable : (prefixWord ++ tailWord_7140739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140739).length < 2 ^ (prefixWord ++ tailWord_7140739).sum := by decide
  have hdescent : baseEnd_7140739 < baseStart_7140739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140743 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_7140743 : Nat := 118140960795 + 7140743 * 2 ^ 59
def prefixEnd_7140743 : Nat := 4983230072969 + 3 ^ 40 * 7140743 * 2
def baseEnd_7140743 : Nat := 3666633389228460543872827

theorem tailTrace_7140743 : CollatzResearch.WordTrace tailWord_7140743 prefixEnd_7140743 3666633389228460543872827 := by
  unfold tailWord_7140743
  simp only [CollatzResearch.WordTrace]
  refine ⟨260444293569315127656826883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173629529046210085104551255 260444293569315127656826883)
  ·
    refine ⟨390666440353972691485240325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260444293569315127656826883 390666440353972691485240325)
    ·
      refine ⟨73249957566369879653482561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390666440353972691485240325 73249957566369879653482561)
      ·
        refine ⟨54937468174777409740111921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73249957566369879653482561 54937468174777409740111921)
        ·
          refine ⟨41203101131083057305083941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54937468174777409740111921 41203101131083057305083941)
          ·
            refine ⟨7725581462078073244703239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41203101131083057305083941 7725581462078073244703239)
            ·
              refine ⟨11588372193117109867054859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725581462078073244703239 11588372193117109867054859)
              ·
                refine ⟨17382558289675664800582289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11588372193117109867054859 17382558289675664800582289)
                ·
                  refine ⟨13036918717256748600436717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17382558289675664800582289 13036918717256748600436717)
                  ·
                    refine ⟨4888844518971280725163769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13036918717256748600436717 4888844518971280725163769)
                    ·
                      refine ⟨3666633389228460543872827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888844518971280725163769 3666633389228460543872827)
                      ·
                        rfl

theorem cell23_7140743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_7140743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140743 prefixEnd_7140743 := by exact prefixLift 7140743
  have htrace : WordTrace (prefixWord ++ tailWord_7140743) baseStart_7140743 baseEnd_7140743 := by
    simpa [prefixWord, tailWord_7140743, baseEnd_7140743] using wordTrace_append hprefix tailTrace_7140743
  have hstable : (prefixWord ++ tailWord_7140743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140743).length < 2 ^ (prefixWord ++ tailWord_7140743).sum := by decide
  have hdescent : baseEnd_7140743 < baseStart_7140743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140762 : List Nat := [3, 1, 1, 4, 1, 1, 12]
def baseStart_7140762 : Nat := 118140960795 + 7140762 * 2 ^ 59
def prefixEnd_7140762 : Nat := 4983230072969 + 3 ^ 40 * 7140762 * 2
def baseEnd_7140762 : Nat := 45267199325443160117719

theorem tailTrace_7140762 : CollatzResearch.WordTrace tailWord_7140762 prefixEnd_7140762 45267199325443160117719 := by
  unfold tailWord_7140762
  simp only [CollatzResearch.WordTrace]
  refine ⟨65111246639061573475442135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173629991037497529267845693 65111246639061573475442135)
  ·
    refine ⟨97666869958592360213163203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65111246639061573475442135 97666869958592360213163203)
    ·
      refine ⟨146500304937888540319744805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97666869958592360213163203 146500304937888540319744805)
      ·
        refine ⟨27468807175854101309952151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146500304937888540319744805 27468807175854101309952151)
        ·
          refine ⟨41203210763781151964928227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27468807175854101309952151 41203210763781151964928227)
          ·
            refine ⟨61804816145671727947392341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41203210763781151964928227 61804816145671727947392341)
            ·
              refine ⟨45267199325443160117719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 61804816145671727947392341 45267199325443160117719)
              ·
                rfl

theorem cell23_7140762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 12].length) (baseStart_7140762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140762 prefixEnd_7140762 := by exact prefixLift 7140762
  have htrace : WordTrace (prefixWord ++ tailWord_7140762) baseStart_7140762 baseEnd_7140762 := by
    simpa [prefixWord, tailWord_7140762, baseEnd_7140762] using wordTrace_append hprefix tailTrace_7140762
  have hstable : (prefixWord ++ tailWord_7140762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140762).length < 2 ^ (prefixWord ++ tailWord_7140762).sum := by decide
  have hdescent : baseEnd_7140762 < baseStart_7140762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140772 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_7140772 : Nat := 118140960795 + 7140772 * 2 ^ 59
def prefixEnd_7140772 : Nat := 4983230072969 + 3 ^ 40 * 7140772 * 2
def baseEnd_7140772 : Nat := 3666648280167440930410193

theorem tailTrace_7140772 : CollatzResearch.WordTrace tailWord_7140772 prefixEnd_7140772 3666648280167440930410193 := by
  unfold tailWord_7140772
  simp only [CollatzResearch.WordTrace]
  refine ⟨130222675643105032804816285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173630234190806710406421713 130222675643105032804816285)
  ·
    refine ⟨48833503366164387301806107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130222675643105032804816285 48833503366164387301806107)
    ·
      refine ⟨73250255049246580952709161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48833503366164387301806107 73250255049246580952709161)
      ·
        refine ⟨54937691286934935714531871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73250255049246580952709161 54937691286934935714531871)
        ·
          refine ⟨82406536930402403571797807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54937691286934935714531871 82406536930402403571797807)
          ·
            refine ⟨123609805395603605357696711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82406536930402403571797807 123609805395603605357696711)
            ·
              refine ⟨185414708093405408036545067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123609805395603605357696711 185414708093405408036545067)
              ·
                refine ⟨278122062140108112054817601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185414708093405408036545067 278122062140108112054817601)
                ·
                  refine ⟨208591546605081084041113201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278122062140108112054817601 208591546605081084041113201)
                  ·
                    refine ⟨156443659953810813030834901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208591546605081084041113201 156443659953810813030834901)
                    ·
                      refine ⟨3666648280167440930410193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156443659953810813030834901 3666648280167440930410193)
                      ·
                        rfl

theorem cell23_7140772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_7140772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140772 prefixEnd_7140772 := by exact prefixLift 7140772
  have htrace : WordTrace (prefixWord ++ tailWord_7140772) baseStart_7140772 baseEnd_7140772 := by
    simpa [prefixWord, tailWord_7140772, baseEnd_7140772] using wordTrace_append hprefix tailTrace_7140772
  have hstable : (prefixWord ++ tailWord_7140772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140772).length < 2 ^ (prefixWord ++ tailWord_7140772).sum := by decide
  have hdescent : baseEnd_7140772 < baseStart_7140772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140792 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_7140792 : Nat := 118140960795 + 7140792 * 2 ^ 59
def prefixEnd_7140792 : Nat := 4983230072969 + 3 ^ 40 * 7140792 * 2
def baseEnd_7140792 : Nat := 1222219516593510284053367

theorem tailTrace_7140792 : CollatzResearch.WordTrace tailWord_7140792 prefixEnd_7140792 1222219516593510284053367 := by
  unfold tailWord_7140792
  simp only [CollatzResearch.WordTrace]
  refine ⟨130223040373068804512680315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173630720497425072683573753 130223040373068804512680315)
  ·
    refine ⟨195334560559603206769020473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130223040373068804512680315 195334560559603206769020473)
    ·
      refine ⟨146500920419702405076765355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195334560559603206769020473 146500920419702405076765355)
      ·
        refine ⟨219751380629553607615148033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146500920419702405076765355 219751380629553607615148033)
        ·
          refine ⟨164813535472165205711361025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219751380629553607615148033 164813535472165205711361025)
          ·
            refine ⟨123610151604123904283520769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164813535472165205711361025 123610151604123904283520769)
            ·
              refine ⟨92707613703092928212640577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123610151604123904283520769 92707613703092928212640577)
              ·
                refine ⟨69530710277319696159480433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92707613703092928212640577 69530710277319696159480433)
                ·
                  refine ⟨52148032707989772119610325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69530710277319696159480433 52148032707989772119610325)
                  ·
                    refine ⟨1222219516593510284053367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52148032707989772119610325 1222219516593510284053367)
                    ·
                      rfl

theorem cell23_7140792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_7140792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140792 prefixEnd_7140792 := by exact prefixLift 7140792
  have htrace : WordTrace (prefixWord ++ tailWord_7140792) baseStart_7140792 baseEnd_7140792 := by
    simpa [prefixWord, tailWord_7140792, baseEnd_7140792] using wordTrace_append hprefix tailTrace_7140792
  have hstable : (prefixWord ++ tailWord_7140792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140792).length < 2 ^ (prefixWord ++ tailWord_7140792).sum := by decide
  have hdescent : baseEnd_7140792 < baseStart_7140792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140793 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 3]
def baseStart_7140793 : Nat := 118140960795 + 7140793 * 2 ^ 59
def prefixEnd_7140793 : Nat := 4983230072969 + 3 ^ 40 * 7140793 * 2
def baseEnd_7140793 : Nat := 3666659063261185348247597

theorem tailTrace_7140793 : CollatzResearch.WordTrace tailWord_7140793 prefixEnd_7140793 3666659063261185348247597 := by
  unfold tailWord_7140793
  simp only [CollatzResearch.WordTrace]
  refine ⟨260446117219133986196147033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173630744812755990797431355 260446117219133986196147033)
  ·
    refine ⟨195334587914350489647110275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260446117219133986196147033 195334587914350489647110275)
    ·
      refine ⟨293001881871525734470665413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195334587914350489647110275 293001881871525734470665413)
      ·
        refine ⟨54937852850911075213249765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293001881871525734470665413 54937852850911075213249765)
        ·
          refine ⟨10300847409545826602484331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54937852850911075213249765 10300847409545826602484331)
          ·
            refine ⟨15451271114318739903726497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10300847409545826602484331 15451271114318739903726497)
            ·
              refine ⟨11588453335739054927794873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15451271114318739903726497 11588453335739054927794873)
              ·
                refine ⟨8691340001804291195846155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11588453335739054927794873 8691340001804291195846155)
                ·
                  refine ⟨13037010002706436793769233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8691340001804291195846155 13037010002706436793769233)
                  ·
                    refine ⟨9777757502029827595326925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13037010002706436793769233 9777757502029827595326925)
                    ·
                      refine ⟨3666659063261185348247597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777757502029827595326925 3666659063261185348247597)
                      ·
                        rfl

theorem cell23_7140793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_7140793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140793 prefixEnd_7140793 := by exact prefixLift 7140793
  have htrace : WordTrace (prefixWord ++ tailWord_7140793) baseStart_7140793 baseEnd_7140793 := by
    simpa [prefixWord, tailWord_7140793, baseEnd_7140793] using wordTrace_append hprefix tailTrace_7140793
  have hstable : (prefixWord ++ tailWord_7140793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140793).length < 2 ^ (prefixWord ++ tailWord_7140793).sum := by decide
  have hdescent : baseEnd_7140793 < baseStart_7140793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140799 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 7, 2]
def baseStart_7140799 : Nat := 118140960795 + 7140799 * 2 ^ 59
def prefixEnd_7140799 : Nat := 4983230072969 + 3 ^ 40 * 7140799 * 2
def baseEnd_7140799 : Nat := 3666662144145112324772569

theorem tailTrace_7140799 : CollatzResearch.WordTrace tailWord_7140799 prefixEnd_7140799 3666662144145112324772569 := by
  unfold tailWord_7140799
  simp only [CollatzResearch.WordTrace]
  refine ⟨260446336057112249220865451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173630890704741499480576967 260446336057112249220865451)
  ·
    refine ⟨390669504085668373831298177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260446336057112249220865451 390669504085668373831298177)
    ·
      refine ⟨293002128064251280373473633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390669504085668373831298177 293002128064251280373473633)
      ·
        refine ⟨219751596048188460280105225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293002128064251280373473633 219751596048188460280105225)
        ·
          refine ⟨164813697036141345210078919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219751596048188460280105225 164813697036141345210078919)
          ·
            refine ⟨247220545554212017815118379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164813697036141345210078919 247220545554212017815118379)
            ·
              refine ⟨370830818331318026722677569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247220545554212017815118379 370830818331318026722677569)
              ·
                refine ⟨278123113748488520042008177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370830818331318026722677569 278123113748488520042008177)
                ·
                  refine ⟨208592335311366390031506133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278123113748488520042008177 208592335311366390031506133)
                  ·
                    refine ⟨4888882858860149766363425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208592335311366390031506133 4888882858860149766363425)
                    ·
                      refine ⟨3666662144145112324772569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888882858860149766363425 3666662144145112324772569)
                      ·
                        rfl

theorem cell23_7140799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_7140799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140799 prefixEnd_7140799 := by exact prefixLift 7140799
  have htrace : WordTrace (prefixWord ++ tailWord_7140799) baseStart_7140799 baseEnd_7140799 := by
    simpa [prefixWord, tailWord_7140799, baseEnd_7140799] using wordTrace_append hprefix tailTrace_7140799
  have hstable : (prefixWord ++ tailWord_7140799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140799).length < 2 ^ (prefixWord ++ tailWord_7140799).sum := by decide
  have hdescent : baseEnd_7140799 < baseStart_7140799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140849 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_7140849 : Nat := 118140960795 + 7140849 * 2 ^ 59
def prefixEnd_7140849 : Nat := 4983230072969 + 3 ^ 40 * 7140849 * 2
def baseEnd_7140849 : Nat := 3666687818177837129147339

theorem tailTrace_7140849 : CollatzResearch.WordTrace tailWord_7140849 prefixEnd_7140849 3666687818177837129147339 := by
  unfold tailWord_7140849
  simp only [CollatzResearch.WordTrace]
  refine ⟨260448159706931107760185601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173632106471287405173457067 260448159706931107760185601)
  ·
    refine ⟨195336119780198330820139201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260448159706931107760185601 195336119780198330820139201)
    ·
      refine ⟨146502089835148748115104401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195336119780198330820139201 146502089835148748115104401)
      ·
        refine ⟨109876567376361561086328301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146502089835148748115104401 109876567376361561086328301)
        ·
          refine ⟨41203712766135585407373113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109876567376361561086328301 41203712766135585407373113)
          ·
            refine ⟨30902784574601689055529835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41203712766135585407373113 30902784574601689055529835)
            ·
              refine ⟨46354176861902533583294753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30902784574601689055529835 46354176861902533583294753)
              ·
                refine ⟨34765632646426900187471065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46354176861902533583294753 34765632646426900187471065)
                ·
                  refine ⟨26074224484820175140603299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34765632646426900187471065 26074224484820175140603299)
                  ·
                    refine ⟨39111336727230262710904949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26074224484820175140603299 39111336727230262710904949)
                    ·
                      refine ⟨3666687818177837129147339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39111336727230262710904949 3666687818177837129147339)
                      ·
                        rfl

theorem cell23_7140849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_7140849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140849 prefixEnd_7140849 := by exact prefixLift 7140849
  have htrace : WordTrace (prefixWord ++ tailWord_7140849) baseStart_7140849 baseEnd_7140849 := by
    simpa [prefixWord, tailWord_7140849, baseEnd_7140849] using wordTrace_append hprefix tailTrace_7140849
  have hstable : (prefixWord ++ tailWord_7140849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140849).length < 2 ^ (prefixWord ++ tailWord_7140849).sum := by decide
  have hdescent : baseEnd_7140849 < baseStart_7140849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140850 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7140850 : Nat := 118140960795 + 7140850 * 2 ^ 59
def prefixEnd_7140850 : Nat := 4983230072969 + 3 ^ 40 * 7140850 * 2
def baseEnd_7140850 : Nat := 3666688331658491625234835

theorem tailTrace_7140850 : CollatzResearch.WordTrace tailWord_7140850 prefixEnd_7140850 3666688331658491625234835 := by
  unfold tailWord_7140850
  simp only [CollatzResearch.WordTrace]
  refine ⟨65112049044981871232743001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173632130786618323287314669 65112049044981871232743001)
  ·
    refine ⟨48834036783736403424557251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65112049044981871232743001 48834036783736403424557251)
    ·
      refine ⟨73251055175604605136835877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48834036783736403424557251 73251055175604605136835877)
      ·
        refine ⟨13734572845425863463156727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73251055175604605136835877 13734572845425863463156727)
        ·
          refine ⟨20601859268138795194735091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13734572845425863463156727 20601859268138795194735091)
          ·
            refine ⟨30902788902208192792102637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20601859268138795194735091 30902788902208192792102637)
            ·
              refine ⟨11588545838328072297038489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30902788902208192792102637 11588545838328072297038489)
              ·
                refine ⟨8691409378746054222778867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11588545838328072297038489 8691409378746054222778867)
                ·
                  refine ⟨13037114068119081334168301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8691409378746054222778867 13037114068119081334168301)
                  ·
                    refine ⟨4888917775544655500313113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13037114068119081334168301 4888917775544655500313113)
                    ·
                      refine ⟨3666688331658491625234835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4888917775544655500313113 3666688331658491625234835)
                      ·
                        rfl

theorem cell23_7140850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7140850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140850 prefixEnd_7140850 := by exact prefixLift 7140850
  have htrace : WordTrace (prefixWord ++ tailWord_7140850) baseStart_7140850 baseEnd_7140850 := by
    simpa [prefixWord, tailWord_7140850, baseEnd_7140850] using wordTrace_append hprefix tailTrace_7140850
  have hstable : (prefixWord ++ tailWord_7140850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140850).length < 2 ^ (prefixWord ++ tailWord_7140850).sum := by decide
  have hdescent : baseEnd_7140850 < baseStart_7140850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140896 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7140896 : Nat := 118140960795 + 7140896 * 2 ^ 59
def prefixEnd_7140896 : Nat := 4983230072969 + 3 ^ 40 * 7140896 * 2
def baseEnd_7140896 : Nat := 3666711951768598445259623

theorem tailTrace_7140896 : CollatzResearch.WordTrace tailWord_7140896 prefixEnd_7140896 3666711951768598445259623 := by
  unfold tailWord_7140896
  simp only [CollatzResearch.WordTrace]
  refine ⟨130224936968880417393573271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173633249291840556524764361 130224936968880417393573271)
  ·
    refine ⟨195337405453320626090359907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130224936968880417393573271 195337405453320626090359907)
    ·
      refine ⟨293006108179980939135539861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195337405453320626090359907 293006108179980939135539861)
      ·
        refine ⟨13734661320936606521978431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 293006108179980939135539861 13734661320936606521978431)
        ·
          refine ⟨20601991981404909782967647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13734661320936606521978431 20601991981404909782967647)
          ·
            refine ⟨30902987972107364674451471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20601991981404909782967647 30902987972107364674451471)
            ·
              refine ⟨46354481958161047011677207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30902987972107364674451471 46354481958161047011677207)
              ·
                refine ⟨69531722937241570517515811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46354481958161047011677207 69531722937241570517515811)
                ·
                  refine ⟨104297584405862355776273717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69531722937241570517515811 104297584405862355776273717)
                  ·
                    refine ⟨9777898538049595854025661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104297584405862355776273717 9777898538049595854025661)
                    ·
                      refine ⟨3666711951768598445259623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9777898538049595854025661 3666711951768598445259623)
                      ·
                        rfl

theorem cell23_7140896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7140896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140896 prefixEnd_7140896 := by exact prefixLift 7140896
  have htrace : WordTrace (prefixWord ++ tailWord_7140896) baseStart_7140896 baseEnd_7140896 := by
    simpa [prefixWord, tailWord_7140896, baseEnd_7140896] using wordTrace_append hprefix tailTrace_7140896
  have hstable : (prefixWord ++ tailWord_7140896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140896).length < 2 ^ (prefixWord ++ tailWord_7140896).sum := by decide
  have hdescent : baseEnd_7140896 < baseStart_7140896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7140949 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7140949 : Nat := 118140960795 + 7140949 * 2 ^ 59
def prefixEnd_7140949 : Nat := 4983230072969 + 3 ^ 40 * 7140949 * 2
def baseEnd_7140949 : Nat := 3666739166243286737896879

theorem tailTrace_7140949 : CollatzResearch.WordTrace tailWord_7140949 prefixEnd_7140949 3666739166243286737896879 := by
  unfold tailWord_7140949
  simp only [CollatzResearch.WordTrace]
  refine ⟨260451807006568824838825901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173634538004379216559217267 260451807006568824838825901)
  ·
    refine ⟨97669427627463309314559713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260451807006568824838825901 97669427627463309314559713)
    ·
      refine ⟨73252070720597481985919785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97669427627463309314559713 73252070720597481985919785)
      ·
        refine ⟨54939053040448111489439839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73252070720597481985919785 54939053040448111489439839)
        ·
          refine ⟨82408579560672167234159759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54939053040448111489439839 82408579560672167234159759)
          ·
            refine ⟨123612869341008250851239639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82408579560672167234159759 123612869341008250851239639)
            ·
              refine ⟨185419304011512376276859459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123612869341008250851239639 185419304011512376276859459)
              ·
                refine ⟨278128956017268564415289189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185419304011512376276859459 278128956017268564415289189)
                ·
                  refine ⟨52149179253237855827866723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278128956017268564415289189 52149179253237855827866723)
                  ·
                    refine ⟨78223768879856783741800085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52149179253237855827866723 78223768879856783741800085)
                    ·
                      refine ⟨3666739166243286737896879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78223768879856783741800085 3666739166243286737896879)
                      ·
                        rfl

theorem cell23_7140949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7140949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7140949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7140949 prefixEnd_7140949 := by exact prefixLift 7140949
  have htrace : WordTrace (prefixWord ++ tailWord_7140949) baseStart_7140949 baseEnd_7140949 := by
    simpa [prefixWord, tailWord_7140949, baseEnd_7140949] using wordTrace_append hprefix tailTrace_7140949
  have hstable : (prefixWord ++ tailWord_7140949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7140949).length < 2 ^ (prefixWord ++ tailWord_7140949).sum := by decide
  have hdescent : baseEnd_7140949 < baseStart_7140949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7140949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141037 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7141037 : Nat := 118140960795 + 7141037 * 2 ^ 59
def prefixEnd_7141037 : Nat := 4983230072969 + 3 ^ 40 * 7141037 * 2
def baseEnd_7141037 : Nat := 3666784352540882393596475

theorem tailTrace_7141037 : CollatzResearch.WordTrace tailWord_7141037 prefixEnd_7141037 3666784352540882393596475 := by
  unfold tailWord_7141037
  simp only [CollatzResearch.WordTrace]
  refine ⟨260455016630250015868029365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173636677753500010578686243 260455016630250015868029365)
  ·
    refine ⟨24417657809085938987627753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260455016630250015868029365 24417657809085938987627753)
    ·
      refine ⟨18313243356814454240720815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24417657809085938987627753 18313243356814454240720815)
      ·
        refine ⟨27469865035221681361081223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18313243356814454240720815 27469865035221681361081223)
        ·
          refine ⟨41204797552832522041621835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27469865035221681361081223 41204797552832522041621835)
          ·
            refine ⟨61807196329248783062432753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41204797552832522041621835 61807196329248783062432753)
            ·
              refine ⟨46355397246936587296824565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61807196329248783062432753 46355397246936587296824565)
              ·
                refine ⟨4345818491900305059077303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46355397246936587296824565 4345818491900305059077303)
                ·
                  refine ⟨6518727737850457588615955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345818491900305059077303 6518727737850457588615955)
                  ·
                    refine ⟨9778091606775686382923933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6518727737850457588615955 9778091606775686382923933)
                    ·
                      refine ⟨3666784352540882393596475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778091606775686382923933 3666784352540882393596475)
                      ·
                        rfl

theorem cell23_7141037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7141037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141037 prefixEnd_7141037 := by exact prefixLift 7141037
  have htrace : WordTrace (prefixWord ++ tailWord_7141037) baseStart_7141037 baseEnd_7141037 := by
    simpa [prefixWord, tailWord_7141037, baseEnd_7141037] using wordTrace_append hprefix tailTrace_7141037
  have hstable : (prefixWord ++ tailWord_7141037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141037).length < 2 ^ (prefixWord ++ tailWord_7141037).sum := by decide
  have hdescent : baseEnd_7141037 < baseStart_7141037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141054 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_7141054 : Nat := 118140960795 + 7141054 * 2 ^ 59
def prefixEnd_7141054 : Nat := 4983230072969 + 3 ^ 40 * 7141054 * 2
def baseEnd_7141054 : Nat := 3666793081712008827083897

theorem tailTrace_7141054 : CollatzResearch.WordTrace tailWord_7141054 prefixEnd_7141054 3666793081712008827083897 := by
  unfold tailWord_7141054
  simp only [CollatzResearch.WordTrace]
  refine ⟨32556954583898553471424777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173637091114125618514265477 32556954583898553471424777)
  ·
    refine ⟨24417715937923915103568583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32556954583898553471424777 24417715937923915103568583)
    ·
      refine ⟨36626573906885872655352875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24417715937923915103568583 36626573906885872655352875)
      ·
        refine ⟨54939860860328808983029313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36626573906885872655352875 54939860860328808983029313)
        ·
          refine ⟨41204895645246606737271985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54939860860328808983029313 41204895645246606737271985)
          ·
            refine ⟨30903671733934955052953989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41204895645246606737271985 30903671733934955052953989)
            ·
              refine ⟨5794438450112804072428873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30903671733934955052953989 5794438450112804072428873)
              ·
                refine ⟨4345828837584603054321655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5794438450112804072428873 4345828837584603054321655)
                ·
                  refine ⟨6518743256376904581482483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345828837584603054321655 6518743256376904581482483)
                  ·
                    refine ⟨9778114884565356872223725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6518743256376904581482483 9778114884565356872223725)
                    ·
                      refine ⟨3666793081712008827083897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778114884565356872223725 3666793081712008827083897)
                      ·
                        rfl

theorem cell23_7141054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_7141054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141054 prefixEnd_7141054 := by exact prefixLift 7141054
  have htrace : WordTrace (prefixWord ++ tailWord_7141054) baseStart_7141054 baseEnd_7141054 := by
    simpa [prefixWord, tailWord_7141054, baseEnd_7141054] using wordTrace_append hprefix tailTrace_7141054
  have hstable : (prefixWord ++ tailWord_7141054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141054).length < 2 ^ (prefixWord ++ tailWord_7141054).sum := by decide
  have hdescent : baseEnd_7141054 < baseStart_7141054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141056 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_7141056 : Nat := 118140960795 + 7141056 * 2 ^ 59
def prefixEnd_7141056 : Nat := 4983230072969 + 3 ^ 40 * 7141056 * 2
def baseEnd_7141056 : Nat := 3666794108673317819258887

theorem tailTrace_7141056 : CollatzResearch.WordTrace tailWord_7141056 prefixEnd_7141056 3666794108673317819258887 := by
  unfold tailWord_7141056
  simp only [CollatzResearch.WordTrace]
  refine ⟨130227854808590591056485511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173637139744787454741980681 130227854808590591056485511)
  ·
    refine ⟨195341782212885886584728267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130227854808590591056485511 195341782212885886584728267)
    ·
      refine ⟨293012673319328829877092401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195341782212885886584728267 293012673319328829877092401)
      ·
        refine ⟨219759504989496622407819301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293012673319328829877092401 219759504989496622407819301)
        ·
          refine ⟨41204907185530616701466119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219759504989496622407819301 41204907185530616701466119)
          ·
            refine ⟨61807360778295925052199179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41204907185530616701466119 61807360778295925052199179)
            ·
              refine ⟨92711041167443887578298769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61807360778295925052199179 92711041167443887578298769)
              ·
                refine ⟨69533280875582915683724077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92711041167443887578298769 69533280875582915683724077)
                ·
                  refine ⟨26074980328343593381396529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69533280875582915683724077 26074980328343593381396529)
                  ·
                    refine ⟨19556235246257695036047397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26074980328343593381396529 19556235246257695036047397)
                    ·
                      refine ⟨3666794108673317819258887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19556235246257695036047397 3666794108673317819258887)
                      ·
                        rfl

theorem cell23_7141056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_7141056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141056 prefixEnd_7141056 := by exact prefixLift 7141056
  have htrace : WordTrace (prefixWord ++ tailWord_7141056) baseStart_7141056 baseEnd_7141056 := by
    simpa [prefixWord, tailWord_7141056, baseEnd_7141056] using wordTrace_append hprefix tailTrace_7141056
  have hstable : (prefixWord ++ tailWord_7141056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141056).length < 2 ^ (prefixWord ++ tailWord_7141056).sum := by decide
  have hdescent : baseEnd_7141056 < baseStart_7141056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141073 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_7141073 : Nat := 118140960795 + 7141073 * 2 ^ 59
def prefixEnd_7141073 : Nat := 4983230072969 + 3 ^ 40 * 7141073 * 2
def baseEnd_7141073 : Nat := 3666802837844444252746309

theorem tailTrace_7141073 : CollatzResearch.WordTrace tailWord_7141073 prefixEnd_7141073 3666802837844444252746309 := by
  unfold tailWord_7141073
  simp only [CollatzResearch.WordTrace]
  refine ⟨260456329658119594016339873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173637553105413062677559915 260456329658119594016339873)
  ·
    refine ⟨195342247243589695512254905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260456329658119594016339873 195342247243589695512254905)
    ·
      refine ⟨146506685432692271634191179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195342247243589695512254905 146506685432692271634191179)
      ·
        refine ⟨219760028149038407451286769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146506685432692271634191179 219760028149038407451286769)
        ·
          refine ⟨164820021111778805588465077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219760028149038407451286769 164820021111778805588465077)
          ·
            refine ⟨15451876979229263023918601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164820021111778805588465077 15451876979229263023918601)
            ·
              refine ⟨11588907734421947267938951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15451876979229263023918601 11588907734421947267938951)
              ·
                refine ⟨17383361601632920901908427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11588907734421947267938951 17383361601632920901908427)
                ·
                  refine ⟨26075042402449381352862641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17383361601632920901908427 26075042402449381352862641)
                  ·
                    refine ⟨19556281801837036014646981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26075042402449381352862641 19556281801837036014646981)
                    ·
                      refine ⟨3666802837844444252746309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19556281801837036014646981 3666802837844444252746309)
                      ·
                        rfl

theorem cell23_7141073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_7141073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141073 prefixEnd_7141073 := by exact prefixLift 7141073
  have htrace : WordTrace (prefixWord ++ tailWord_7141073) baseStart_7141073 baseEnd_7141073 := by
    simpa [prefixWord, tailWord_7141073, baseEnd_7141073] using wordTrace_append hprefix tailTrace_7141073
  have hstable : (prefixWord ++ tailWord_7141073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141073).length < 2 ^ (prefixWord ++ tailWord_7141073).sum := by decide
  have hdescent : baseEnd_7141073 < baseStart_7141073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141093 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_7141093 : Nat := 118140960795 + 7141093 * 2 ^ 59
def prefixEnd_7141093 : Nat := 4983230072969 + 3 ^ 40 * 7141093 * 2
def baseEnd_7141093 : Nat := 3666813107457534174496217

theorem tailTrace_7141093 : CollatzResearch.WordTrace tailWord_7141093 prefixEnd_7141093 3666813107457534174496217 := by
  unfold tailWord_7141093
  simp only [CollatzResearch.WordTrace]
  refine ⟨260457059118047137432067933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173638039412031424954711955 260457059118047137432067933)
  ·
    refine ⟨97671397169267676537025475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260457059118047137432067933 97671397169267676537025475)
    ·
      refine ⟨146507095753901514805538213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97671397169267676537025475 146507095753901514805538213)
      ·
        refine ⟨27470080453856534026038415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146507095753901514805538213 27470080453856534026038415)
        ·
          refine ⟨41205120680784801039057623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27470080453856534026038415 41205120680784801039057623)
          ·
            refine ⟨61807681021177201558586435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41205120680784801039057623 61807681021177201558586435)
            ·
              refine ⟨92711521531765802337879653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61807681021177201558586435 92711521531765802337879653)
              ·
                refine ⟨17383410287206087938352435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92711521531765802337879653 17383410287206087938352435)
                ·
                  refine ⟨26075115430809131907528653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17383410287206087938352435 26075115430809131907528653)
                  ·
                    refine ⟨9778168286553424465323245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26075115430809131907528653 9778168286553424465323245)
                    ·
                      refine ⟨3666813107457534174496217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778168286553424465323245 3666813107457534174496217)
                      ·
                        rfl

theorem cell23_7141093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_7141093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141093 prefixEnd_7141093 := by exact prefixLift 7141093
  have htrace : WordTrace (prefixWord ++ tailWord_7141093) baseStart_7141093 baseEnd_7141093 := by
    simpa [prefixWord, tailWord_7141093, baseEnd_7141093] using wordTrace_append hprefix tailTrace_7141093
  have hstable : (prefixWord ++ tailWord_7141093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141093).length < 2 ^ (prefixWord ++ tailWord_7141093).sum := by decide
  have hdescent : baseEnd_7141093 < baseStart_7141093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141127 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7141127 : Nat := 118140960795 + 7141127 * 2 ^ 59
def prefixEnd_7141127 : Nat := 4983230072969 + 3 ^ 40 * 7141127 * 2
def baseEnd_7141127 : Nat := 3666830565799787041471061

theorem tailTrace_7141127 : CollatzResearch.WordTrace tailWord_7141127 prefixEnd_7141127 3666830565799787041471061 := by
  unfold tailWord_7141127
  simp only [CollatzResearch.WordTrace]
  refine ⟨260458299199923961238805635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173638866133282640825870423 260458299199923961238805635)
  ·
    refine ⟨390687448799885941858208453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260458299199923961238805635 390687448799885941858208453)
    ·
      refine ⟨73253896649978614098414085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390687448799885941858208453 73253896649978614098414085)
      ·
        refine ⟨13735105621870990143452641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73253896649978614098414085 13735105621870990143452641)
        ·
          refine ⟨10301329216403242607589481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13735105621870990143452641 10301329216403242607589481)
          ·
            refine ⟨7725996912302431955692111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10301329216403242607589481 7725996912302431955692111)
            ·
              refine ⟨11588995368453647933538167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725996912302431955692111 11588995368453647933538167)
              ·
                refine ⟨17383493052680471900307251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11588995368453647933538167 17383493052680471900307251)
                ·
                  refine ⟨26075239579020707850460877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17383493052680471900307251 26075239579020707850460877)
                  ·
                    refine ⟨9778214842132765443922829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26075239579020707850460877 9778214842132765443922829)
                    ·
                      refine ⟨3666830565799787041471061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778214842132765443922829 3666830565799787041471061)
                      ·
                        rfl

theorem cell23_7141127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7141127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141127 prefixEnd_7141127 := by exact prefixLift 7141127
  have htrace : WordTrace (prefixWord ++ tailWord_7141127) baseStart_7141127 baseEnd_7141127 := by
    simpa [prefixWord, tailWord_7141127, baseEnd_7141127] using wordTrace_append hprefix tailTrace_7141127
  have hstable : (prefixWord ++ tailWord_7141127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141127).length < 2 ^ (prefixWord ++ tailWord_7141127).sum := by decide
  have hdescent : baseEnd_7141127 < baseStart_7141127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141153 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7141153 : Nat := 118140960795 + 7141153 * 2 ^ 59
def prefixEnd_7141153 : Nat := 4983230072969 + 3 ^ 40 * 7141153 * 2
def baseEnd_7141153 : Nat := 3666843916296803939745941

theorem tailTrace_7141153 : CollatzResearch.WordTrace tailWord_7141153 prefixEnd_7141153 3666843916296803939745941 := by
  unfold tailWord_7141153
  simp only [CollatzResearch.WordTrace]
  refine ⟨260459247497829767679252113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173639498331886511786168075 260459247497829767679252113)
  ·
    refine ⟨195344435623372325759439085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260459247497829767679252113 195344435623372325759439085)
    ·
      refine ⟨73254163358764622159789657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195344435623372325759439085 73254163358764622159789657)
      ·
        refine ⟨54940622519073466619842243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73254163358764622159789657 54940622519073466619842243)
        ·
          refine ⟨82410933778610199929763365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54940622519073466619842243 82410933778610199929763365)
          ·
            refine ⟨15452050083489412486830631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82410933778610199929763365 15452050083489412486830631)
            ·
              refine ⟨23178075125234118730245947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15452050083489412486830631 23178075125234118730245947)
              ·
                refine ⟨34767112687851178095368921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23178075125234118730245947 34767112687851178095368921)
                ·
                  refine ⟨26075334515888383571526691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34767112687851178095368921 26075334515888383571526691)
                  ·
                    refine ⟨39113001773832575357290037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26075334515888383571526691 39113001773832575357290037)
                    ·
                      refine ⟨3666843916296803939745941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39113001773832575357290037 3666843916296803939745941)
                      ·
                        rfl

theorem cell23_7141153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7141153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141153 prefixEnd_7141153 := by exact prefixLift 7141153
  have htrace : WordTrace (prefixWord ++ tailWord_7141153) baseStart_7141153 baseEnd_7141153 := by
    simpa [prefixWord, tailWord_7141153, baseEnd_7141153] using wordTrace_append hprefix tailTrace_7141153
  have hstable : (prefixWord ++ tailWord_7141153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141153).length < 2 ^ (prefixWord ++ tailWord_7141153).sum := by decide
  have hdescent : baseEnd_7141153 < baseStart_7141153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141230 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7141230 : Nat := 118140960795 + 7141230 * 2 ^ 59
def prefixEnd_7141230 : Nat := 4983230072969 + 3 ^ 40 * 7141230 * 2
def baseEnd_7141230 : Nat := 3666883454307200138483087

theorem tailTrace_7141230 : CollatzResearch.WordTrace tailWord_7141230 prefixEnd_7141230 3666883454307200138483087 := by
  unfold tailWord_7141230
  simp only [CollatzResearch.WordTrace]
  refine ⟨32557756989818851228725643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173641370612367206553203429 32557756989818851228725643)
  ·
    refine ⟨48836635484728276843088465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32557756989818851228725643 48836635484728276843088465)
    ·
      refine ⟨36627476613546207632316349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48836635484728276843088465 36627476613546207632316349)
      ·
        refine ⟨13735303730079827862118631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36627476613546207632316349 13735303730079827862118631)
        ·
          refine ⟨20602955595119741793177947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13735303730079827862118631 20602955595119741793177947)
          ·
            refine ⟨30904433392679612689766921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20602955595119741793177947 30904433392679612689766921)
            ·
              refine ⟨23178325044509709517325191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30904433392679612689766921 23178325044509709517325191)
              ·
                refine ⟨34767487566764564275987787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23178325044509709517325191 34767487566764564275987787)
                ·
                  refine ⟨52151231350146846413981681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34767487566764564275987787 52151231350146846413981681)
                  ·
                    refine ⟨39113423512610134810486261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52151231350146846413981681 39113423512610134810486261)
                    ·
                      refine ⟨3666883454307200138483087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39113423512610134810486261 3666883454307200138483087)
                      ·
                        rfl

theorem cell23_7141230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7141230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141230 prefixEnd_7141230 := by exact prefixLift 7141230
  have htrace : WordTrace (prefixWord ++ tailWord_7141230) baseStart_7141230 baseEnd_7141230 := by
    simpa [prefixWord, tailWord_7141230, baseEnd_7141230] using wordTrace_append hprefix tailTrace_7141230
  have hstable : (prefixWord ++ tailWord_7141230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141230).length < 2 ^ (prefixWord ++ tailWord_7141230).sum := by decide
  have hdescent : baseEnd_7141230 < baseStart_7141230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141243 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 3]
def baseStart_7141243 : Nat := 118140960795 + 7141243 * 2 ^ 59
def prefixEnd_7141243 : Nat := 4983230072969 + 3 ^ 40 * 7141243 * 2
def baseEnd_7141243 : Nat := 3666890129555708587620527

theorem tailTrace_7141243 : CollatzResearch.WordTrace tailWord_7141243 prefixEnd_7141243 3666890129555708587620527 := by
  unfold tailWord_7141243
  simp only [CollatzResearch.WordTrace]
  refine ⟨260462530067503713050028383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173641686711669142033352255 260462530067503713050028383)
  ·
    refine ⟨390693795101255569575042575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260462530067503713050028383 390693795101255569575042575)
    ·
      refine ⟨586040692651883354362563863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390693795101255569575042575 586040692651883354362563863)
      ·
        refine ⟨879061038977825031543845795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586040692651883354362563863 879061038977825031543845795)
        ·
          refine ⟨1318591558466737547315768693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879061038977825031543845795 1318591558466737547315768693)
          ·
            refine ⟨123617958606256645060853315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1318591558466737547315768693 123617958606256645060853315)
            ·
              refine ⟨185426937909384967591279973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123617958606256645060853315 185426937909384967591279973)
              ·
                refine ⟨34767550858009681423364995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185426937909384967591279973 34767550858009681423364995)
                ·
                  refine ⟨52151326287014522135047493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34767550858009681423364995 52151326287014522135047493)
                  ·
                    refine ⟨9778373678815222900321405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52151326287014522135047493 9778373678815222900321405)
                    ·
                      refine ⟨3666890129555708587620527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778373678815222900321405 3666890129555708587620527)
                      ·
                        rfl

theorem cell23_7141243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 3].length) (baseStart_7141243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141243 prefixEnd_7141243 := by exact prefixLift 7141243
  have htrace : WordTrace (prefixWord ++ tailWord_7141243) baseStart_7141243 baseEnd_7141243 := by
    simpa [prefixWord, tailWord_7141243, baseEnd_7141243] using wordTrace_append hprefix tailTrace_7141243
  have hstable : (prefixWord ++ tailWord_7141243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141243).length < 2 ^ (prefixWord ++ tailWord_7141243).sum := by decide
  have hdescent : baseEnd_7141243 < baseStart_7141243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141297 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 6]
def baseStart_7141297 : Nat := 118140960795 + 7141297 * 2 ^ 59
def prefixEnd_7141297 : Nat := 4983230072969 + 3 ^ 40 * 7141297 * 2
def baseEnd_7141297 : Nat := 407435317501227930705031

theorem tailTrace_7141297 : CollatzResearch.WordTrace tailWord_7141297 prefixEnd_7141297 407435317501227930705031 := by
  unfold tailWord_7141297
  simp only [CollatzResearch.WordTrace]
  refine ⟨260464499609308080272494145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173642999739538720181662763 260464499609308080272494145)
  ·
    refine ⟨195348374706981060204370609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260464499609308080272494145 195348374706981060204370609)
    ·
      refine ⟨146511281030235795153277957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195348374706981060204370609 146511281030235795153277957)
      ·
        refine ⟨27470865193169211591239617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146511281030235795153277957 27470865193169211591239617)
        ·
          refine ⟨20603148894876908693429713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27470865193169211591239617 20603148894876908693429713)
          ·
            refine ⟨15452361671157681520072285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20603148894876908693429713 15452361671157681520072285)
            ·
              refine ⟨5794635626684130570027107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15452361671157681520072285 5794635626684130570027107)
              ·
                refine ⟨8691953440026195855040661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794635626684130570027107 8691953440026195855040661)
                ·
                  refine ⟨407435317501227930705031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8691953440026195855040661 407435317501227930705031)
                  ·
                    rfl

theorem cell23_7141297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 6].length) (baseStart_7141297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141297 prefixEnd_7141297 := by exact prefixLift 7141297
  have htrace : WordTrace (prefixWord ++ tailWord_7141297) baseStart_7141297 baseEnd_7141297 := by
    simpa [prefixWord, tailWord_7141297, baseEnd_7141297] using wordTrace_append hprefix tailTrace_7141297
  have hstable : (prefixWord ++ tailWord_7141297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141297).length < 2 ^ (prefixWord ++ tailWord_7141297).sum := by decide
  have hdescent : baseEnd_7141297 < baseStart_7141297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141323 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 3, 6]
def baseStart_7141323 : Nat := 118140960795 + 7141323 * 2 ^ 59
def prefixEnd_7141323 : Nat := 4983230072969 + 3 ^ 40 * 7141323 * 2
def baseEnd_7141323 : Nat := 1222310402669356091540053

theorem tailTrace_7141323 : CollatzResearch.WordTrace tailWord_7141323 prefixEnd_7141323 1222310402669356091540053 := by
  unfold tailWord_7141323
  simp only [CollatzResearch.WordTrace]
  refine ⟨260465447907213886712940623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173643631938142591141960415 260465447907213886712940623)
  ·
    refine ⟨390698171860820830069410935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260465447907213886712940623 390698171860820830069410935)
    ·
      refine ⟨586047257791231245104116403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390698171860820830069410935 586047257791231245104116403)
      ·
        refine ⟨879070886686846867656174605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586047257791231245104116403 879070886686846867656174605)
        ·
          refine ⟨329651582507567575371065477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879070886686846867656174605 329651582507567575371065477)
          ·
            refine ⟨61809671720168920382074777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329651582507567575371065477 61809671720168920382074777)
            ·
              refine ⟨46357253790126690286556083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61809671720168920382074777 46357253790126690286556083)
              ·
                refine ⟨69535880685190035429834125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46357253790126690286556083 69535880685190035429834125)
                ·
                  refine ⟨26075955256946263286187797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69535880685190035429834125 26075955256946263286187797)
                  ·
                    refine ⟨1222310402669356091540053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26075955256946263286187797 1222310402669356091540053)
                    ·
                      rfl

theorem cell23_7141323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_7141323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141323 prefixEnd_7141323 := by exact prefixLift 7141323
  have htrace : WordTrace (prefixWord ++ tailWord_7141323) baseStart_7141323 baseEnd_7141323 := by
    simpa [prefixWord, tailWord_7141323, baseEnd_7141323] using wordTrace_append hprefix tailTrace_7141323
  have hstable : (prefixWord ++ tailWord_7141323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141323).length < 2 ^ (prefixWord ++ tailWord_7141323).sum := by decide
  have hdescent : baseEnd_7141323 < baseStart_7141323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141341 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_7141341 : Nat := 118140960795 + 7141341 * 2 ^ 59
def prefixEnd_7141341 : Nat := 4983230072969 + 3 ^ 40 * 7141341 * 2
def baseEnd_7141341 : Nat := 3666940450659849204195077

theorem tailTrace_7141341 : CollatzResearch.WordTrace tailWord_7141341 prefixEnd_7141341 3666940450659849204195077 := by
  unfold tailWord_7141341
  simp only [CollatzResearch.WordTrace]
  refine ⟨260466104421148675787095877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173644069614099117191397251 260466104421148675787095877)
  ·
    refine ⟨48837394578965376710080477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260466104421148675787095877 48837394578965376710080477)
    ·
      refine ⟨18314022967112016266280179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48837394578965376710080477 18314022967112016266280179)
      ·
        refine ⟨27471034450668024399420269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314022967112016266280179 27471034450668024399420269)
        ·
          refine ⟨10301637919000509149782601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27471034450668024399420269 10301637919000509149782601)
          ·
            refine ⟨7726228439250381862336951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10301637919000509149782601 7726228439250381862336951)
            ·
              refine ⟨11589342658875572793505427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726228439250381862336951 11589342658875572793505427)
              ·
                refine ⟨17384013988313359190258141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11589342658875572793505427 17384013988313359190258141)
                ·
                  refine ⟨6519005245617509696346803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17384013988313359190258141 6519005245617509696346803)
                  ·
                    refine ⟨9778507868426264544520205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6519005245617509696346803 9778507868426264544520205)
                    ·
                      refine ⟨3666940450659849204195077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778507868426264544520205 3666940450659849204195077)
                      ·
                        rfl

theorem cell23_7141341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_7141341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141341 prefixEnd_7141341 := by exact prefixLift 7141341
  have htrace : WordTrace (prefixWord ++ tailWord_7141341) baseStart_7141341 baseEnd_7141341 := by
    simpa [prefixWord, tailWord_7141341, baseEnd_7141341] using wordTrace_append hprefix tailTrace_7141341
  have hstable : (prefixWord ++ tailWord_7141341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141341).length < 2 ^ (prefixWord ++ tailWord_7141341).sum := by decide
  have hdescent : baseEnd_7141341 < baseStart_7141341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141384 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_7141384 : Nat := 118140960795 + 7141384 * 2 ^ 59
def prefixEnd_7141384 : Nat := 4983230072969 + 3 ^ 40 * 7141384 * 2
def baseEnd_7141384 : Nat := 3666962530327992535957379

theorem tailTrace_7141384 : CollatzResearch.WordTrace tailWord_7141384 prefixEnd_7141384 3666962530327992535957379 := by
  unfold tailWord_7141384
  simp only [CollatzResearch.WordTrace]
  refine ⟨130233836379996447065455603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173645115173328596087274137 130233836379996447065455603)
  ·
    refine ⟨195350754569994670598183405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130233836379996447065455603 195350754569994670598183405)
    ·
      refine ⟨73256532963748001474318777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195350754569994670598183405 73256532963748001474318777)
      ·
        refine ⟨54942399722811001105739083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73256532963748001474318777 54942399722811001105739083)
        ·
          refine ⟨82413599584216501658608625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54942399722811001105739083 82413599584216501658608625)
          ·
            refine ⟨61810199688162376243956469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82413599584216501658608625 61810199688162376243956469)
            ·
              refine ⟨5794706220765222772870919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61810199688162376243956469 5794706220765222772870919)
              ·
                refine ⟨8692059331147834159306379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794706220765222772870919 8692059331147834159306379)
                ·
                  refine ⟨13038088996721751238959569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692059331147834159306379 13038088996721751238959569)
                  ·
                    refine ⟨9778566747541313429219677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13038088996721751238959569 9778566747541313429219677)
                    ·
                      refine ⟨3666962530327992535957379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778566747541313429219677 3666962530327992535957379)
                      ·
                        rfl

theorem cell23_7141384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_7141384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141384 prefixEnd_7141384 := by exact prefixLift 7141384
  have htrace : WordTrace (prefixWord ++ tailWord_7141384) baseStart_7141384 baseEnd_7141384 := by
    simpa [prefixWord, tailWord_7141384, baseEnd_7141384] using wordTrace_append hprefix tailTrace_7141384
  have hstable : (prefixWord ++ tailWord_7141384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141384).length < 2 ^ (prefixWord ++ tailWord_7141384).sum := by decide
  have hdescent : baseEnd_7141384 < baseStart_7141384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141393 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_7141393 : Nat := 118140960795 + 7141393 * 2 ^ 59
def prefixEnd_7141393 : Nat := 4983230072969 + 3 ^ 40 * 7141393 * 2
def baseEnd_7141393 : Nat := 3666967151653883000744837

theorem tailTrace_7141393 : CollatzResearch.WordTrace tailWord_7141393 prefixEnd_7141393 3666967151653883000744837 := by
  unfold tailWord_7141393
  simp only [CollatzResearch.WordTrace]
  refine ⟨260468001016960288667988833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173645334011306859111992555 260468001016960288667988833)
  ·
    refine ⟨195351000762720216500991625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260468001016960288667988833 195351000762720216500991625)
    ·
      refine ⟨146513250572040162375743719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195351000762720216500991625 146513250572040162375743719)
      ·
        refine ⟨219769875858060243563615579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146513250572040162375743719 219769875858060243563615579)
        ·
          refine ⟨329654813787090365345423369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219769875858060243563615579 329654813787090365345423369)
          ·
            refine ⟨247241110340317774009067527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329654813787090365345423369 247241110340317774009067527)
            ·
              refine ⟨370861665510476661013601291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247241110340317774009067527 370861665510476661013601291)
              ·
                refine ⟨556292498265714991520401937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370861665510476661013601291 556292498265714991520401937)
                ·
                  refine ⟨417219373699286243640301453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556292498265714991520401937 417219373699286243640301453)
                  ·
                    refine ⟨156457265137232341365113045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417219373699286243640301453 156457265137232341365113045)
                    ·
                      refine ⟨3666967151653883000744837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156457265137232341365113045 3666967151653883000744837)
                      ·
                        rfl

theorem cell23_7141393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_7141393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141393 prefixEnd_7141393 := by exact prefixLift 7141393
  have htrace : WordTrace (prefixWord ++ tailWord_7141393) baseStart_7141393 baseEnd_7141393 := by
    simpa [prefixWord, tailWord_7141393, baseEnd_7141393] using wordTrace_append hprefix tailTrace_7141393
  have hstable : (prefixWord ++ tailWord_7141393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141393).length < 2 ^ (prefixWord ++ tailWord_7141393).sum := by decide
  have hdescent : baseEnd_7141393 < baseStart_7141393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141407 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 5, 3, 2]
def baseStart_7141407 : Nat := 118140960795 + 7141407 * 2 ^ 59
def prefixEnd_7141407 : Nat := 4983230072969 + 3 ^ 40 * 7141407 * 2
def baseEnd_7141407 : Nat := 3666974340383045945969773

theorem tailTrace_7141407 : CollatzResearch.WordTrace tailWord_7141407 prefixEnd_7141407 3666974340383045945969773 := by
  unfold tailWord_7141407
  simp only [CollatzResearch.WordTrace]
  refine ⟨260468511638909569058998475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173645674425939712705998983 260468511638909569058998475)
  ·
    refine ⟨390702767458364353588497713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260468511638909569058998475 390702767458364353588497713)
    ·
      refine ⟨293027075593773265191373285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390702767458364353588497713 293027075593773265191373285)
      ·
        refine ⟨54942576673832487223382491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293027075593773265191373285 54942576673832487223382491)
        ·
          refine ⟨82413865010748730835073737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54942576673832487223382491 82413865010748730835073737)
          ·
            refine ⟨61810398758061548126305303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82413865010748730835073737 61810398758061548126305303)
            ·
              refine ⟨92715598137092322189457955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61810398758061548126305303 92715598137092322189457955)
              ·
                refine ⟨139073397205638483284186933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92715598137092322189457955 139073397205638483284186933)
                ·
                  refine ⟨13038130988028607807892525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139073397205638483284186933 13038130988028607807892525)
                  ·
                    refine ⟨4889299120510727927959697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13038130988028607807892525 4889299120510727927959697)
                    ·
                      refine ⟨3666974340383045945969773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889299120510727927959697 3666974340383045945969773)
                      ·
                        rfl

theorem cell23_7141407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_7141407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141407 prefixEnd_7141407 := by exact prefixLift 7141407
  have htrace : WordTrace (prefixWord ++ tailWord_7141407) baseStart_7141407 baseEnd_7141407 := by
    simpa [prefixWord, tailWord_7141407, baseEnd_7141407] using wordTrace_append hprefix tailTrace_7141407
  have hstable : (prefixWord ++ tailWord_7141407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141407).length < 2 ^ (prefixWord ++ tailWord_7141407).sum := by decide
  have hdescent : baseEnd_7141407 < baseStart_7141407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141441 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7141441 : Nat := 118140960795 + 7141441 * 2 ^ 59
def prefixEnd_7141441 : Nat := 4983230072969 + 3 ^ 40 * 7141441 * 2
def baseEnd_7141441 : Nat := 3666991798725298812944617

theorem tailTrace_7141441 : CollatzResearch.WordTrace tailWord_7141441 prefixEnd_7141441 3666991798725298812944617 := by
  unfold tailWord_7141441
  simp only [CollatzResearch.WordTrace]
  refine ⟨260469751720786392865736177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173646501147190928577157451 260469751720786392865736177)
  ·
    refine ⟨195352313790589794649302133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260469751720786392865736177 195352313790589794649302133)
    ·
      refine ⟨18314279417867793248372075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195352313790589794649302133 18314279417867793248372075)
      ·
        refine ⟨27471419126801689872558113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314279417867793248372075 27471419126801689872558113)
        ·
          refine ⟨20603564345101267404418585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27471419126801689872558113 20603564345101267404418585)
          ·
            refine ⟨15452673258825950553313939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20603564345101267404418585 15452673258825950553313939)
            ·
              refine ⟨23179009888238925829970909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15452673258825950553313939 23179009888238925829970909)
              ·
                refine ⟨8692128708089597186239091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23179009888238925829970909 8692128708089597186239091)
                ·
                  refine ⟨13038193062134395779358637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692128708089597186239091 13038193062134395779358637)
                  ·
                    refine ⟨4889322398300398417259489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13038193062134395779358637 4889322398300398417259489)
                    ·
                      refine ⟨3666991798725298812944617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889322398300398417259489 3666991798725298812944617)
                      ·
                        rfl

theorem cell23_7141441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7141441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141441 prefixEnd_7141441 := by exact prefixLift 7141441
  have htrace : WordTrace (prefixWord ++ tailWord_7141441) baseStart_7141441 baseEnd_7141441 := by
    simpa [prefixWord, tailWord_7141441, baseEnd_7141441] using wordTrace_append hprefix tailTrace_7141441
  have hstable : (prefixWord ++ tailWord_7141441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141441).length < 2 ^ (prefixWord ++ tailWord_7141441).sum := by decide
  have hdescent : baseEnd_7141441 < baseStart_7141441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141507 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 2, 5]
def baseStart_7141507 : Nat := 118140960795 + 7141507 * 2 ^ 59
def prefixEnd_7141507 : Nat := 4983230072969 + 3 ^ 40 * 7141507 * 2
def baseEnd_7141507 : Nat := 1222341896149498518239771

theorem tailTrace_7141507 : CollatzResearch.WordTrace tailWord_7141507 prefixEnd_7141507 1222341896149498518239771 := by
  unfold tailWord_7141507
  simp only [CollatzResearch.WordTrace]
  refine ⟨260472158938547286137638775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173648105959031524091759183 260472158938547286137638775)
  ·
    refine ⟨390708238407820929206458163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260472158938547286137638775 390708238407820929206458163)
    ·
      refine ⟨586062357611731393809687245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390708238407820929206458163 586062357611731393809687245)
      ·
        refine ⟨219773384104399272678632717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586062357611731393809687245 219773384104399272678632717)
        ·
          refine ⟨82415019039149727254487269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219773384104399272678632717 82415019039149727254487269)
          ·
            refine ⟨15452816069840573860216363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82415019039149727254487269 15452816069840573860216363)
            ·
              refine ⟨23179224104760860790324545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15452816069840573860216363 23179224104760860790324545)
              ·
                refine ⟨17384418078570645592743409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23179224104760860790324545 17384418078570645592743409)
                ·
                  refine ⟨13038313558927984194557557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17384418078570645592743409 13038313558927984194557557)
                  ·
                    refine ⟨1222341896149498518239771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13038313558927984194557557 1222341896149498518239771)
                    ·
                      rfl

theorem cell23_7141507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 5].length) (baseStart_7141507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141507 prefixEnd_7141507 := by exact prefixLift 7141507
  have htrace : WordTrace (prefixWord ++ tailWord_7141507) baseStart_7141507 baseEnd_7141507 := by
    simpa [prefixWord, tailWord_7141507, baseEnd_7141507] using wordTrace_append hprefix tailTrace_7141507
  have hstable : (prefixWord ++ tailWord_7141507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141507).length < 2 ^ (prefixWord ++ tailWord_7141507).sum := by decide
  have hdescent : baseEnd_7141507 < baseStart_7141507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141526 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7141526 : Nat := 118140960795 + 7141526 * 2 ^ 59
def prefixEnd_7141526 : Nat := 4983230072969 + 3 ^ 40 * 7141526 * 2
def baseEnd_7141526 : Nat := 3667035444580930980381727

theorem tailTrace_7141526 : CollatzResearch.WordTrace tailWord_7141526 prefixEnd_7141526 3667035444580930980381727 := by
  unfold tailWord_7141526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16279553245342403273911277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173648567950318968255053621 16279553245342403273911277)
  ·
    refine ⟨6104832467003401227716729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16279553245342403273911277 6104832467003401227716729)
    ·
      refine ⟨4578624350252550920787547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6104832467003401227716729 4578624350252550920787547)
      ·
        refine ⟨6867936525378826381181321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578624350252550920787547 6867936525378826381181321)
        ·
          refine ⟨5150952394034119785885991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6867936525378826381181321 5150952394034119785885991)
          ·
            refine ⟨7726428591051179678828987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150952394034119785885991 7726428591051179678828987)
            ·
              refine ⟨11589642886576769518243481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726428591051179678828987 11589642886576769518243481)
              ·
                refine ⟨8692232164932577138682611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11589642886576769518243481 8692232164932577138682611)
                ·
                  refine ⟨13038348247398865708023917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692232164932577138682611 13038348247398865708023917)
                  ·
                    refine ⟨4889380592774574640508969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13038348247398865708023917 4889380592774574640508969)
                    ·
                      refine ⟨3667035444580930980381727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889380592774574640508969 3667035444580930980381727)
                      ·
                        rfl

theorem cell23_7141526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7141526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141526 prefixEnd_7141526 := by exact prefixLift 7141526
  have htrace : WordTrace (prefixWord ++ tailWord_7141526) baseStart_7141526 baseEnd_7141526 := by
    simpa [prefixWord, tailWord_7141526, baseEnd_7141526] using wordTrace_append hprefix tailTrace_7141526
  have hstable : (prefixWord ++ tailWord_7141526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141526).length < 2 ^ (prefixWord ++ tailWord_7141526).sum := by decide
  have hdescent : baseEnd_7141526 < baseStart_7141526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141594 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_7141594 : Nat := 118140960795 + 7141594 * 2 ^ 59
def prefixEnd_7141594 : Nat := 4983230072969 + 3 ^ 40 * 7141594 * 2
def baseEnd_7141594 : Nat := 3667070361265436714331413

theorem tailTrace_7141594 : CollatzResearch.WordTrace tailWord_7141594 prefixEnd_7141594 3667070361265436714331413 := by
  unfold tailWord_7141594
  simp only [CollatzResearch.WordTrace]
  refine ⟨65118833022308024999013959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173650221392821399997370557 65118833022308024999013959)
  ·
    refine ⟨97678249533462037498520939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65118833022308024999013959 97678249533462037498520939)
    ·
      refine ⟨146517374300193056247781409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97678249533462037498520939 146517374300193056247781409)
      ·
        refine ⟨109888030725144792185836057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146517374300193056247781409 109888030725144792185836057)
        ·
          refine ⟨82416023043858594139377043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109888030725144792185836057 82416023043858594139377043)
          ·
            refine ⟨123624034565787891209065565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82416023043858594139377043 123624034565787891209065565)
            ·
              refine ⟨46359012962170459203399587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123624034565787891209065565 46359012962170459203399587)
              ·
                refine ⟨69538519443255688805099381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46359012962170459203399587 69538519443255688805099381)
                ·
                  refine ⟨6519236197805220825478067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69538519443255688805099381 6519236197805220825478067)
                  ·
                    refine ⟨9778854296707831238217101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6519236197805220825478067 9778854296707831238217101)
                    ·
                      refine ⟨3667070361265436714331413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778854296707831238217101 3667070361265436714331413)
                      ·
                        rfl

theorem cell23_7141594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_7141594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141594 prefixEnd_7141594 := by exact prefixLift 7141594
  have htrace : WordTrace (prefixWord ++ tailWord_7141594) baseStart_7141594 baseEnd_7141594 := by
    simpa [prefixWord, tailWord_7141594, baseEnd_7141594] using wordTrace_append hprefix tailTrace_7141594
  have hstable : (prefixWord ++ tailWord_7141594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141594).length < 2 ^ (prefixWord ++ tailWord_7141594).sum := by decide
  have hdescent : baseEnd_7141594 < baseStart_7141594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141628 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_7141628 : Nat := 118140960795 + 7141628 * 2 ^ 59
def prefixEnd_7141628 : Nat := 4983230072969 + 3 ^ 40 * 7141628 * 2
def baseEnd_7141628 : Nat := 3667087819607689581306257

theorem tailTrace_7141628 : CollatzResearch.WordTrace tailWord_7141628 prefixEnd_7141628 3667087819607689581306257 := by
  unfold tailWord_7141628
  simp only [CollatzResearch.WordTrace]
  refine ⟨130238286085554461901396769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173651048114072615868529025 130238286085554461901396769)
  ·
    refine ⟨97678714564165846426047577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130238286085554461901396769 97678714564165846426047577)
    ·
      refine ⟨73259035923124384819535683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97678714564165846426047577 73259035923124384819535683)
      ·
        refine ⟨109888553884686577229303525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73259035923124384819535683 109888553884686577229303525)
        ·
          refine ⟨20604103853378733230494411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109888553884686577229303525 20604103853378733230494411)
          ·
            refine ⟨30906155780068099845741617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20604103853378733230494411 30906155780068099845741617)
            ·
              refine ⟨23179616835051074884306213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30906155780068099845741617 23179616835051074884306213)
              ·
                refine ⟨4346178156572076540807415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23179616835051074884306213 4346178156572076540807415)
                ·
                  refine ⟨6519267234858114811211123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346178156572076540807415 6519267234858114811211123)
                  ·
                    refine ⟨9778900852287172216816685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6519267234858114811211123 9778900852287172216816685)
                    ·
                      refine ⟨3667087819607689581306257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778900852287172216816685 3667087819607689581306257)
                      ·
                        rfl

theorem cell23_7141628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_7141628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141628 prefixEnd_7141628 := by exact prefixLift 7141628
  have htrace : WordTrace (prefixWord ++ tailWord_7141628) baseStart_7141628 baseEnd_7141628 := by
    simpa [prefixWord, tailWord_7141628, baseEnd_7141628] using wordTrace_append hprefix tailTrace_7141628
  have hstable : (prefixWord ++ tailWord_7141628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141628).length < 2 ^ (prefixWord ++ tailWord_7141628).sum := by decide
  have hdescent : baseEnd_7141628 < baseStart_7141628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141637 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_7141637 : Nat := 118140960795 + 7141637 * 2 ^ 59
def prefixEnd_7141637 : Nat := 4983230072969 + 3 ^ 40 * 7141637 * 2
def baseEnd_7141637 : Nat := 3667092440933580046093715

theorem tailTrace_7141637 : CollatzResearch.WordTrace tailWord_7141637 prefixEnd_7141637 3667092440933580046093715 := by
  unfold tailWord_7141637
  simp only [CollatzResearch.WordTrace]
  refine ⟨260476900428076318339871165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173651266952050878893247443 260476900428076318339871165)
  ·
    refine ⟨97678837660528619377451687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260476900428076318339871165 97678837660528619377451687)
    ·
      refine ⟨146518256490792929066177531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97678837660528619377451687 146518256490792929066177531)
      ·
        refine ⟨219777384736189393599266297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146518256490792929066177531 219777384736189393599266297)
        ·
          refine ⟨164833038552142045199449723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219777384736189393599266297 164833038552142045199449723)
          ·
            refine ⟨247249557828213067799174585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164833038552142045199449723 247249557828213067799174585)
            ·
              refine ⟨185437168371159800849380939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247249557828213067799174585 185437168371159800849380939)
              ·
                refine ⟨278155752556739701274071409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185437168371159800849380939 278155752556739701274071409)
                ·
                  refine ⟨208616814417554775955553557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278155752556739701274071409 208616814417554775955553557)
                  ·
                    refine ⟨9778913175822880122916573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208616814417554775955553557 9778913175822880122916573)
                    ·
                      refine ⟨3667092440933580046093715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778913175822880122916573 3667092440933580046093715)
                      ·
                        rfl

theorem cell23_7141637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_7141637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141637 prefixEnd_7141637 := by exact prefixLift 7141637
  have htrace : WordTrace (prefixWord ++ tailWord_7141637) baseStart_7141637 baseEnd_7141637 := by
    simpa [prefixWord, tailWord_7141637, baseEnd_7141637] using wordTrace_append hprefix tailTrace_7141637
  have hstable : (prefixWord ++ tailWord_7141637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141637).length < 2 ^ (prefixWord ++ tailWord_7141637).sum := by decide
  have hdescent : baseEnd_7141637 < baseStart_7141637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141662 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7141662 : Nat := 118140960795 + 7141662 * 2 ^ 59
def prefixEnd_7141662 : Nat := 4983230072969 + 3 ^ 40 * 7141662 * 2
def baseEnd_7141662 : Nat := 3667105277949942448281101

theorem tailTrace_7141662 : CollatzResearch.WordTrace tailWord_7141662 prefixEnd_7141662 3667105277949942448281101 := by
  unfold tailWord_7141662
  simp only [CollatzResearch.WordTrace]
  refine ⟨32559726531623218451191405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173651874835323831739687493 32559726531623218451191405)
  ·
    refine ⟨12209897449358706919196777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32559726531623218451191405 12209897449358706919196777)
    ·
      refine ⟨9157423087019030189397583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12209897449358706919196777 9157423087019030189397583)
      ·
        refine ⟨13736134630528545284096375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9157423087019030189397583 13736134630528545284096375)
        ·
          refine ⟨20604201945792817926144563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13736134630528545284096375 20604201945792817926144563)
          ·
            refine ⟨30906302918689226889216845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20604201945792817926144563 30906302918689226889216845)
            ·
              refine ⟨11589863594508460083456317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30906302918689226889216845 11589863594508460083456317)
              ·
                refine ⟨4346198847940672531296119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11589863594508460083456317 4346198847940672531296119)
                ·
                  refine ⟨6519298271911008796944179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346198847940672531296119 6519298271911008796944179)
                  ·
                    refine ⟨9778947407866513195416269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6519298271911008796944179 9778947407866513195416269)
                    ·
                      refine ⟨3667105277949942448281101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9778947407866513195416269 3667105277949942448281101)
                      ·
                        rfl

theorem cell23_7141662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7141662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141662 prefixEnd_7141662 := by exact prefixLift 7141662
  have htrace : WordTrace (prefixWord ++ tailWord_7141662) baseStart_7141662 baseEnd_7141662 := by
    simpa [prefixWord, tailWord_7141662, baseEnd_7141662] using wordTrace_append hprefix tailTrace_7141662
  have hstable : (prefixWord ++ tailWord_7141662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141662).length < 2 ^ (prefixWord ++ tailWord_7141662).sum := by decide
  have hdescent : baseEnd_7141662 < baseStart_7141662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141707 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4]
def baseStart_7141707 : Nat := 118140960795 + 7141707 * 2 ^ 59
def prefixEnd_7141707 : Nat := 4983230072969 + 3 ^ 40 * 7141707 * 2
def baseEnd_7141707 : Nat := 3667128384579394772218393

theorem tailTrace_7141707 : CollatzResearch.WordTrace tailWord_7141707 prefixEnd_7141707 3667128384579394772218393 := by
  unfold tailWord_7141707
  simp only [CollatzResearch.WordTrace]
  refine ⟨260479453537822720294919375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173652969025215146863279583 260479453537822720294919375)
  ·
    refine ⟨390719180306734080442379063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260479453537822720294919375 390719180306734080442379063)
    ·
      refine ⟨586078770460101120663568595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390719180306734080442379063 586078770460101120663568595)
      ·
        refine ⟨879118155690151680995352893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586078770460101120663568595 879118155690151680995352893)
        ·
          refine ⟨329669308383806880373257335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879118155690151680995352893 329669308383806880373257335)
          ·
            refine ⟨494503962575710320559886003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329669308383806880373257335 494503962575710320559886003)
            ·
              refine ⟨741755943863565480839829005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494503962575710320559886003 741755943863565480839829005)
              ·
                refine ⟨278158478948837055314935877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 741755943863565480839829005 278158478948837055314935877)
                ·
                  refine ⟨52154714802906947871550477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278158478948837055314935877 52154714802906947871550477)
                  ·
                    refine ⟨19558018051090105451831429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52154714802906947871550477 19558018051090105451831429)
                    ·
                      refine ⟨3667128384579394772218393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19558018051090105451831429 3667128384579394772218393)
                      ·
                        rfl

theorem cell23_7141707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_7141707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141707 prefixEnd_7141707 := by exact prefixLift 7141707
  have htrace : WordTrace (prefixWord ++ tailWord_7141707) baseStart_7141707 baseEnd_7141707 := by
    simpa [prefixWord, tailWord_7141707, baseEnd_7141707] using wordTrace_append hprefix tailTrace_7141707
  have hstable : (prefixWord ++ tailWord_7141707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141707).length < 2 ^ (prefixWord ++ tailWord_7141707).sum := by decide
  have hdescent : baseEnd_7141707 < baseStart_7141707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141711 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 1, 3, 2]
def baseStart_7141711 : Nat := 118140960795 + 7141711 * 2 ^ 59
def prefixEnd_7141711 : Nat := 4983230072969 + 3 ^ 40 * 7141711 * 2
def baseEnd_7141711 : Nat := 3667130438502012756568375

theorem tailTrace_7141711 : CollatzResearch.WordTrace tailWord_7141711 prefixEnd_7141711 3667130438502012756568375 := by
  unfold tailWord_7141711
  simp only [CollatzResearch.WordTrace]
  refine ⟨260479599429808228978064987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173653066286538819318709991 260479599429808228978064987)
  ·
    refine ⟨390719399144712343467097481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260479599429808228978064987 390719399144712343467097481)
    ·
      refine ⟨293039549358534257600323111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390719399144712343467097481 293039549358534257600323111)
      ·
        refine ⟨439559324037801386400484667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293039549358534257600323111 439559324037801386400484667)
        ·
          refine ⟨659338986056702079600727001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439559324037801386400484667 659338986056702079600727001)
          ·
            refine ⟨494504239542526559700545251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659338986056702079600727001 494504239542526559700545251)
            ·
              refine ⟨741756359313789839550817877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494504239542526559700545251 741756359313789839550817877)
              ·
                refine ⟨8692457335708474682236147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 741756359313789839550817877 8692457335708474682236147)
                ·
                  refine ⟨13038686003562712023354221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692457335708474682236147 13038686003562712023354221)
                  ·
                    refine ⟨4889507251336017008757833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13038686003562712023354221 4889507251336017008757833)
                    ·
                      refine ⟨3667130438502012756568375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889507251336017008757833 3667130438502012756568375)
                      ·
                        rfl

theorem cell23_7141711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 3, 2].length) (baseStart_7141711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141711 prefixEnd_7141711 := by exact prefixLift 7141711
  have htrace : WordTrace (prefixWord ++ tailWord_7141711) baseStart_7141711 baseEnd_7141711 := by
    simpa [prefixWord, tailWord_7141711, baseEnd_7141711] using wordTrace_append hprefix tailTrace_7141711
  have hstable : (prefixWord ++ tailWord_7141711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141711).length < 2 ^ (prefixWord ++ tailWord_7141711).sum := by decide
  have hdescent : baseEnd_7141711 < baseStart_7141711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141741 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7141741 : Nat := 118140960795 + 7141741 * 2 ^ 59
def prefixEnd_7141741 : Nat := 4983230072969 + 3 ^ 40 * 7141741 * 2
def baseEnd_7141741 : Nat := 3667145842921647639193237

theorem tailTrace_7141741 : CollatzResearch.WordTrace tailWord_7141741 prefixEnd_7141741 3667145842921647639193237 := by
  unfold tailWord_7141741
  simp only [CollatzResearch.WordTrace]
  refine ⟨260480693619699544101657077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173653795746466362734438051 260480693619699544101657077)
  ·
    refine ⟨24420065026846832259530351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260480693619699544101657077 24420065026846832259530351)
    ·
      refine ⟨36630097540270248389295527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24420065026846832259530351 36630097540270248389295527)
      ·
        refine ⟨54945146310405372583943291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36630097540270248389295527 54945146310405372583943291)
        ·
          refine ⟨82417719465608058875914937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54945146310405372583943291 82417719465608058875914937)
          ·
            refine ⟨61813289599206044156936203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82417719465608058875914937 61813289599206044156936203)
            ·
              refine ⟨92719934398809066235404305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61813289599206044156936203 92719934398809066235404305)
              ·
                refine ⟨69539950799106799676553229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92719934398809066235404305 69539950799106799676553229)
                ·
                  refine ⟨26077481549665049878707461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69539950799106799676553229 26077481549665049878707461)
                  ·
                    refine ⟨4889527790562196852257649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26077481549665049878707461 4889527790562196852257649)
                    ·
                      refine ⟨3667145842921647639193237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889527790562196852257649 3667145842921647639193237)
                      ·
                        rfl

theorem cell23_7141741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7141741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141741 prefixEnd_7141741 := by exact prefixLift 7141741
  have htrace : WordTrace (prefixWord ++ tailWord_7141741) baseStart_7141741 baseEnd_7141741 := by
    simpa [prefixWord, tailWord_7141741, baseEnd_7141741] using wordTrace_append hprefix tailTrace_7141741
  have hstable : (prefixWord ++ tailWord_7141741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141741).length < 2 ^ (prefixWord ++ tailWord_7141741).sum := by decide
  have hdescent : baseEnd_7141741 < baseStart_7141741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141744 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_7141744 : Nat := 118140960795 + 7141744 * 2 ^ 59
def prefixEnd_7141744 : Nat := 4983230072969 + 3 ^ 40 * 7141744 * 2
def baseEnd_7141744 : Nat := 3667147383363611127455723

theorem tailTrace_7141744 : CollatzResearch.WordTrace tailWord_7141744 prefixEnd_7141744 3667147383363611127455723 := by
  unfold tailWord_7141744
  simp only [CollatzResearch.WordTrace]
  refine ⟨130240401519344337807008143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173653868692459117076010857 130240401519344337807008143)
  ·
    refine ⟨195360602279016506710512215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130240401519344337807008143 195360602279016506710512215)
    ·
      refine ⟨293040903418524760065768323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195360602279016506710512215 293040903418524760065768323)
      ·
        refine ⟨439561355127787140098652485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293040903418524760065768323 439561355127787140098652485)
        ·
          refine ⟨82417754086460088768497341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439561355127787140098652485 82417754086460088768497341)
          ·
            refine ⟨30906657782422533288186503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82417754086460088768497341 30906657782422533288186503)
            ·
              refine ⟨46359986673633799932279755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30906657782422533288186503 46359986673633799932279755)
              ·
                refine ⟨69539980010450699898419633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46359986673633799932279755 69539980010450699898419633)
                ·
                  refine ⟨52154985007838024923814725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69539980010450699898419633 52154985007838024923814725)
                  ·
                    refine ⟨9779059688969629673215261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52154985007838024923814725 9779059688969629673215261)
                    ·
                      refine ⟨3667147383363611127455723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9779059688969629673215261 3667147383363611127455723)
                      ·
                        rfl

theorem cell23_7141744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_7141744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141744 prefixEnd_7141744 := by exact prefixLift 7141744
  have htrace : WordTrace (prefixWord ++ tailWord_7141744) baseStart_7141744 baseEnd_7141744 := by
    simpa [prefixWord, tailWord_7141744, baseEnd_7141744] using wordTrace_append hprefix tailTrace_7141744
  have hstable : (prefixWord ++ tailWord_7141744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141744).length < 2 ^ (prefixWord ++ tailWord_7141744).sum := by decide
  have hdescent : baseEnd_7141744 < baseStart_7141744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141764 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 7]
def baseStart_7141764 : Nat := 118140960795 + 7141764 * 2 ^ 59
def prefixEnd_7141764 : Nat := 4983230072969 + 3 ^ 40 * 7141764 * 2
def baseEnd_7141764 : Nat := 407461961441855672133959

theorem tailTrace_7141764 : CollatzResearch.WordTrace tailWord_7141764 prefixEnd_7141764 407461961441855672133959 := by
  unfold tailWord_7141764
  simp only [CollatzResearch.WordTrace]
  refine ⟨130240766249308109514872173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173654354999077479353162897 130240766249308109514872173)
  ·
    refine ⟨48840287343490541068077065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130240766249308109514872173 48840287343490541068077065)
    ·
      refine ⟨36630215507617905801057799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48840287343490541068077065 36630215507617905801057799)
      ·
        refine ⟨54945323261426858701586699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36630215507617905801057799 54945323261426858701586699)
        ·
          refine ⟨82417984892140288052380049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54945323261426858701586699 82417984892140288052380049)
          ·
            refine ⟨61813488669105216039285037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82417984892140288052380049 61813488669105216039285037)
            ·
              refine ⟨23180058250914456014731889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61813488669105216039285037 23180058250914456014731889)
              ·
                refine ⟨17385043688185842011048917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23180058250914456014731889 17385043688185842011048917)
                ·
                  refine ⟨407461961441855672133959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17385043688185842011048917 407461961441855672133959)
                  ·
                    rfl

theorem cell23_7141764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_7141764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141764 prefixEnd_7141764 := by exact prefixLift 7141764
  have htrace : WordTrace (prefixWord ++ tailWord_7141764) baseStart_7141764 baseEnd_7141764 := by
    simpa [prefixWord, tailWord_7141764, baseEnd_7141764] using wordTrace_append hprefix tailTrace_7141764
  have hstable : (prefixWord ++ tailWord_7141764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141764).length < 2 ^ (prefixWord ++ tailWord_7141764).sum := by decide
  have hdescent : baseEnd_7141764 < baseStart_7141764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141787 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_7141787 : Nat := 118140960795 + 7141787 * 2 ^ 59
def prefixEnd_7141787 : Nat := 4983230072969 + 3 ^ 40 * 7141787 * 2
def baseEnd_7141787 : Nat := 3667169463031754459218025

theorem tailTrace_7141787 : CollatzResearch.WordTrace tailWord_7141787 prefixEnd_7141787 3667169463031754459218025 := by
  unfold tailWord_7141787
  simp only [CollatzResearch.WordTrace]
  refine ⟨260482371377532893957831615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173654914251688595971887743 260482371377532893957831615)
  ·
    refine ⟨390723557066299340936747423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260482371377532893957831615 390723557066299340936747423)
    ·
      refine ⟨586085335599449011405121135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390723557066299340936747423 586085335599449011405121135)
      ·
        refine ⟨879128003399173517107681703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586085335599449011405121135 879128003399173517107681703)
        ·
          refine ⟨1318692005098760275661522555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879128003399173517107681703 1318692005098760275661522555)
          ·
            refine ⟨1978038007648140413492283833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318692005098760275661522555 1978038007648140413492283833)
            ·
              refine ⟨1483528505736105310119212875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978038007648140413492283833 1483528505736105310119212875)
              ·
                refine ⟨2225292758604157965178819313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483528505736105310119212875 2225292758604157965178819313)
                ·
                  refine ⟨1668969568953118473884114485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225292758604157965178819313 1668969568953118473884114485)
                  ·
                    refine ⟨156465897089354856926635733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1668969568953118473884114485 156465897089354856926635733)
                    ·
                      refine ⟨3667169463031754459218025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156465897089354856926635733 3667169463031754459218025)
                      ·
                        rfl

theorem cell23_7141787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_7141787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141787 prefixEnd_7141787 := by exact prefixLift 7141787
  have htrace : WordTrace (prefixWord ++ tailWord_7141787) baseStart_7141787 baseEnd_7141787 := by
    simpa [prefixWord, tailWord_7141787, baseEnd_7141787] using wordTrace_append hprefix tailTrace_7141787
  have hstable : (prefixWord ++ tailWord_7141787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141787).length < 2 ^ (prefixWord ++ tailWord_7141787).sum := by decide
  have hdescent : baseEnd_7141787 < baseStart_7141787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141904 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_7141904 : Nat := 118140960795 + 7141904 * 2 ^ 59
def prefixEnd_7141904 : Nat := 4983230072969 + 3 ^ 40 * 7141904 * 2
def baseEnd_7141904 : Nat := 3667229540268330501454987

theorem tailTrace_7141904 : CollatzResearch.WordTrace tailWord_7141904 prefixEnd_7141904 3667229540268330501454987 := by
  unfold tailWord_7141904
  simp only [CollatzResearch.WordTrace]
  refine ⟨130243319359054511469920383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173657759145406015293227177 130243319359054511469920383)
  ·
    refine ⟨195364979038581767204880575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130243319359054511469920383 195364979038581767204880575)
    ·
      refine ⟨293047468557872650807320863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195364979038581767204880575 293047468557872650807320863)
      ·
        refine ⟨439571202836808976210981295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293047468557872650807320863 439571202836808976210981295)
        ·
          refine ⟨659356804255213464316471943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439571202836808976210981295 659356804255213464316471943)
          ·
            refine ⟨989035206382820196474707915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659356804255213464316471943 989035206382820196474707915)
            ·
              refine ⟨1483552809574230294712061873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989035206382820196474707915 1483552809574230294712061873)
              ·
                refine ⟨1112664607180672721034046405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483552809574230294712061873 1112664607180672721034046405)
                ·
                  refine ⟨208624613846376135193883701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112664607180672721034046405 208624613846376135193883701)
                  ·
                    refine ⟨19558557548097762674426597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208624613846376135193883701 19558557548097762674426597)
                    ·
                      refine ⟨3667229540268330501454987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19558557548097762674426597 3667229540268330501454987)
                      ·
                        rfl

theorem cell23_7141904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_7141904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141904 prefixEnd_7141904 := by exact prefixLift 7141904
  have htrace : WordTrace (prefixWord ++ tailWord_7141904) baseStart_7141904 baseEnd_7141904 := by
    simpa [prefixWord, tailWord_7141904, baseEnd_7141904] using wordTrace_append hprefix tailTrace_7141904
  have hstable : (prefixWord ++ tailWord_7141904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141904).length < 2 ^ (prefixWord ++ tailWord_7141904).sum := by decide
  have hdescent : baseEnd_7141904 < baseStart_7141904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141921 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7141921 : Nat := 118140960795 + 7141921 * 2 ^ 59
def prefixEnd_7141921 : Nat := 4983230072969 + 3 ^ 40 * 7141921 * 2
def baseEnd_7141921 : Nat := 3667238269439456934942409

theorem tailTrace_7141921 : CollatzResearch.WordTrace tailWord_7141921 prefixEnd_7141921 3667238269439456934942409 := by
  unfold tailWord_7141921
  simp only [CollatzResearch.WordTrace]
  refine ⟨260487258759047434843209617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173658172506031623228806411 260487258759047434843209617)
  ·
    refine ⟨195365444069285576132407213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260487258759047434843209617 195365444069285576132407213)
    ·
      refine ⟨73262041525982091049652705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195365444069285576132407213 73262041525982091049652705)
      ·
        refine ⟨54946531144486568287239529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73262041525982091049652705 54946531144486568287239529)
        ·
          refine ⟨41209898358364926215429647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54946531144486568287239529 41209898358364926215429647)
          ·
            refine ⟨61814847537547389323144471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41209898358364926215429647 61814847537547389323144471)
            ·
              refine ⟨92722271306321083984716707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61814847537547389323144471 92722271306321083984716707)
              ·
                refine ⟨139083406959481625977075061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92722271306321083984716707 139083406959481625977075061)
                ·
                  refine ⟨13039069402451402435350787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139083406959481625977075061 13039069402451402435350787)
                  ·
                    refine ⟨19558604103677103653026181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13039069402451402435350787 19558604103677103653026181)
                    ·
                      refine ⟨3667238269439456934942409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19558604103677103653026181 3667238269439456934942409)
                      ·
                        rfl

theorem cell23_7141921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7141921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141921 prefixEnd_7141921 := by exact prefixLift 7141921
  have htrace : WordTrace (prefixWord ++ tailWord_7141921) baseStart_7141921 baseEnd_7141921 := by
    simpa [prefixWord, tailWord_7141921, baseEnd_7141921] using wordTrace_append hprefix tailTrace_7141921
  have hstable : (prefixWord ++ tailWord_7141921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141921).length < 2 ^ (prefixWord ++ tailWord_7141921).sum := by decide
  have hdescent : baseEnd_7141921 < baseStart_7141921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141942 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_7141942 : Nat := 118140960795 + 7141942 * 2 ^ 59
def prefixEnd_7141942 : Nat := 4983230072969 + 3 ^ 40 * 7141942 * 2
def baseEnd_7141942 : Nat := 3667249052533201352779813

theorem tailTrace_7141942 : CollatzResearch.WordTrace tailWord_7141942 prefixEnd_7141942 3667249052533201352779813 := by
  unfold tailWord_7141942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280501543248209714357755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173658683127980903619816053 16280501543248209714357755)
  ·
    refine ⟨24420752314872314571536633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16280501543248209714357755 24420752314872314571536633)
    ·
      refine ⟨18315564236154235928652475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24420752314872314571536633 18315564236154235928652475)
      ·
        refine ⟨27473346354231353892978713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18315564236154235928652475 27473346354231353892978713)
        ·
          refine ⟨20605009765673515419734035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27473346354231353892978713 20605009765673515419734035)
          ·
            refine ⟨30907514648510273129601053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20605009765673515419734035 30907514648510273129601053)
            ·
              refine ⟨11590317993191352423600395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30907514648510273129601053 11590317993191352423600395)
              ·
                refine ⟨17385476989787028635400593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590317993191352423600395 17385476989787028635400593)
                ·
                  refine ⟨13039107742340271476550445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17385476989787028635400593 13039107742340271476550445)
                  ·
                    refine ⟨4889665403377601803706417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13039107742340271476550445 4889665403377601803706417)
                    ·
                      refine ⟨3667249052533201352779813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889665403377601803706417 3667249052533201352779813)
                      ·
                        rfl

theorem cell23_7141942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_7141942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141942 prefixEnd_7141942 := by exact prefixLift 7141942
  have htrace : WordTrace (prefixWord ++ tailWord_7141942) baseStart_7141942 baseEnd_7141942 := by
    simpa [prefixWord, tailWord_7141942, baseEnd_7141942] using wordTrace_append hprefix tailTrace_7141942
  have hstable : (prefixWord ++ tailWord_7141942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141942).length < 2 ^ (prefixWord ++ tailWord_7141942).sum := by decide
  have hdescent : baseEnd_7141942 < baseStart_7141942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141951 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_7141951 : Nat := 118140960795 + 7141951 * 2 ^ 59
def prefixEnd_7141951 : Nat := 4983230072969 + 3 ^ 40 * 7141951 * 2
def baseEnd_7141951 : Nat := 3667253673859091817567271

theorem tailTrace_7141951 : CollatzResearch.WordTrace tailWord_7141951 prefixEnd_7141951 3667253673859091817567271 := by
  unfold tailWord_7141951
  simp only [CollatzResearch.WordTrace]
  refine ⟨260488352948938749966801707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173658901965959166644534471 260488352948938749966801707)
  ·
    refine ⟨390732529423408124950202561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260488352948938749966801707 390732529423408124950202561)
    ·
      refine ⟨293049397067556093712651921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390732529423408124950202561 293049397067556093712651921)
      ·
        refine ⟨219787047800667070284488941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293049397067556093712651921 219787047800667070284488941)
        ·
          refine ⟨82420142925250151356683353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219787047800667070284488941 82420142925250151356683353)
          ·
            refine ⟨61815107193937613517512515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82420142925250151356683353 61815107193937613517512515)
            ·
              refine ⟨92722660790906420276268773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61815107193937613517512515 92722660790906420276268773)
              ·
                refine ⟨17385498898294953801800395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92722660790906420276268773 17385498898294953801800395)
                ·
                  refine ⟨26078248347442430702700593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17385498898294953801800395 26078248347442430702700593)
                  ·
                    refine ⟨19558686260581823027025445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26078248347442430702700593 19558686260581823027025445)
                    ·
                      refine ⟨3667253673859091817567271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19558686260581823027025445 3667253673859091817567271)
                      ·
                        rfl

theorem cell23_7141951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_7141951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141951 prefixEnd_7141951 := by exact prefixLift 7141951
  have htrace : WordTrace (prefixWord ++ tailWord_7141951) baseStart_7141951 baseEnd_7141951 := by
    simpa [prefixWord, tailWord_7141951, baseEnd_7141951] using wordTrace_append hprefix tailTrace_7141951
  have hstable : (prefixWord ++ tailWord_7141951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141951).length < 2 ^ (prefixWord ++ tailWord_7141951).sum := by decide
  have hdescent : baseEnd_7141951 < baseStart_7141951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141965 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7141965 : Nat := 118140960795 + 7141965 * 2 ^ 59
def prefixEnd_7141965 : Nat := 4983230072969 + 3 ^ 40 * 7141965 * 2
def baseEnd_7141965 : Nat := 1222420287529418254264069

theorem tailTrace_7141965 : CollatzResearch.WordTrace tailWord_7141965 prefixEnd_7141965 1222420287529418254264069 := by
  unfold tailWord_7141965
  simp only [CollatzResearch.WordTrace]
  refine ⟨260488863570888030357811349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173659242380592020238540899 260488863570888030357811349)
  ·
    refine ⟨12210415479885376423022407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260488863570888030357811349 12210415479885376423022407)
    ·
      refine ⟨18315623219828064634533611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12210415479885376423022407 18315623219828064634533611)
      ·
        refine ⟨27473434829742096951800417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18315623219828064634533611 27473434829742096951800417)
        ·
          refine ⟨20605076122306572713850313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27473434829742096951800417 20605076122306572713850313)
          ·
            refine ⟨15453807091729929535387735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20605076122306572713850313 15453807091729929535387735)
            ·
              refine ⟨23180710637594894303081603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15453807091729929535387735 23180710637594894303081603)
              ·
                refine ⟨34771065956392341454622405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23180710637594894303081603 34771065956392341454622405)
                ·
                  refine ⟨6519574866823564022741701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34771065956392341454622405 6519574866823564022741701)
                  ·
                    refine ⟨1222420287529418254264069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519574866823564022741701 1222420287529418254264069)
                    ·
                      rfl

theorem cell23_7141965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7141965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141965 prefixEnd_7141965 := by exact prefixLift 7141965
  have htrace : WordTrace (prefixWord ++ tailWord_7141965) baseStart_7141965 baseEnd_7141965 := by
    simpa [prefixWord, tailWord_7141965, baseEnd_7141965] using wordTrace_append hprefix tailTrace_7141965
  have hstable : (prefixWord ++ tailWord_7141965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141965).length < 2 ^ (prefixWord ++ tailWord_7141965).sum := by decide
  have hdescent : baseEnd_7141965 < baseStart_7141965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141972 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_7141972 : Nat := 118140960795 + 7141972 * 2 ^ 59
def prefixEnd_7141972 : Nat := 4983230072969 + 3 ^ 40 * 7141972 * 2
def baseEnd_7141972 : Nat := 3667264456952836235404675

theorem tailTrace_7141972 : CollatzResearch.WordTrace tailWord_7141972 prefixEnd_7141972 3667264456952836235404675 := by
  unfold tailWord_7141972
  simp only [CollatzResearch.WordTrace]
  refine ⟨130244559440931335276658085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173659412587908447035544113 130244559440931335276658085)
  ·
    refine ⟨24420854895174625364373391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130244559440931335276658085 24420854895174625364373391)
    ·
      refine ⟨36631282342761938046560087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24420854895174625364373391 36631282342761938046560087)
      ·
        refine ⟨54946923514142907069840131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36631282342761938046560087 54946923514142907069840131)
        ·
          refine ⟨82420385271214360604760197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54946923514142907069840131 82420385271214360604760197)
          ·
            refine ⟨15453822238352692613392537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82420385271214360604760197 15453822238352692613392537)
            ·
              refine ⟨11590366678764519460044403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15453822238352692613392537 11590366678764519460044403)
              ·
                refine ⟨17385550018146779190066605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590366678764519460044403 17385550018146779190066605)
                ·
                  refine ⟨6519581256805042196274977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17385550018146779190066605 6519581256805042196274977)
                  ·
                    refine ⟨4889685942603781647206233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6519581256805042196274977 4889685942603781647206233)
                    ·
                      refine ⟨3667264456952836235404675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889685942603781647206233 3667264456952836235404675)
                      ·
                        rfl

theorem cell23_7141972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_7141972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141972 prefixEnd_7141972 := by exact prefixLift 7141972
  have htrace : WordTrace (prefixWord ++ tailWord_7141972) baseStart_7141972 baseEnd_7141972 := by
    simpa [prefixWord, tailWord_7141972, baseEnd_7141972] using wordTrace_append hprefix tailTrace_7141972
  have hstable : (prefixWord ++ tailWord_7141972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141972).length < 2 ^ (prefixWord ++ tailWord_7141972).sum := by decide
  have hdescent : baseEnd_7141972 < baseStart_7141972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7141992 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7141992 : Nat := 118140960795 + 7141992 * 2 ^ 59
def prefixEnd_7141992 : Nat := 4983230072969 + 3 ^ 40 * 7141992 * 2
def baseEnd_7141992 : Nat := 3667274726565926157154583

theorem tailTrace_7141992 : CollatzResearch.WordTrace tailWord_7141992 prefixEnd_7141992 3667274726565926157154583 := by
  unfold tailWord_7141992
  simp only [CollatzResearch.WordTrace]
  refine ⟨130244924170895106984522115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173659898894526809312696153 130244924170895106984522115)
  ·
    refine ⟨195367386256342660476783173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130244924170895106984522115 195367386256342660476783173)
    ·
      refine ⟨36631384923064248839396845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195367386256342660476783173 36631384923064248839396845)
      ·
        refine ⟨13736769346149093314773817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36631384923064248839396845 13736769346149093314773817)
        ·
          refine ⟨10302577009611819986080363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13736769346149093314773817 10302577009611819986080363)
          ·
            refine ⟨15453865514417729979120545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10302577009611819986080363 15453865514417729979120545)
            ·
              refine ⟨11590399135813297484340409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15453865514417729979120545 11590399135813297484340409)
              ·
                refine ⟨8692799351859973113255307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11590399135813297484340409 8692799351859973113255307)
                ·
                  refine ⟨13039199027789959669882961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692799351859973113255307 13039199027789959669882961)
                  ·
                    refine ⟨9779399270842469752412221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13039199027789959669882961 9779399270842469752412221)
                    ·
                      refine ⟨3667274726565926157154583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9779399270842469752412221 3667274726565926157154583)
                      ·
                        rfl

theorem cell23_7141992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7141992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7141992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7141992 prefixEnd_7141992 := by exact prefixLift 7141992
  have htrace : WordTrace (prefixWord ++ tailWord_7141992) baseStart_7141992 baseEnd_7141992 := by
    simpa [prefixWord, tailWord_7141992, baseEnd_7141992] using wordTrace_append hprefix tailTrace_7141992
  have hstable : (prefixWord ++ tailWord_7141992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7141992).length < 2 ^ (prefixWord ++ tailWord_7141992).sum := by decide
  have hdescent : baseEnd_7141992 < baseStart_7141992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7141992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142028 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 5, 4, 2]
def baseStart_7142028 : Nat := 118140960795 + 7142028 * 2 ^ 59
def prefixEnd_7142028 : Nat := 4983230072969 + 3 ^ 40 * 7142028 * 2
def baseEnd_7142028 : Nat := 3667293211869488016304417

theorem tailTrace_7142028 : CollatzResearch.WordTrace tailWord_7142028 prefixEnd_7142028 3667293211869488016304417 := by
  unfold tailWord_7142028
  simp only [CollatzResearch.WordTrace]
  refine ⟨130245580684829896058677369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173660774246439861411569825 130245580684829896058677369)
  ·
    refine ⟨97684185513622422044008027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130245580684829896058677369 97684185513622422044008027)
    ·
      refine ⟨146526278270433633066012041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97684185513622422044008027 146526278270433633066012041)
      ·
        refine ⟨109894708702825224799509031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146526278270433633066012041 109894708702825224799509031)
        ·
          refine ⟨164842063054237837199263547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109894708702825224799509031 164842063054237837199263547)
          ·
            refine ⟨247263094581356755798895321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164842063054237837199263547 247263094581356755798895321)
            ·
              refine ⟨185447320936017566849171491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247263094581356755798895321 185447320936017566849171491)
              ·
                refine ⟨278170981404026350273757237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185447320936017566849171491 278170981404026350273757237)
                ·
                  refine ⟨26078529506627470338164741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278170981404026350273757237 26078529506627470338164741)
                  ·
                    refine ⟨4889724282492650688405889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26078529506627470338164741 4889724282492650688405889)
                    ·
                      refine ⟨3667293211869488016304417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889724282492650688405889 3667293211869488016304417)
                      ·
                        rfl

theorem cell23_7142028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_7142028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142028 prefixEnd_7142028 := by exact prefixLift 7142028
  have htrace : WordTrace (prefixWord ++ tailWord_7142028) baseStart_7142028 baseEnd_7142028 := by
    simpa [prefixWord, tailWord_7142028, baseEnd_7142028] using wordTrace_append hprefix tailTrace_7142028
  have hstable : (prefixWord ++ tailWord_7142028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142028).length < 2 ^ (prefixWord ++ tailWord_7142028).sum := by decide
  have hdescent : baseEnd_7142028 < baseStart_7142028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142031 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_7142031 : Nat := 118140960795 + 7142031 * 2 ^ 59
def prefixEnd_7142031 : Nat := 4983230072969 + 3 ^ 40 * 7142031 * 2
def baseEnd_7142031 : Nat := 3667294752311451504566903

theorem tailTrace_7142031 : CollatzResearch.WordTrace tailWord_7142031 prefixEnd_7142031 3667294752311451504566903 := by
  unfold tailWord_7142031
  simp only [CollatzResearch.WordTrace]
  refine ⟨260491270788648923629713947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173660847192432615753142631 260491270788648923629713947)
  ·
    refine ⟨390736906182973385444570921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260491270788648923629713947 390736906182973385444570921)
    ·
      refine ⟨293052679637230039083428191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390736906182973385444570921 293052679637230039083428191)
      ·
        refine ⟨439579019455845058625142287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293052679637230039083428191 439579019455845058625142287)
        ·
          refine ⟨659368529183767587937713431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439579019455845058625142287 659368529183767587937713431)
          ·
            refine ⟨989052793775651381906570147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659368529183767587937713431 989052793775651381906570147)
            ·
              refine ⟨1483579190663477072859855221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989052793775651381906570147 1483579190663477072859855221)
              ·
                refine ⟨139085549124700975580611427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1483579190663477072859855221 139085549124700975580611427)
                ·
                  refine ⟨208628323687051463370917141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139085549124700975580611427 208628323687051463370917141)
                  ·
                    refine ⟨9779452672830537345511741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208628323687051463370917141 9779452672830537345511741)
                    ·
                      refine ⟨3667294752311451504566903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9779452672830537345511741 3667294752311451504566903)
                      ·
                        rfl

theorem cell23_7142031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_7142031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142031 prefixEnd_7142031 := by exact prefixLift 7142031
  have htrace : WordTrace (prefixWord ++ tailWord_7142031) baseStart_7142031 baseEnd_7142031 := by
    simpa [prefixWord, tailWord_7142031, baseEnd_7142031] using wordTrace_append hprefix tailTrace_7142031
  have hstable : (prefixWord ++ tailWord_7142031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142031).length < 2 ^ (prefixWord ++ tailWord_7142031).sum := by decide
  have hdescent : baseEnd_7142031 < baseStart_7142031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142041 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_7142041 : Nat := 118140960795 + 7142041 * 2 ^ 59
def prefixEnd_7142041 : Nat := 4983230072969 + 3 ^ 40 * 7142041 * 2
def baseEnd_7142041 : Nat := 3667299887117996465441857

theorem tailTrace_7142041 : CollatzResearch.WordTrace tailWord_7142041 prefixEnd_7142041 3667299887117996465441857 := by
  unfold tailWord_7142041
  simp only [CollatzResearch.WordTrace]
  refine ⟨260491635518612695337577977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173661090345741796891718651 260491635518612695337577977)
  ·
    refine ⟨195368726638959521503183483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260491635518612695337577977 195368726638959521503183483)
    ·
      refine ⟨293053089958439282254775225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195368726638959521503183483 293053089958439282254775225)
      ·
        refine ⟨219789817468829461691081419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293053089958439282254775225 219789817468829461691081419)
        ·
          refine ⟨329684726203244192536622129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219789817468829461691081419 329684726203244192536622129)
          ·
            refine ⟨247263544652433144402466597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329684726203244192536622129 247263544652433144402466597)
            ·
              refine ⟨46361914622331214575462487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247263544652433144402466597 46361914622331214575462487)
              ·
                refine ⟨69542871933496821863193731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46361914622331214575462487 69542871933496821863193731)
                ·
                  refine ⟨104314307900245232794790597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69542871933496821863193731 104314307900245232794790597)
                  ·
                    refine ⟨19558932731295981149023237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104314307900245232794790597 19558932731295981149023237)
                    ·
                      refine ⟨3667299887117996465441857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19558932731295981149023237 3667299887117996465441857)
                      ·
                        rfl

theorem cell23_7142041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_7142041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142041 prefixEnd_7142041 := by exact prefixLift 7142041
  have htrace : WordTrace (prefixWord ++ tailWord_7142041) baseStart_7142041 baseEnd_7142041 := by
    simpa [prefixWord, tailWord_7142041, baseEnd_7142041] using wordTrace_append hprefix tailTrace_7142041
  have hstable : (prefixWord ++ tailWord_7142041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142041).length < 2 ^ (prefixWord ++ tailWord_7142041).sum := by decide
  have hdescent : baseEnd_7142041 < baseStart_7142041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142049 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7142049 : Nat := 118140960795 + 7142049 * 2 ^ 59
def prefixEnd_7142049 : Nat := 4983230072969 + 3 ^ 40 * 7142049 * 2
def baseEnd_7142049 : Nat := 3667303994963232434141821

theorem tailTrace_7142049 : CollatzResearch.WordTrace tailWord_7142049 prefixEnd_7142049 3667303994963232434141821 := by
  unfold tailWord_7142049
  simp only [CollatzResearch.WordTrace]
  refine ⟨260491927302583712703869201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173661284868389141802579467 260491927302583712703869201)
  ·
    refine ⟨195368945476937784527901901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260491927302583712703869201 195368945476937784527901901)
    ·
      refine ⟨73263354553851669197963213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195368945476937784527901901 73263354553851669197963213)
      ·
        refine ⟨27473757957694375949236205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73263354553851669197963213 27473757957694375949236205)
        ·
          refine ⟨10302659234135390980963577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27473757957694375949236205 10302659234135390980963577)
          ·
            refine ⟨7726994425601543235722683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10302659234135390980963577 7726994425601543235722683)
            ·
              refine ⟨11590491638402314853584025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726994425601543235722683 11590491638402314853584025)
              ·
                refine ⟨8692868728801736140188019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11590491638402314853584025 8692868728801736140188019)
                ·
                  refine ⟨13039303093202604210282029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692868728801736140188019 13039303093202604210282029)
                  ·
                    refine ⟨4889738659950976578855761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13039303093202604210282029 4889738659950976578855761)
                    ·
                      refine ⟨3667303994963232434141821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889738659950976578855761 3667303994963232434141821)
                      ·
                        rfl

theorem cell23_7142049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7142049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142049 prefixEnd_7142049 := by exact prefixLift 7142049
  have htrace : WordTrace (prefixWord ++ tailWord_7142049) baseStart_7142049 baseEnd_7142049 := by
    simpa [prefixWord, tailWord_7142049, baseEnd_7142049] using wordTrace_append hprefix tailTrace_7142049
  have hstable : (prefixWord ++ tailWord_7142049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142049).length < 2 ^ (prefixWord ++ tailWord_7142049).sum := by decide
  have hdescent : baseEnd_7142049 < baseStart_7142049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142062 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7142062 : Nat := 118140960795 + 7142062 * 2 ^ 59
def prefixEnd_7142062 : Nat := 4983230072969 + 3 ^ 40 * 7142062 * 2
def baseEnd_7142062 : Nat := 3667310670211740883279261

theorem tailTrace_7142062 : CollatzResearch.WordTrace tailWord_7142062 prefixEnd_7142062 3667310670211740883279261 := by
  unfold tailWord_7142062
  simp only [CollatzResearch.WordTrace]
  refine ⟨32561550181442076990511555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173661600967691077282728293 32561550181442076990511555)
  ·
    refine ⟨48842325272163115485767333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32561550181442076990511555 48842325272163115485767333)
    ·
      refine ⟨9157935988530584153581375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48842325272163115485767333 9157935988530584153581375)
      ·
        refine ⟨13736903982795876230372063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9157935988530584153581375 13736903982795876230372063)
        ·
          refine ⟨20605355974193814345558095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13736903982795876230372063 20605355974193814345558095)
          ·
            refine ⟨30908033961290721518337143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20605355974193814345558095 30908033961290721518337143)
            ·
              refine ⟨46362050941936082277505715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30908033961290721518337143 46362050941936082277505715)
              ·
                refine ⟨69543076412904123416258573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46362050941936082277505715 69543076412904123416258573)
                ·
                  refine ⟨26078653654839046281096965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69543076412904123416258573 26078653654839046281096965)
                  ·
                    refine ⟨4889747560282321177705681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26078653654839046281096965 4889747560282321177705681)
                    ·
                      refine ⟨3667310670211740883279261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889747560282321177705681 3667310670211740883279261)
                      ·
                        rfl

theorem cell23_7142062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7142062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142062 prefixEnd_7142062 := by exact prefixLift 7142062
  have htrace : WordTrace (prefixWord ++ tailWord_7142062) baseStart_7142062 baseEnd_7142062 := by
    simpa [prefixWord, tailWord_7142062, baseEnd_7142062] using wordTrace_append hprefix tailTrace_7142062
  have hstable : (prefixWord ++ tailWord_7142062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142062).length < 2 ^ (prefixWord ++ tailWord_7142062).sum := by decide
  have hdescent : baseEnd_7142062 < baseStart_7142062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142115 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 2, 5]
def baseStart_7142115 : Nat := 118140960795 + 7142115 * 2 ^ 59
def prefixEnd_7142115 : Nat := 4983230072969 + 3 ^ 40 * 7142115 * 2
def baseEnd_7142115 : Nat := 1222445961562143058638839

theorem tailTrace_7142115 : CollatzResearch.WordTrace tailWord_7142115 prefixEnd_7142115 1222445961562143058638839 := by
  unfold tailWord_7142115
  simp only [CollatzResearch.WordTrace]
  refine ⟨260494334520344605975771799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173662889680229737317181199 260494334520344605975771799)
  ·
    refine ⟨390741501780516908963657699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260494334520344605975771799 390741501780516908963657699)
    ·
      refine ⟨586112252670775363445486549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390741501780516908963657699 586112252670775363445486549)
      ·
        refine ⟨13737005921971297580753591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 586112252670775363445486549 13737005921971297580753591)
        ·
          refine ⟨20605508882956946371130387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13737005921971297580753591 20605508882956946371130387)
          ·
            refine ⟨30908263324435419556695581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20605508882956946371130387 30908263324435419556695581)
            ·
              refine ⟨11590598746663282333760843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30908263324435419556695581 11590598746663282333760843)
              ·
                refine ⟨17385898119994923500641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590598746663282333760843 17385898119994923500641265)
                ·
                  refine ⟨13039423589996192625480949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17385898119994923500641265 13039423589996192625480949)
                  ·
                    refine ⟨1222445961562143058638839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13039423589996192625480949 1222445961562143058638839)
                    ·
                      rfl

theorem cell23_7142115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 5].length) (baseStart_7142115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142115 prefixEnd_7142115 := by exact prefixLift 7142115
  have htrace : WordTrace (prefixWord ++ tailWord_7142115) baseStart_7142115 baseEnd_7142115 := by
    simpa [prefixWord, tailWord_7142115, baseEnd_7142115] using wordTrace_append hprefix tailTrace_7142115
  have hstable : (prefixWord ++ tailWord_7142115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142115).length < 2 ^ (prefixWord ++ tailWord_7142115).sum := by decide
  have hdescent : baseEnd_7142115 < baseStart_7142115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142128 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 5, 4]
def baseStart_7142128 : Nat := 118140960795 + 7142128 * 2 ^ 59
def prefixEnd_7142128 : Nat := 4983230072969 + 3 ^ 40 * 7142128 * 2
def baseEnd_7142128 : Nat := 1222448186644979208351319

theorem tailTrace_7142128 : CollatzResearch.WordTrace tailWord_7142128 prefixEnd_7142128 1222448186644979208351319 := by
  unfold tailWord_7142128
  simp only [CollatzResearch.WordTrace]
  refine ⟨130247404334648754597997519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173663205779531672797330025 130247404334648754597997519)
  ·
    refine ⟨195371106501973131896996279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130247404334648754597997519 195371106501973131896996279)
    ·
      refine ⟨293056659752959697845494419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195371106501973131896996279 293056659752959697845494419)
      ·
        refine ⟨439584989629439546768241629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293056659752959697845494419 439584989629439546768241629)
        ·
          refine ⟨164844371111039830038090611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439584989629439546768241629 164844371111039830038090611)
          ·
            refine ⟨247266556666559745057135917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164844371111039830038090611 247266556666559745057135917)
            ·
              refine ⟨92724958749959904396425969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247266556666559745057135917 92724958749959904396425969)
              ·
                refine ⟨69543719062469928297319477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92724958749959904396425969 69543719062469928297319477)
                ·
                  refine ⟨6519723662106555777873701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69543719062469928297319477 6519723662106555777873701)
                  ·
                    refine ⟨1222448186644979208351319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519723662106555777873701 1222448186644979208351319)
                    ·
                      rfl

theorem cell23_7142128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_7142128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142128 prefixEnd_7142128 := by exact prefixLift 7142128
  have htrace : WordTrace (prefixWord ++ tailWord_7142128) baseStart_7142128 baseEnd_7142128 := by
    simpa [prefixWord, tailWord_7142128, baseEnd_7142128] using wordTrace_append hprefix tailTrace_7142128
  have hstable : (prefixWord ++ tailWord_7142128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142128).length < 2 ^ (prefixWord ++ tailWord_7142128).sum := by decide
  have hdescent : baseEnd_7142128 < baseStart_7142128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142148 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7142148 : Nat := 118140960795 + 7142148 * 2 ^ 59
def prefixEnd_7142148 : Nat := 4983230072969 + 3 ^ 40 * 7142148 * 2
def baseEnd_7142148 : Nat := 3667354829548027546803865

theorem tailTrace_7142148 : CollatzResearch.WordTrace tailWord_7142148 prefixEnd_7142148 3667354829548027546803865 := by
  unfold tailWord_7142148
  simp only [CollatzResearch.WordTrace]
  refine ⟨130247769064612526305861549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173663692086150035074482065 130247769064612526305861549)
  ·
    refine ⟨48842913399229697364698081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130247769064612526305861549 48842913399229697364698081)
    ·
      refine ⟨36632185049422273023523561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48842913399229697364698081 36632185049422273023523561)
      ·
        refine ⟨27474138787066704767642671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36632185049422273023523561 27474138787066704767642671)
        ·
          refine ⟨41211208180600057151464007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27474138787066704767642671 41211208180600057151464007)
          ·
            refine ⟨61816812270900085727196011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41211208180600057151464007 61816812270900085727196011)
            ·
              refine ⟨92725218406350128590794017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61816812270900085727196011 92725218406350128590794017)
              ·
                refine ⟨69543913804762596443095513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92725218406350128590794017 69543913804762596443095513)
                ·
                  refine ⟨52157935353571947332321635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69543913804762596443095513 52157935353571947332321635)
                  ·
                    refine ⟨78236903030357920998482453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52157935353571947332321635 78236903030357920998482453)
                    ·
                      refine ⟨3667354829548027546803865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78236903030357920998482453 3667354829548027546803865)
                      ·
                        rfl

theorem cell23_7142148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7142148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142148 prefixEnd_7142148 := by exact prefixLift 7142148
  have htrace : WordTrace (prefixWord ++ tailWord_7142148) baseStart_7142148 baseEnd_7142148 := by
    simpa [prefixWord, tailWord_7142148, baseEnd_7142148] using wordTrace_append hprefix tailTrace_7142148
  have hstable : (prefixWord ++ tailWord_7142148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142148).length < 2 ^ (prefixWord ++ tailWord_7142148).sum := by decide
  have hdescent : baseEnd_7142148 < baseStart_7142148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142168 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7142168 : Nat := 118140960795 + 7142168 * 2 ^ 59
def prefixEnd_7142168 : Nat := 4983230072969 + 3 ^ 40 * 7142168 * 2
def baseEnd_7142168 : Nat := 3667365099161117468553773

theorem tailTrace_7142168 : CollatzResearch.WordTrace tailWord_7142168 prefixEnd_7142168 3667365099161117468553773 := by
  unfold tailWord_7142168
  simp only [CollatzResearch.WordTrace]
  refine ⟨130248133794576298013725579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173664178392768397351634105 130248133794576298013725579)
  ·
    refine ⟨195372200691864447020588369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130248133794576298013725579 195372200691864447020588369)
    ·
      refine ⟨146529150518898335265441277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195372200691864447020588369 146529150518898335265441277)
      ·
        refine ⟨54948431444586875724540479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146529150518898335265441277 54948431444586875724540479)
        ·
          refine ⟨82422647166880313586810719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54948431444586875724540479 82422647166880313586810719)
          ·
            refine ⟨123633970750320470380216079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82422647166880313586810719 123633970750320470380216079)
            ·
              refine ⟨185450956125480705570324119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123633970750320470380216079 185450956125480705570324119)
              ·
                refine ⟨278176434188221058355486179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185450956125480705570324119 278176434188221058355486179)
                ·
                  refine ⟨417264651282331587533229269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278176434188221058355486179 417264651282331587533229269)
                  ·
                    refine ⟨9779640264429646582810061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 417264651282331587533229269 9779640264429646582810061)
                    ·
                      refine ⟨3667365099161117468553773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9779640264429646582810061 3667365099161117468553773)
                      ·
                        rfl

theorem cell23_7142168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7142168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142168 prefixEnd_7142168 := by exact prefixLift 7142168
  have htrace : WordTrace (prefixWord ++ tailWord_7142168) baseStart_7142168 baseEnd_7142168 := by
    simpa [prefixWord, tailWord_7142168, baseEnd_7142168] using wordTrace_append hprefix tailTrace_7142168
  have hstable : (prefixWord ++ tailWord_7142168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142168).length < 2 ^ (prefixWord ++ tailWord_7142168).sum := by decide
  have hdescent : baseEnd_7142168 < baseStart_7142168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142196 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_7142196 : Nat := 118140960795 + 7142196 * 2 ^ 59
def prefixEnd_7142196 : Nat := 4983230072969 + 3 ^ 40 * 7142196 * 2
def baseEnd_7142196 : Nat := 1222459825539814453001215

theorem tailTrace_7142196 : CollatzResearch.WordTrace tailWord_7142196 prefixEnd_7142196 1222459825539814453001215 := by
  unfold tailWord_7142196
  simp only [CollatzResearch.WordTrace]
  refine ⟨130248644416525578404735221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173664859222034104539646961 130248644416525578404735221)
  ·
    refine ⟨12210810414049272975443927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130248644416525578404735221 12210810414049272975443927)
    ·
      refine ⟨18316215621073909463165891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12210810414049272975443927 18316215621073909463165891)
      ·
        refine ⟨27474323431610864194748837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18316215621073909463165891 27474323431610864194748837)
        ·
          refine ⟨5151435643427037036515407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27474323431610864194748837 5151435643427037036515407)
          ·
            refine ⟨7727153465140555554773111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151435643427037036515407 7727153465140555554773111)
            ·
              refine ⟨11590730197710833332159667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727153465140555554773111 11590730197710833332159667)
              ·
                refine ⟨17386095296566249998239501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590730197710833332159667 17386095296566249998239501)
                ·
                  refine ⟨6519785736212343749339813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17386095296566249998239501 6519785736212343749339813)
                  ·
                    refine ⟨1222459825539814453001215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519785736212343749339813 1222459825539814453001215)
                    ·
                      rfl

theorem cell23_7142196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_7142196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142196 prefixEnd_7142196 := by exact prefixLift 7142196
  have htrace : WordTrace (prefixWord ++ tailWord_7142196) baseStart_7142196 baseEnd_7142196 := by
    simpa [prefixWord, tailWord_7142196, baseEnd_7142196] using wordTrace_append hprefix tailTrace_7142196
  have hstable : (prefixWord ++ tailWord_7142196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142196).length < 2 ^ (prefixWord ++ tailWord_7142196).sum := by decide
  have hdescent : baseEnd_7142196 < baseStart_7142196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142245 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_7142245 : Nat := 118140960795 + 7142245 * 2 ^ 59
def prefixEnd_7142245 : Nat := 4983230072969 + 3 ^ 40 * 7142245 * 2
def baseEnd_7142245 : Nat := 3667404637171513667290919

theorem tailTrace_7142245 : CollatzResearch.WordTrace tailWord_7142245 prefixEnd_7142245 3667404637171513667290919 := by
  unfold tailWord_7142245
  simp only [CollatzResearch.WordTrace]
  refine ⟨260499076009873638178004189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173666050673249092118669459 260499076009873638178004189)
  ·
    refine ⟨97687153503702614316751571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260499076009873638178004189 97687153503702614316751571)
    ·
      refine ⟨146530730255553921475127357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97687153503702614316751571 146530730255553921475127357)
      ·
        refine ⟨54949023845832720553172759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146530730255553921475127357 54949023845832720553172759)
        ·
          refine ⟨82423535768749080829759139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54949023845832720553172759 82423535768749080829759139)
          ·
            refine ⟨123635303653123621244638709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82423535768749080829759139 123635303653123621244638709)
            ·
              refine ⟨11590809717480339491684879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123635303653123621244638709 11590809717480339491684879)
              ·
                refine ⟨17386214576220509237527319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590809717480339491684879 17386214576220509237527319)
                ·
                  refine ⟨26079321864330763856290979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17386214576220509237527319 26079321864330763856290979)
                  ·
                    refine ⟨39118982796496145784436469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26079321864330763856290979 39118982796496145784436469)
                    ·
                      refine ⟨3667404637171513667290919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39118982796496145784436469 3667404637171513667290919)
                      ·
                        rfl

theorem cell23_7142245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_7142245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142245 prefixEnd_7142245 := by exact prefixLift 7142245
  have htrace : WordTrace (prefixWord ++ tailWord_7142245) baseStart_7142245 baseEnd_7142245 := by
    simpa [prefixWord, tailWord_7142245, baseEnd_7142245] using wordTrace_append hprefix tailTrace_7142245
  have hstable : (prefixWord ++ tailWord_7142245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142245).length < 2 ^ (prefixWord ++ tailWord_7142245).sum := by decide
  have hdescent : baseEnd_7142245 < baseStart_7142245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142248 : List Nat := [2, 1, 4, 2, 1, 13]
def baseStart_7142248 : Nat := 118140960795 + 7142248 * 2 ^ 59
def prefixEnd_7142248 : Nat := 4983230072969 + 3 ^ 40 * 7142248 * 2
def baseEnd_7142248 : Nat := 15092206492236531504335

theorem tailTrace_7142248 : CollatzResearch.WordTrace tailWord_7142248 prefixEnd_7142248 15092206492236531504335 := by
  unfold tailWord_7142248
  simp only [CollatzResearch.WordTrace]
  refine ⟨130249592714431384845181699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173666123619241846460242265 130249592714431384845181699)
  ·
    refine ⟨195374389071647077267772549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130249592714431384845181699 195374389071647077267772549)
    ·
      refine ⟨36632697950933826987707353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195374389071647077267772549 36632697950933826987707353)
      ·
        refine ⟨27474523463200370240780515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36632697950933826987707353 27474523463200370240780515)
        ·
          refine ⟨41211785194800555361170773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27474523463200370240780515 41211785194800555361170773)
          ·
            refine ⟨15092206492236531504335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 41211785194800555361170773 15092206492236531504335)
            ·
              rfl

theorem cell23_7142248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 13].length) (baseStart_7142248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142248 prefixEnd_7142248 := by exact prefixLift 7142248
  have htrace : WordTrace (prefixWord ++ tailWord_7142248) baseStart_7142248 baseEnd_7142248 := by
    simpa [prefixWord, tailWord_7142248, baseEnd_7142248] using wordTrace_append hprefix tailTrace_7142248
  have hstable : (prefixWord ++ tailWord_7142248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142248).length < 2 ^ (prefixWord ++ tailWord_7142248).sum := by decide
  have hdescent : baseEnd_7142248 < baseStart_7142248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142252 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_7142252 : Nat := 118140960795 + 7142252 * 2 ^ 59
def prefixEnd_7142252 : Nat := 4983230072969 + 3 ^ 40 * 7142252 * 2
def baseEnd_7142252 : Nat := 1222469410512031713301129

theorem tailTrace_7142252 : CollatzResearch.WordTrace tailWord_7142252 prefixEnd_7142252 1222469410512031713301129 := by
  unfold tailWord_7142252
  simp only [CollatzResearch.WordTrace]
  refine ⟨130249665660424139186754505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173666220880565518915672673 130249665660424139186754505)
  ·
    refine ⟨97687249245318104390065879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130249665660424139186754505 97687249245318104390065879)
    ·
      refine ⟨146530873867977156585098819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97687249245318104390065879 146530873867977156585098819)
      ·
        refine ⟨219796310801965734877648229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146530873867977156585098819 219796310801965734877648229)
        ·
          refine ⟨41211808275368575289559043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219796310801965734877648229 41211808275368575289559043)
          ·
            refine ⟨61817712413052862934338565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41211808275368575289559043 61817712413052862934338565)
            ·
              refine ⟨11590821077447411800188481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61817712413052862934338565 11590821077447411800188481)
              ·
                refine ⟨8693115808085558850141361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11590821077447411800188481 8693115808085558850141361)
                ·
                  refine ⟨6519836856064169137606021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693115808085558850141361 6519836856064169137606021)
                  ·
                    refine ⟨1222469410512031713301129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519836856064169137606021 1222469410512031713301129)
                    ·
                      rfl

theorem cell23_7142252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_7142252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142252 prefixEnd_7142252 := by exact prefixLift 7142252
  have htrace : WordTrace (prefixWord ++ tailWord_7142252) baseStart_7142252 baseEnd_7142252 := by
    simpa [prefixWord, tailWord_7142252, baseEnd_7142252] using wordTrace_append hprefix tailTrace_7142252
  have hstable : (prefixWord ++ tailWord_7142252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142252).length < 2 ^ (prefixWord ++ tailWord_7142252).sum := by decide
  have hdescent : baseEnd_7142252 < baseStart_7142252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142265 : List Nat := [1, 2, 1, 3, 2, 5, 1, 8]
def baseStart_7142265 : Nat := 118140960795 + 7142265 * 2 ^ 59
def prefixEnd_7142265 : Nat := 4983230072969 + 3 ^ 40 * 7142265 * 2
def baseEnd_7142265 : Nat := 135830181732763095890401

theorem tailTrace_7142265 : CollatzResearch.WordTrace tailWord_7142265 prefixEnd_7142265 135830181732763095890401 := by
  unfold tailWord_7142265
  simp only [CollatzResearch.WordTrace]
  refine ⟨260499805469801181593732249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173666536979867454395821499 260499805469801181593732249)
  ·
    refine ⟨195374854102350886195299187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260499805469801181593732249 195374854102350886195299187)
    ·
      refine ⟨293062281153526329292948781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195374854102350886195299187 293062281153526329292948781)
      ·
        refine ⟨109898355432572373484855793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293062281153526329292948781 109898355432572373484855793)
        ·
          refine ⟨82423766574429280113641845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109898355432572373484855793 82423766574429280113641845)
          ·
            refine ⟨7727228116352745010653923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82423766574429280113641845 7727228116352745010653923)
            ·
              refine ⟨11590842174529117515980885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727228116352745010653923 11590842174529117515980885)
              ·
                refine ⟨135830181732763095890401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11590842174529117515980885 135830181732763095890401)
                ·
                  rfl

theorem cell23_7142265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 8].length) (baseStart_7142265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142265 prefixEnd_7142265 := by exact prefixLift 7142265
  have htrace : WordTrace (prefixWord ++ tailWord_7142265) baseStart_7142265 baseEnd_7142265 := by
    simpa [prefixWord, tailWord_7142265, baseEnd_7142265] using wordTrace_append hprefix tailTrace_7142265
  have hstable : (prefixWord ++ tailWord_7142265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142265).length < 2 ^ (prefixWord ++ tailWord_7142265).sum := by decide
  have hdescent : baseEnd_7142265 < baseStart_7142265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142268 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_7142268 : Nat := 118140960795 + 7142268 * 2 ^ 59
def prefixEnd_7142268 : Nat := 4983230072969 + 3 ^ 40 * 7142268 * 2
def baseEnd_7142268 : Nat := 3667416447226567077303313

theorem tailTrace_7142268 : CollatzResearch.WordTrace tailWord_7142268 prefixEnd_7142268 3667416447226567077303313 := by
  unfold tailWord_7142268
  simp only [CollatzResearch.WordTrace]
  refine ⟨130249957444395156553045729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173666609925860208737394305 130249957444395156553045729)
  ·
    refine ⟨97687468083296367414784297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130249957444395156553045729 97687468083296367414784297)
    ·
      refine ⟨73265601062472275561088223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97687468083296367414784297 73265601062472275561088223)
      ·
        refine ⟨109898401593708413341632335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73265601062472275561088223 109898401593708413341632335)
        ·
          refine ⟨164847602390562620012448503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109898401593708413341632335 164847602390562620012448503)
          ·
            refine ⟨247271403585843930018672755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164847602390562620012448503 247271403585843930018672755)
            ·
              refine ⟨370907105378765895028009133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247271403585843930018672755 370907105378765895028009133)
              ·
                refine ⟨139090164517037210635503425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370907105378765895028009133 139090164517037210635503425)
                ·
                  refine ⟨104317623387777907976627569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139090164517037210635503425 104317623387777907976627569)
                  ·
                    refine ⟨78238217540833430982470677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104317623387777907976627569 78238217540833430982470677)
                    ·
                      refine ⟨3667416447226567077303313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78238217540833430982470677 3667416447226567077303313)
                      ·
                        rfl

theorem cell23_7142268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_7142268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142268 prefixEnd_7142268 := by exact prefixLift 7142268
  have htrace : WordTrace (prefixWord ++ tailWord_7142268) baseStart_7142268 baseEnd_7142268 := by
    simpa [prefixWord, tailWord_7142268, baseEnd_7142268] using wordTrace_append hprefix tailTrace_7142268
  have hstable : (prefixWord ++ tailWord_7142268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142268).length < 2 ^ (prefixWord ++ tailWord_7142268).sum := by decide
  have hdescent : baseEnd_7142268 < baseStart_7142268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142282 : List Nat := [3, 1, 2, 4, 1, 2, 3, 7]
def baseStart_7142282 : Nat := 118140960795 + 7142282 * 2 ^ 59
def prefixEnd_7142282 : Nat := 4983230072969 + 3 ^ 40 * 7142282 * 2
def baseEnd_7142282 : Nat := 135830505035397408241787

theorem tailTrace_7142282 : CollatzResearch.WordTrace tailWord_7142282 prefixEnd_7142282 135830505035397408241787 := by
  unfold tailWord_7142282
  simp only [CollatzResearch.WordTrace]
  refine ⟨65125106377684898374275275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173666950340493062331400733 65125106377684898374275275)
  ·
    refine ⟨97687659566527347561412913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65125106377684898374275275 97687659566527347561412913)
    ·
      refine ⟨73265744674895510671059685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97687659566527347561412913 73265744674895510671059685)
      ·
        refine ⟨13737327126542908250823691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73265744674895510671059685 13737327126542908250823691)
        ·
          refine ⟨20605990689814362376235537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13737327126542908250823691 20605990689814362376235537)
          ·
            refine ⟨15454493017360771782176653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20605990689814362376235537 15454493017360771782176653)
            ·
              refine ⟨5795434881510289418316245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15454493017360771782176653 5795434881510289418316245)
              ·
                refine ⟨135830505035397408241787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5795434881510289418316245 135830505035397408241787)
                ·
                  rfl

theorem cell23_7142282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_7142282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142282 prefixEnd_7142282 := by exact prefixLift 7142282
  have htrace : WordTrace (prefixWord ++ tailWord_7142282) baseStart_7142282 baseEnd_7142282 := by
    simpa [prefixWord, tailWord_7142282, baseEnd_7142282] using wordTrace_append hprefix tailTrace_7142282
  have hstable : (prefixWord ++ tailWord_7142282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142282).length < 2 ^ (prefixWord ++ tailWord_7142282).sum := by decide
  have hdescent : baseEnd_7142282 < baseStart_7142282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142292 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_7142292 : Nat := 118140960795 + 7142292 * 2 ^ 59
def prefixEnd_7142292 : Nat := 4983230072969 + 3 ^ 40 * 7142292 * 2
def baseEnd_7142292 : Nat := 3667428770762274983403203

theorem tailTrace_7142292 : CollatzResearch.WordTrace tailWord_7142292 prefixEnd_7142292 3667428770762274983403203 := by
  unfold tailWord_7142292
  simp only [CollatzResearch.WordTrace]
  refine ⟨130250395120351682602482565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173667193493802243469976753 130250395120351682602482565)
  ·
    refine ⟨24421949085065940487965481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130250395120351682602482565 24421949085065940487965481)
    ·
      refine ⟨18316461813799455365974111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24421949085065940487965481 18316461813799455365974111)
      ·
        refine ⟨27474692720699183048961167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18316461813799455365974111 27474692720699183048961167)
        ·
          refine ⟨41212039081048774573441751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27474692720699183048961167 41212039081048774573441751)
          ·
            refine ⟨61818058621573161860162627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41212039081048774573441751 61818058621573161860162627)
            ·
              refine ⟨92727087932359742790243941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61818058621573161860162627 92727087932359742790243941)
              ·
                refine ⟨17386328987317451773170739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92727087932359742790243941 17386328987317451773170739)
                ·
                  refine ⟨26079493480976177659756109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17386328987317451773170739 26079493480976177659756109)
                  ·
                    refine ⟨9779810055366066622408541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26079493480976177659756109 9779810055366066622408541)
                    ·
                      refine ⟨3667428770762274983403203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9779810055366066622408541 3667428770762274983403203)
                      ·
                        rfl

theorem cell23_7142292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_7142292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142292 prefixEnd_7142292 := by exact prefixLift 7142292
  have htrace : WordTrace (prefixWord ++ tailWord_7142292) baseStart_7142292 baseEnd_7142292 := by
    simpa [prefixWord, tailWord_7142292, baseEnd_7142292] using wordTrace_append hprefix tailTrace_7142292
  have hstable : (prefixWord ++ tailWord_7142292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142292).length < 2 ^ (prefixWord ++ tailWord_7142292).sum := by decide
  have hdescent : baseEnd_7142292 < baseStart_7142292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142325 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_7142325 : Nat := 118140960795 + 7142325 * 2 ^ 59
def prefixEnd_7142325 : Nat := 4983230072969 + 3 ^ 40 * 7142325 * 2
def baseEnd_7142325 : Nat := 1222481905207957784763517

theorem tailTrace_7142325 : CollatzResearch.WordTrace tailWord_7142325 prefixEnd_7142325 1222481905207957784763517 := by
  unfold tailWord_7142325
  simp only [CollatzResearch.WordTrace]
  refine ⟨260501993849583811840916429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173667995899722541227277619 260501993849583811840916429)
  ·
    refine ⟨97688247693593929440343661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260501993849583811840916429 97688247693593929440343661)
    ·
      refine ⟨36633092885097723540128873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97688247693593929440343661 36633092885097723540128873)
      ·
        refine ⟨27474819663823292655096655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36633092885097723540128873 27474819663823292655096655)
        ·
          refine ⟨41212229495734938982644983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27474819663823292655096655 41212229495734938982644983)
          ·
            refine ⟨61818344243602408473967475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41212229495734938982644983 61818344243602408473967475)
            ·
              refine ⟨92727516365403612710951213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61818344243602408473967475 92727516365403612710951213)
              ·
                refine ⟨34772818637026354766606705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92727516365403612710951213 34772818637026354766606705)
                ·
                  refine ⟨26079613977769766074955029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34772818637026354766606705 26079613977769766074955029)
                  ·
                    refine ⟨1222481905207957784763517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26079613977769766074955029 1222481905207957784763517)
                    ·
                      rfl

theorem cell23_7142325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_7142325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142325 prefixEnd_7142325 := by exact prefixLift 7142325
  have htrace : WordTrace (prefixWord ++ tailWord_7142325) baseStart_7142325 baseEnd_7142325 := by
    simpa [prefixWord, tailWord_7142325, baseEnd_7142325] using wordTrace_append hprefix tailTrace_7142325
  have hstable : (prefixWord ++ tailWord_7142325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142325).length < 2 ^ (prefixWord ++ tailWord_7142325).sum := by decide
  have hdescent : baseEnd_7142325 < baseStart_7142325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142383 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 2, 2, 2]
def baseStart_7142383 : Nat := 118140960795 + 7142383 * 2 ^ 59
def prefixEnd_7142383 : Nat := 4983230072969 + 3 ^ 40 * 7142383 * 2
def baseEnd_7142383 : Nat := 3667475497501834127365285

theorem tailTrace_7142383 : CollatzResearch.WordTrace tailWord_7142383 prefixEnd_7142383 3667475497501834127365285 := by
  unfold tailWord_7142383
  simp only [CollatzResearch.WordTrace]
  refine ⟨260504109283373687746527803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173669406188915791831018535 260504109283373687746527803)
  ·
    refine ⟨390756163925060531619791705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260504109283373687746527803 390756163925060531619791705)
    ·
      refine ⟨293067122943795398714843779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390756163925060531619791705 293067122943795398714843779)
      ·
        refine ⟨439600684415693098072265669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293067122943795398714843779 439600684415693098072265669)
        ·
          refine ⟨82425128327942455888549813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439600684415693098072265669 82425128327942455888549813)
          ·
            refine ⟨7727355780744605239551545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82425128327942455888549813 7727355780744605239551545)
            ·
              refine ⟨5795516835558453929663659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7727355780744605239551545 5795516835558453929663659)
              ·
                refine ⟨8693275253337680894495489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5795516835558453929663659 8693275253337680894495489)
                ·
                  refine ⟨6519956440003260670871617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693275253337680894495489 6519956440003260670871617)
                  ·
                    refine ⟨4889967330002445503153713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6519956440003260670871617 4889967330002445503153713)
                    ·
                      refine ⟨3667475497501834127365285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4889967330002445503153713 3667475497501834127365285)
                      ·
                        rfl

theorem cell23_7142383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 2, 2].length) (baseStart_7142383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142383 prefixEnd_7142383 := by exact prefixLift 7142383
  have htrace : WordTrace (prefixWord ++ tailWord_7142383) baseStart_7142383 baseEnd_7142383 := by
    simpa [prefixWord, tailWord_7142383, baseEnd_7142383] using wordTrace_append hprefix tailTrace_7142383
  have hstable : (prefixWord ++ tailWord_7142383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142383).length < 2 ^ (prefixWord ++ tailWord_7142383).sum := by decide
  have hdescent : baseEnd_7142383 < baseStart_7142383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142482 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_7142482 : Nat := 118140960795 + 7142482 * 2 ^ 59
def prefixEnd_7142482 : Nat := 4983230072969 + 3 ^ 40 * 7142482 * 2
def baseEnd_7142482 : Nat := 3667526332086629240027329

theorem tailTrace_7142482 : CollatzResearch.WordTrace tailWord_7142482 prefixEnd_7142482 3667526332086629240027329 := by
  unfold tailWord_7142482
  simp only [CollatzResearch.WordTrace]
  refine ⟨65126930027503756913595425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173671813406676685102921133 65126930027503756913595425)
  ·
    refine ⟨48845197520627817685196569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65126930027503756913595425 48845197520627817685196569)
    ·
      refine ⟨36633898140470863263897427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48845197520627817685196569 36633898140470863263897427)
      ·
        refine ⟨54950847210706294895846141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36633898140470863263897427 54950847210706294895846141)
        ·
          refine ⟨20606567704014860585942303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54950847210706294895846141 20606567704014860585942303)
          ·
            refine ⟨30909851556022290878913455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20606567704014860585942303 30909851556022290878913455)
            ·
              refine ⟨46364777334033436318370183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30909851556022290878913455 46364777334033436318370183)
              ·
                refine ⟨69547166001050154477555275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46364777334033436318370183 69547166001050154477555275)
                ·
                  refine ⟨104320749001575231716332913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69547166001050154477555275 104320749001575231716332913)
                  ·
                    refine ⟨78240561751181423787249685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104320749001575231716332913 78240561751181423787249685)
                    ·
                      refine ⟨3667526332086629240027329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78240561751181423787249685 3667526332086629240027329)
                      ·
                        rfl

theorem cell23_7142482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_7142482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142482 prefixEnd_7142482 := by exact prefixLift 7142482
  have htrace : WordTrace (prefixWord ++ tailWord_7142482) baseStart_7142482 baseEnd_7142482 := by
    simpa [prefixWord, tailWord_7142482, baseEnd_7142482] using wordTrace_append hprefix tailTrace_7142482
  have hstable : (prefixWord ++ tailWord_7142482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142482).length < 2 ^ (prefixWord ++ tailWord_7142482).sum := by decide
  have hdescent : baseEnd_7142482 < baseStart_7142482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142506 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7142506 : Nat := 118140960795 + 7142506 * 2 ^ 59
def prefixEnd_7142506 : Nat := 4983230072969 + 3 ^ 40 * 7142506 * 2
def baseEnd_7142506 : Nat := 3667538655622337146127219

theorem tailTrace_7142506 : CollatzResearch.WordTrace tailWord_7142506 prefixEnd_7142506 3667538655622337146127219 := by
  unfold tailWord_7142506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65127148865482019938313843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173672396974618719835503581 65127148865482019938313843)
  ·
    refine ⟨97690723298223029907470765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65127148865482019938313843 97690723298223029907470765)
    ·
      refine ⟨36634021236833636215301537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97690723298223029907470765 36634021236833636215301537)
      ·
        refine ⟨27475515927625227161476153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36634021236833636215301537 27475515927625227161476153)
        ·
          refine ⟨20606636945718920371107115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27475515927625227161476153 20606636945718920371107115)
          ·
            refine ⟨30909955418578380556660673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20606636945718920371107115 30909955418578380556660673)
            ·
              refine ⟨23182466563933785417495505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30909955418578380556660673 23182466563933785417495505)
              ·
                refine ⟨17386849922950339063121629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23182466563933785417495505 17386849922950339063121629)
                ·
                  refine ⟨6520068721106377148670611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17386849922950339063121629 6520068721106377148670611)
                  ·
                    refine ⟨9780103081659565723005917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6520068721106377148670611 9780103081659565723005917)
                    ·
                      refine ⟨3667538655622337146127219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780103081659565723005917 3667538655622337146127219)
                      ·
                        rfl

theorem cell23_7142506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7142506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142506 prefixEnd_7142506 := by exact prefixLift 7142506
  have htrace : WordTrace (prefixWord ++ tailWord_7142506) baseStart_7142506 baseEnd_7142506 := by
    simpa [prefixWord, tailWord_7142506, baseEnd_7142506] using wordTrace_append hprefix tailTrace_7142506
  have hstable : (prefixWord ++ tailWord_7142506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142506).length < 2 ^ (prefixWord ++ tailWord_7142506).sum := by decide
  have hdescent : baseEnd_7142506 < baseStart_7142506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142509 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_7142509 : Nat := 118140960795 + 7142509 * 2 ^ 59
def prefixEnd_7142509 : Nat := 4983230072969 + 3 ^ 40 * 7142509 * 2
def baseEnd_7142509 : Nat := 1222513398688100211463235

theorem tailTrace_7142509 : CollatzResearch.WordTrace tailWord_7142509 prefixEnd_7142509 1222513398688100211463235 := by
  unfold tailWord_7142509
  simp only [CollatzResearch.WordTrace]
  refine ⟨260508704880917211265614581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173672469920611474177076387 260508704880917211265614581)
  ·
    refine ⟨24422691082585988556151367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260508704880917211265614581 24422691082585988556151367)
    ·
      refine ⟨36634036623878982834227051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24422691082585988556151367 36634036623878982834227051)
      ·
        refine ⟨54951054935818474251340577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36634036623878982834227051 54951054935818474251340577)
        ·
          refine ⟨41213291201863855688505433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54951054935818474251340577 41213291201863855688505433)
          ·
            refine ⟨30909968401397891766379075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41213291201863855688505433 30909968401397891766379075)
            ·
              refine ⟨46364952602096837649568613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30909968401397891766379075 46364952602096837649568613)
              ·
                refine ⟨8693428612893157059294115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46364952602096837649568613 8693428612893157059294115)
                ·
                  refine ⟨13040142919339735588941173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693428612893157059294115 13040142919339735588941173)
                  ·
                    refine ⟨1222513398688100211463235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13040142919339735588941173 1222513398688100211463235)
                    ·
                      rfl

theorem cell23_7142509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_7142509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142509 prefixEnd_7142509 := by exact prefixLift 7142509
  have htrace : WordTrace (prefixWord ++ tailWord_7142509) baseStart_7142509 baseEnd_7142509 := by
    simpa [prefixWord, tailWord_7142509, baseEnd_7142509] using wordTrace_append hprefix tailTrace_7142509
  have hstable : (prefixWord ++ tailWord_7142509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142509).length < 2 ^ (prefixWord ++ tailWord_7142509).sum := by decide
  have hdescent : baseEnd_7142509 < baseStart_7142509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142517 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_7142517 : Nat := 118140960795 + 7142517 * 2 ^ 59
def prefixEnd_7142517 : Nat := 4983230072969 + 3 ^ 40 * 7142517 * 2
def baseEnd_7142517 : Nat := 1222514767969845534363223

theorem tailTrace_7142517 : CollatzResearch.WordTrace tailWord_7142517 prefixEnd_7142517 1222514767969845534363223 := by
  unfold tailWord_7142517
  simp only [CollatzResearch.WordTrace]
  refine ⟨260508996664888228631905805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173672664443258819087937203 260508996664888228631905805)
  ·
    refine ⟨97690873749333085736964677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260508996664888228631905805 97690873749333085736964677)
    ·
      refine ⟨18317038827999953575680877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97690873749333085736964677 18317038827999953575680877)
      ·
        refine ⟨6868889560499982590880329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18317038827999953575680877 6868889560499982590880329)
        ·
          refine ⟨5151667170374986943160247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6868889560499982590880329 5151667170374986943160247)
          ·
            refine ⟨7727500755562480414740371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151667170374986943160247 7727500755562480414740371)
            ·
              refine ⟨11591251133343720622110557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727500755562480414740371 11591251133343720622110557)
              ·
                refine ⟨4346719175003895233291459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11591251133343720622110557 4346719175003895233291459)
                ·
                  refine ⟨6520078762505842849937189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346719175003895233291459 6520078762505842849937189)
                  ·
                    refine ⟨1222514767969845534363223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6520078762505842849937189 1222514767969845534363223)
                    ·
                      rfl

theorem cell23_7142517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_7142517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142517 prefixEnd_7142517 := by exact prefixLift 7142517
  have htrace : WordTrace (prefixWord ++ tailWord_7142517) baseStart_7142517 baseEnd_7142517 := by
    simpa [prefixWord, tailWord_7142517, baseEnd_7142517] using wordTrace_append hprefix tailTrace_7142517
  have hstable : (prefixWord ++ tailWord_7142517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142517).length < 2 ^ (prefixWord ++ tailWord_7142517).sum := by decide
  have hdescent : baseEnd_7142517 < baseStart_7142517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142552 : List Nat := [2, 1, 2, 4, 2, 1, 1, 10]
def baseStart_7142552 : Nat := 118140960795 + 7142552 * 2 ^ 59
def prefixEnd_7142552 : Nat := 4983230072969 + 3 ^ 40 * 7142552 * 2
def baseEnd_7142552 : Nat := 135835639841942369116741

theorem tailTrace_7142552 : CollatzResearch.WordTrace tailWord_7142552 prefixEnd_7142552 135835639841942369116741 := by
  unfold tailWord_7142552
  simp only [CollatzResearch.WordTrace]
  refine ⟨130255136609880714804714955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173673515479840953072953273 130255136609880714804714955)
  ·
    refine ⟨195382704914821072207072433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130255136609880714804714955 195382704914821072207072433)
    ·
      refine ⟨146537028686115804155304325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195382704914821072207072433 146537028686115804155304325)
      ·
        refine ⟨27475692878646713279119561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146537028686115804155304325 27475692878646713279119561)
        ·
          refine ⟨20606769658985034959339671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27475692878646713279119561 20606769658985034959339671)
          ·
            refine ⟨30910154488477552439009507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20606769658985034959339671 30910154488477552439009507)
            ·
              refine ⟨46365231732716328658514261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30910154488477552439009507 46365231732716328658514261)
              ·
                refine ⟨135835639841942369116741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46365231732716328658514261 135835639841942369116741)
                ·
                  rfl

theorem cell23_7142552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 10].length) (baseStart_7142552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142552 prefixEnd_7142552 := by exact prefixLift 7142552
  have htrace : WordTrace (prefixWord ++ tailWord_7142552) baseStart_7142552 baseEnd_7142552 := by
    simpa [prefixWord, tailWord_7142552, baseEnd_7142552] using wordTrace_append hprefix tailTrace_7142552
  have hstable : (prefixWord ++ tailWord_7142552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142552).length < 2 ^ (prefixWord ++ tailWord_7142552).sum := by decide
  have hdescent : baseEnd_7142552 < baseStart_7142552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142556 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_7142556 : Nat := 118140960795 + 7142556 * 2 ^ 59
def prefixEnd_7142556 : Nat := 4983230072969 + 3 ^ 40 * 7142556 * 2
def baseEnd_7142556 : Nat := 1222521443218353983500663

theorem tailTrace_7142556 : CollatzResearch.WordTrace tailWord_7142556 prefixEnd_7142556 1222521443218353983500663 := by
  unfold tailWord_7142556
  simp only [CollatzResearch.WordTrace]
  refine ⟨130255209555873469146287761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173673612741164625528383681 130255209555873469146287761)
  ·
    refine ⟨97691407166905101859715821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130255209555873469146287761 97691407166905101859715821)
    ·
      refine ⟨36634277687589413197393433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97691407166905101859715821 36634277687589413197393433)
      ·
        refine ⟨27475708265692059898045075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36634277687589413197393433 27475708265692059898045075)
        ·
          refine ⟨41213562398538089847067613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27475708265692059898045075 41213562398538089847067613)
          ·
            refine ⟨15455085899451783692650355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41213562398538089847067613 15455085899451783692650355)
            ·
              refine ⟨23182628849177675538975533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15455085899451783692650355 23182628849177675538975533)
              ·
                refine ⟨8693485818441628327115825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23182628849177675538975533 8693485818441628327115825)
                ·
                  refine ⟨6520114363831221245336869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693485818441628327115825 6520114363831221245336869)
                  ·
                    refine ⟨1222521443218353983500663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6520114363831221245336869 1222521443218353983500663)
                    ·
                      rfl

theorem cell23_7142556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_7142556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142556 prefixEnd_7142556 := by exact prefixLift 7142556
  have htrace : WordTrace (prefixWord ++ tailWord_7142556) baseStart_7142556 baseEnd_7142556 := by
    simpa [prefixWord, tailWord_7142556, baseEnd_7142556] using wordTrace_append hprefix tailTrace_7142556
  have hstable : (prefixWord ++ tailWord_7142556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142556).length < 2 ^ (prefixWord ++ tailWord_7142556).sum := by decide
  have hdescent : baseEnd_7142556 < baseStart_7142556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142579 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 3]
def baseStart_7142579 : Nat := 118140960795 + 7142579 * 2 ^ 59
def prefixEnd_7142579 : Nat := 4983230072969 + 3 ^ 40 * 7142579 * 2
def baseEnd_7142579 : Nat := 3667576139710115360514383

theorem tailTrace_7142579 : CollatzResearch.WordTrace tailWord_7142579 prefixEnd_7142579 3667576139710115360514383 := by
  unfold tailWord_7142579
  simp only [CollatzResearch.WordTrace]
  refine ⟨260511257990663613220662791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173674171993775742147108527 260511257990663613220662791)
  ·
    refine ⟨390766886985995419830994187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260511257990663613220662791 390766886985995419830994187)
    ·
      refine ⟨586150330478993129746491281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390766886985995419830994187 586150330478993129746491281)
      ·
        refine ⟨439612747859244847309868461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586150330478993129746491281 439612747859244847309868461)
        ·
          refine ⟨164854780447216817741200673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439612747859244847309868461 164854780447216817741200673)
          ·
            refine ⟨123641085335412613305900505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164854780447216817741200673 123641085335412613305900505)
            ·
              refine ⟨92730814001559459979425379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123641085335412613305900505 92730814001559459979425379)
              ·
                refine ⟨139096221002339189969138069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92730814001559459979425379 139096221002339189969138069)
                ·
                  refine ⟨6520135359484649529803347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139096221002339189969138069 6520135359484649529803347)
                  ·
                    refine ⟨9780203039226974294705021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6520135359484649529803347 9780203039226974294705021)
                    ·
                      refine ⟨3667576139710115360514383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780203039226974294705021 3667576139710115360514383)
                      ·
                        rfl

theorem cell23_7142579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_7142579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142579 prefixEnd_7142579 := by exact prefixLift 7142579
  have htrace : WordTrace (prefixWord ++ tailWord_7142579) baseStart_7142579 baseEnd_7142579 := by
    simpa [prefixWord, tailWord_7142579, baseEnd_7142579] using wordTrace_append hprefix tailTrace_7142579
  have hstable : (prefixWord ++ tailWord_7142579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142579).length < 2 ^ (prefixWord ++ tailWord_7142579).sum := by decide
  have hdescent : baseEnd_7142579 < baseStart_7142579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142613 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7142613 : Nat := 118140960795 + 7142613 * 2 ^ 59
def prefixEnd_7142613 : Nat := 4983230072969 + 3 ^ 40 * 7142613 * 2
def baseEnd_7142613 : Nat := 3667593598052368227489227

theorem tailTrace_7142613 : CollatzResearch.WordTrace tailWord_7142613 prefixEnd_7142613 3667593598052368227489227 := by
  unfold tailWord_7142613
  simp only [CollatzResearch.WordTrace]
  refine ⟨260512498072540437027400493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173674998715026958018266995 260512498072540437027400493)
  ·
    refine ⟨97692186777202663885275185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260512498072540437027400493 97692186777202663885275185)
    ·
      refine ⟨73269140082901997913956389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97692186777202663885275185 73269140082901997913956389)
      ·
        refine ⟨13737963765544124608866823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73269140082901997913956389 13737963765544124608866823)
        ·
          refine ⟨20606945648316186913300235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13737963765544124608866823 20606945648316186913300235)
          ·
            refine ⟨30910418472474280369950353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20606945648316186913300235 30910418472474280369950353)
            ·
              refine ⟨23182813854355710277462765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30910418472474280369950353 23182813854355710277462765)
              ·
                refine ⟨8693555195383391354048537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23182813854355710277462765 8693555195383391354048537)
                ·
                  refine ⟨6520166396537543515536403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693555195383391354048537 6520166396537543515536403)
                  ·
                    refine ⟨9780249594806315273304605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6520166396537543515536403 9780249594806315273304605)
                    ·
                      refine ⟨3667593598052368227489227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780249594806315273304605 3667593598052368227489227)
                      ·
                        rfl

theorem cell23_7142613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7142613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142613 prefixEnd_7142613 := by exact prefixLift 7142613
  have htrace : WordTrace (prefixWord ++ tailWord_7142613) baseStart_7142613 baseEnd_7142613 := by
    simpa [prefixWord, tailWord_7142613, baseEnd_7142613] using wordTrace_append hprefix tailTrace_7142613
  have hstable : (prefixWord ++ tailWord_7142613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142613).length < 2 ^ (prefixWord ++ tailWord_7142613).sum := by decide
  have hdescent : baseEnd_7142613 < baseStart_7142613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142636 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 1, 4, 2]
def baseStart_7142636 : Nat := 118140960795 + 7142636 * 2 ^ 59
def prefixEnd_7142636 : Nat := 4983230072969 + 3 ^ 40 * 7142636 * 2
def baseEnd_7142636 : Nat := 3667605408107421637501621

theorem tailTrace_7142636 : CollatzResearch.WordTrace tailWord_7142636 prefixEnd_7142636 3667605408107421637501621 := by
  unfold tailWord_7142636
  simp only [CollatzResearch.WordTrace]
  refine ⟨130256668475728555977743881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173675557967638074636991841 130256668475728555977743881)
  ·
    refine ⟨97692501356796416983307911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130256668475728555977743881 97692501356796416983307911)
    ·
      refine ⟨146538752035194625474961867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97692501356796416983307911 146538752035194625474961867)
      ·
        refine ⟨219808128052791938212442801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146538752035194625474961867 219808128052791938212442801)
        ·
          refine ⟨164856096039593953659332101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219808128052791938212442801 164856096039593953659332101)
          ·
            refine ⟨30910518007423866311124769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164856096039593953659332101 30910518007423866311124769)
            ·
              refine ⟨23182888505567899733343577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30910518007423866311124769 23182888505567899733343577)
              ·
                refine ⟨17387166379175924800007683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23182888505567899733343577 17387166379175924800007683)
                ·
                  refine ⟨26080749568763887200011525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17387166379175924800007683 26080749568763887200011525)
                  ·
                    refine ⟨4890140544143228850002161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26080749568763887200011525 4890140544143228850002161)
                    ·
                      refine ⟨3667605408107421637501621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4890140544143228850002161 3667605408107421637501621)
                      ·
                        rfl

theorem cell23_7142636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_7142636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142636 prefixEnd_7142636 := by exact prefixLift 7142636
  have htrace : WordTrace (prefixWord ++ tailWord_7142636) baseStart_7142636 baseEnd_7142636 := by
    simpa [prefixWord, tailWord_7142636, baseEnd_7142636] using wordTrace_append hprefix tailTrace_7142636
  have hstable : (prefixWord ++ tailWord_7142636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142636).length < 2 ^ (prefixWord ++ tailWord_7142636).sum := by decide
  have hdescent : baseEnd_7142636 < baseStart_7142636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142659 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 7]
def baseStart_7142659 : Nat := 118140960795 + 7142659 * 2 ^ 59
def prefixEnd_7142659 : Nat := 4983230072969 + 3 ^ 40 * 7142659 * 2
def baseEnd_7142659 : Nat := 407513024240275005279335

theorem tailTrace_7142659 : CollatzResearch.WordTrace tailWord_7142659 prefixEnd_7142659 407513024240275005279335 := by
  unfold tailWord_7142659
  simp only [CollatzResearch.WordTrace]
  refine ⟨260514175830373786883575031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173676117220249191255716687 260514175830373786883575031)
  ·
    refine ⟨390771263745560680325362547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260514175830373786883575031 390771263745560680325362547)
    ·
      refine ⟨586156895618341020488043821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390771263745560680325362547 586156895618341020488043821)
      ·
        refine ⟨219808835856877882683016433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586156895618341020488043821 219808835856877882683016433)
        ·
          refine ⟨164856626892658412012262325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219808835856877882683016433 164856626892658412012262325)
          ·
            refine ⟨15455308771186726126149593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164856626892658412012262325 15455308771186726126149593)
            ·
              refine ⟨11591481578390044594612195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15455308771186726126149593 11591481578390044594612195)
              ·
                refine ⟨17387222367585066891918293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591481578390044594612195 17387222367585066891918293)
                ·
                  refine ⟨407513024240275005279335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17387222367585066891918293 407513024240275005279335)
                  ·
                    rfl

theorem cell23_7142659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 7].length) (baseStart_7142659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142659 prefixEnd_7142659 := by exact prefixLift 7142659
  have htrace : WordTrace (prefixWord ++ tailWord_7142659) baseStart_7142659 baseEnd_7142659 := by
    simpa [prefixWord, tailWord_7142659, baseEnd_7142659] using wordTrace_append hprefix tailTrace_7142659
  have hstable : (prefixWord ++ tailWord_7142659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142659).length < 2 ^ (prefixWord ++ tailWord_7142659).sum := by decide
  have hdescent : baseEnd_7142659 < baseStart_7142659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142689 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_7142689 : Nat := 118140960795 + 7142689 * 2 ^ 59
def prefixEnd_7142689 : Nat := 4983230072969 + 3 ^ 40 * 7142689 * 2
def baseEnd_7142689 : Nat := 1222544207527369976712959

theorem tailTrace_7142689 : CollatzResearch.WordTrace tailWord_7142689 prefixEnd_7142689 1222544207527369976712959 := by
  unfold tailWord_7142689
  simp only [CollatzResearch.WordTrace]
  refine ⟨260515270020265102007167121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173676846680176734671444747 260515270020265102007167121)
  ·
    refine ⟨195386452515198826505375341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260515270020265102007167121 195386452515198826505375341)
    ·
      refine ⟨73269919693199559939515753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195386452515198826505375341 73269919693199559939515753)
      ·
        refine ⟨54952439769899669954636815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73269919693199559939515753 54952439769899669954636815)
        ·
          refine ⟨82428659654849504931955223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54952439769899669954636815 82428659654849504931955223)
          ·
            refine ⟨123642989482274257397932835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82428659654849504931955223 123642989482274257397932835)
            ·
              refine ⟨185464484223411386096899253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123642989482274257397932835 185464484223411386096899253)
              ·
                refine ⟨17387295395944817446584305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185464484223411386096899253 17387295395944817446584305)
                ·
                  refine ⟨13040471546958613084938229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17387295395944817446584305 13040471546958613084938229)
                  ·
                    refine ⟨1222544207527369976712959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13040471546958613084938229 1222544207527369976712959)
                    ·
                      rfl

theorem cell23_7142689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_7142689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142689 prefixEnd_7142689 := by exact prefixLift 7142689
  have htrace : WordTrace (prefixWord ++ tailWord_7142689) baseStart_7142689 baseEnd_7142689 := by
    simpa [prefixWord, tailWord_7142689, baseEnd_7142689] using wordTrace_append hprefix tailTrace_7142689
  have hstable : (prefixWord ++ tailWord_7142689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142689).length < 2 ^ (prefixWord ++ tailWord_7142689).sum := by decide
  have hdescent : baseEnd_7142689 < baseStart_7142689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142693 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 5]
def baseStart_7142693 : Nat := 118140960795 + 7142693 * 2 ^ 59
def prefixEnd_7142693 : Nat := 4983230072969 + 3 ^ 40 * 7142693 * 2
def baseEnd_7142693 : Nat := 407514964056080879387651

theorem tailTrace_7142693 : CollatzResearch.WordTrace tailWord_7142693 prefixEnd_7142693 407514964056080879387651 := by
  unfold tailWord_7142693
  simp only [CollatzResearch.WordTrace]
  refine ⟨260515415912250610690312733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173676943941500407126875155 260515415912250610690312733)
  ·
    refine ⟨97693280967093979008867275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260515415912250610690312733 97693280967093979008867275)
    ·
      refine ⟨146539921450640968513300913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97693280967093979008867275 146539921450640968513300913)
      ·
        refine ⟨109904941087980726384975685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146539921450640968513300913 109904941087980726384975685)
        ·
          refine ⟨20607176453996386197182941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109904941087980726384975685 20607176453996386197182941)
          ·
            refine ⟨7727691170248644823943603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20607176453996386197182941 7727691170248644823943603)
            ·
              refine ⟨11591536755372967235915405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727691170248644823943603 11591536755372967235915405)
              ·
                refine ⟨4346826283264862713468277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11591536755372967235915405 4346826283264862713468277)
                ·
                  refine ⟨407514964056080879387651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4346826283264862713468277 407514964056080879387651)
                  ·
                    rfl

theorem cell23_7142693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_7142693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142693 prefixEnd_7142693 := by exact prefixLift 7142693
  have htrace : WordTrace (prefixWord ++ tailWord_7142693) baseStart_7142693 baseEnd_7142693 := by
    simpa [prefixWord, tailWord_7142693, baseEnd_7142693] using wordTrace_append hprefix tailTrace_7142693
  have hstable : (prefixWord ++ tailWord_7142693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142693).length < 2 ^ (prefixWord ++ tailWord_7142693).sum := by decide
  have hdescent : baseEnd_7142693 < baseStart_7142693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142706 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_7142706 : Nat := 118140960795 + 7142706 * 2 ^ 59
def prefixEnd_7142706 : Nat := 4983230072969 + 3 ^ 40 * 7142706 * 2
def baseEnd_7142706 : Nat := 1222547117251078787875433

theorem tailTrace_7142706 : CollatzResearch.WordTrace tailWord_7142706 prefixEnd_7142706 1222547117251078787875433 := by
  unfold tailWord_7142706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65128972515300878477633993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173677260040802342607023981 65128972515300878477633993)
  ·
    refine ⟨48846729386475658858225495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65128972515300878477633993 48846729386475658858225495)
    ·
      refine ⟨73270094079713488287338243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48846729386475658858225495 73270094079713488287338243)
      ·
        refine ⟨109905141119570232431007365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73270094079713488287338243 109905141119570232431007365)
        ·
          refine ⟨20607213959919418580813881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109905141119570232431007365 20607213959919418580813881)
          ·
            refine ⟨15455410469939563935610411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20607213959919418580813881 15455410469939563935610411)
            ·
              refine ⟨23183115704909345903415617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15455410469939563935610411 23183115704909345903415617)
              ·
                refine ⟨17387336778682009427561713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23183115704909345903415617 17387336778682009427561713)
                ·
                  refine ⟨13040502584011507070671285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17387336778682009427561713 13040502584011507070671285)
                  ·
                    refine ⟨1222547117251078787875433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13040502584011507070671285 1222547117251078787875433)
                    ·
                      rfl

theorem cell23_7142706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_7142706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142706 prefixEnd_7142706 := by exact prefixLift 7142706
  have htrace : WordTrace (prefixWord ++ tailWord_7142706) baseStart_7142706 baseEnd_7142706 := by
    simpa [prefixWord, tailWord_7142706, baseEnd_7142706] using wordTrace_append hprefix tailTrace_7142706
  have hstable : (prefixWord ++ tailWord_7142706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142706).length < 2 ^ (prefixWord ++ tailWord_7142706).sum := by decide
  have hdescent : baseEnd_7142706 < baseStart_7142706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142710 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_7142710 : Nat := 118140960795 + 7142710 * 2 ^ 59
def prefixEnd_7142710 : Nat := 4983230072969 + 3 ^ 40 * 7142710 * 2
def baseEnd_7142710 : Nat := 407515933963983816441809

theorem tailTrace_7142710 : CollatzResearch.WordTrace tailWord_7142710 prefixEnd_7142710 407515933963983816441809 := by
  unfold tailWord_7142710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282252247074313912105099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173677357302126015062454389 16282252247074313912105099)
  ·
    refine ⟨24423378370611470868157649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282252247074313912105099 24423378370611470868157649)
    ·
      refine ⟨18317533777958603151118237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24423378370611470868157649 18317533777958603151118237)
      ·
        refine ⟨6869075166734476181669339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18317533777958603151118237 6869075166734476181669339)
        ·
          refine ⟨10303612750101714272504009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869075166734476181669339 10303612750101714272504009)
          ·
            refine ⟨7727709562576285704378007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10303612750101714272504009 7727709562576285704378007)
            ·
              refine ⟨11591564343864428556567011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727709562576285704378007 11591564343864428556567011)
              ·
                refine ⟨17387346515796642834850517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591564343864428556567011 17387346515796642834850517)
                ·
                  refine ⟨407515933963983816441809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17387346515796642834850517 407515933963983816441809)
                  ·
                    rfl

theorem cell23_7142710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_7142710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142710 prefixEnd_7142710 := by exact prefixLift 7142710
  have htrace : WordTrace (prefixWord ++ tailWord_7142710) baseStart_7142710 baseEnd_7142710 := by
    simpa [prefixWord, tailWord_7142710, baseEnd_7142710] using wordTrace_append hprefix tailTrace_7142710
  have hstable : (prefixWord ++ tailWord_7142710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142710).length < 2 ^ (prefixWord ++ tailWord_7142710).sum := by decide
  have hdescent : baseEnd_7142710 < baseStart_7142710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142729 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_7142729 : Nat := 118140960795 + 7142729 * 2 ^ 59
def prefixEnd_7142729 : Nat := 4983230072969 + 3 ^ 40 * 7142729 * 2
def baseEnd_7142729 : Nat := 3667653161808289773638693

theorem tailTrace_7142729 : CollatzResearch.WordTrace tailWord_7142729 prefixEnd_7142729 3667653161808289773638693 := by
  unfold tailWord_7142729
  simp only [CollatzResearch.WordTrace]
  refine ⟨260516728940120188838623241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173677819293413459225748827 260516728940120188838623241)
  ·
    refine ⟨195387546705090141628967431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260516728940120188838623241 195387546705090141628967431)
    ·
      refine ⟨293081320057635212443451147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195387546705090141628967431 293081320057635212443451147)
      ·
        refine ⟨439621980086452818665176721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293081320057635212443451147 439621980086452818665176721)
        ·
          refine ⟨329716485064839613998882541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439621980086452818665176721 329716485064839613998882541)
          ·
            refine ⟨123643681899314855249580953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329716485064839613998882541 123643681899314855249580953)
            ·
              refine ⟨92732761424486141437185715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123643681899314855249580953 92732761424486141437185715)
              ·
                refine ⟨139099142136729212155778573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92732761424486141437185715 139099142136729212155778573)
                ·
                  refine ⟨52162178301273454558416965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139099142136729212155778573 52162178301273454558416965)
                  ·
                    refine ⟨9780408431488772729703181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52162178301273454558416965 9780408431488772729703181)
                    ·
                      refine ⟨3667653161808289773638693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780408431488772729703181 3667653161808289773638693)
                      ·
                        rfl

theorem cell23_7142729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_7142729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142729 prefixEnd_7142729 := by exact prefixLift 7142729
  have htrace : WordTrace (prefixWord ++ tailWord_7142729) baseStart_7142729 baseEnd_7142729 := by
    simpa [prefixWord, tailWord_7142729, baseEnd_7142729] using wordTrace_append hprefix tailTrace_7142729
  have hstable : (prefixWord ++ tailWord_7142729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142729).length < 2 ^ (prefixWord ++ tailWord_7142729).sum := by decide
  have hdescent : baseEnd_7142729 < baseStart_7142729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142746 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_7142746 : Nat := 118140960795 + 7142746 * 2 ^ 59
def prefixEnd_7142746 : Nat := 4983230072969 + 3 ^ 40 * 7142746 * 2
def baseEnd_7142746 : Nat := 3667661890979416207126115

theorem tailTrace_7142746 : CollatzResearch.WordTrace tailWord_7142746 prefixEnd_7142746 3667661890979416207126115 := by
  unfold tailWord_7142746
  simp only [CollatzResearch.WordTrace]
  refine ⟨65129337245264650185498023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173678232654039067161328061 65129337245264650185498023)
  ·
    refine ⟨97694005867896975278247035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65129337245264650185498023 97694005867896975278247035)
    ·
      refine ⟨146541008801845462917370553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97694005867896975278247035 146541008801845462917370553)
      ·
        refine ⟨109905756601384097188027915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146541008801845462917370553 109905756601384097188027915)
        ·
          refine ⟨164858634902076145782041873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109905756601384097188027915 164858634902076145782041873)
          ·
            refine ⟨123643976176557109336531405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164858634902076145782041873 123643976176557109336531405)
            ·
              refine ⟨46366491066208916001199277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123643976176557109336531405 46366491066208916001199277)
              ·
                refine ⟨17387434149828343500449729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46366491066208916001199277 17387434149828343500449729)
                ·
                  refine ⟨13040575612371257625337297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17387434149828343500449729 13040575612371257625337297)
                  ·
                    refine ⟨9780431709278443219002973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13040575612371257625337297 9780431709278443219002973)
                    ·
                      refine ⟨3667661890979416207126115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780431709278443219002973 3667661890979416207126115)
                      ·
                        rfl

theorem cell23_7142746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_7142746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142746 prefixEnd_7142746 := by exact prefixLift 7142746
  have htrace : WordTrace (prefixWord ++ tailWord_7142746) baseStart_7142746 baseEnd_7142746 := by
    simpa [prefixWord, tailWord_7142746, baseEnd_7142746] using wordTrace_append hprefix tailTrace_7142746
  have hstable : (prefixWord ++ tailWord_7142746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142746).length < 2 ^ (prefixWord ++ tailWord_7142746).sum := by decide
  have hdescent : baseEnd_7142746 < baseStart_7142746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142776 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_7142776 : Nat := 118140960795 + 7142776 * 2 ^ 59
def prefixEnd_7142776 : Nat := 4983230072969 + 3 ^ 40 * 7142776 * 2
def baseEnd_7142776 : Nat := 3667677295399051089750977

theorem tailTrace_7142776 : CollatzResearch.WordTrace tailWord_7142776 prefixEnd_7142776 3667677295399051089750977 := by
  unfold tailWord_7142776
  simp only [CollatzResearch.WordTrace]
  refine ⟨130259221585474957932792091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173678962113966610577056121 130259221585474957932792091)
  ·
    refine ⟨195388832378212436899188137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130259221585474957932792091 195388832378212436899188137)
    ·
      refine ⟨146541624283659327674391103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195388832378212436899188137 146541624283659327674391103)
      ·
        refine ⟨219812436425488991511586655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146541624283659327674391103 219812436425488991511586655)
        ·
          refine ⟨329718654638233487267379983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219812436425488991511586655 329718654638233487267379983)
          ·
            refine ⟨494577981957350230901069975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329718654638233487267379983 494577981957350230901069975)
            ·
              refine ⟨741866972936025346351604963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494577981957350230901069975 741866972936025346351604963)
              ·
                refine ⟨1112800459404038019527407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741866972936025346351604963 1112800459404038019527407445)
                ·
                  refine ⟨6520315191820535270668403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1112800459404038019527407445 6520315191820535270668403)
                  ·
                    refine ⟨9780472787730802906002605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6520315191820535270668403 9780472787730802906002605)
                    ·
                      refine ⟨3667677295399051089750977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780472787730802906002605 3667677295399051089750977)
                      ·
                        rfl

theorem cell23_7142776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_7142776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142776 prefixEnd_7142776 := by exact prefixLift 7142776
  have htrace : WordTrace (prefixWord ++ tailWord_7142776) baseStart_7142776 baseEnd_7142776 := by
    simpa [prefixWord, tailWord_7142776, baseEnd_7142776] using wordTrace_append hprefix tailTrace_7142776
  have hstable : (prefixWord ++ tailWord_7142776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142776).length < 2 ^ (prefixWord ++ tailWord_7142776).sum := by decide
  have hdescent : baseEnd_7142776 < baseStart_7142776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142779 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 5, 5]
def baseStart_7142779 : Nat := 118140960795 + 7142779 * 2 ^ 59
def prefixEnd_7142779 : Nat := 4983230072969 + 3 ^ 40 * 7142779 * 2
def baseEnd_7142779 : Nat := 1222559611947004859337821

theorem tailTrace_7142779 : CollatzResearch.WordTrace tailWord_7142779 prefixEnd_7142779 1222559611947004859337821 := by
  unfold tailWord_7142779
  simp only [CollatzResearch.WordTrace]
  refine ⟨260518552589939047377943391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173679035059959364918628927 260518552589939047377943391)
  ·
    refine ⟨390777828884908571066915087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260518552589939047377943391 390777828884908571066915087)
    ·
      refine ⟨586166743327362856600372631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390777828884908571066915087 586166743327362856600372631)
      ·
        refine ⟨879250114991044284900558947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586166743327362856600372631 879250114991044284900558947)
        ·
          refine ⟨1318875172486566427350838421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879250114991044284900558947 1318875172486566427350838421)
          ·
            refine ⟨61822273710307801282070551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1318875172486566427350838421 61822273710307801282070551)
            ·
              refine ⟨92733410565461701923105827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61822273710307801282070551 92733410565461701923105827)
              ·
                refine ⟨139100115848192552884658741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92733410565461701923105827 139100115848192552884658741)
                ·
                  refine ⟨13040635860768051832936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139100115848192552884658741 13040635860768051832936757)
                  ·
                    refine ⟨1222559611947004859337821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13040635860768051832936757 1222559611947004859337821)
                    ·
                      rfl

theorem cell23_7142779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 5].length) (baseStart_7142779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142779 prefixEnd_7142779 := by exact prefixLift 7142779
  have htrace : WordTrace (prefixWord ++ tailWord_7142779) baseStart_7142779 baseEnd_7142779 := by
    simpa [prefixWord, tailWord_7142779, baseEnd_7142779] using wordTrace_append hprefix tailTrace_7142779
  have hstable : (prefixWord ++ tailWord_7142779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142779).length < 2 ^ (prefixWord ++ tailWord_7142779).sum := by decide
  have hdescent : baseEnd_7142779 < baseStart_7142779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142796 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_7142796 : Nat := 118140960795 + 7142796 * 2 ^ 59
def prefixEnd_7142796 : Nat := 4983230072969 + 3 ^ 40 * 7142796 * 2
def baseEnd_7142796 : Nat := 1222562521670713670500295

theorem tailTrace_7142796 : CollatzResearch.WordTrace tailWord_7142796 prefixEnd_7142796 1222562521670713670500295 := by
  unfold tailWord_7142796
  simp only [CollatzResearch.WordTrace]
  refine ⟨130259586315438729640656121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173679448420584972854208161 130259586315438729640656121)
  ·
    refine ⟨97694689736579047230492091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130259586315438729640656121 97694689736579047230492091)
    ·
      refine ⟨146542034604868570845738137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97694689736579047230492091 146542034604868570845738137)
      ·
        refine ⟨109906525953651428134303603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146542034604868570845738137 109906525953651428134303603)
        ·
          refine ⟨164859788930477142201455405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109906525953651428134303603 164859788930477142201455405)
          ·
            refine ⟨61822420848928928325545777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164859788930477142201455405 61822420848928928325545777)
            ·
              refine ⟨46366815636696696244159333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61822420848928928325545777 46366815636696696244159333)
              ·
                refine ⟨8693777931880630545779875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46366815636696696244159333 8693777931880630545779875)
                ·
                  refine ⟨13040666897820945818669813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693777931880630545779875 13040666897820945818669813)
                  ·
                    refine ⟨1222562521670713670500295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13040666897820945818669813 1222562521670713670500295)
                    ·
                      rfl

theorem cell23_7142796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_7142796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142796 prefixEnd_7142796 := by exact prefixLift 7142796
  have htrace : WordTrace (prefixWord ++ tailWord_7142796) baseStart_7142796 baseEnd_7142796 := by
    simpa [prefixWord, tailWord_7142796, baseEnd_7142796] using wordTrace_append hprefix tailTrace_7142796
  have hstable : (prefixWord ++ tailWord_7142796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142796).length < 2 ^ (prefixWord ++ tailWord_7142796).sum := by decide
  have hdescent : baseEnd_7142796 < baseStart_7142796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142813 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_7142813 : Nat := 118140960795 + 7142813 * 2 ^ 59
def prefixEnd_7142813 : Nat := 4983230072969 + 3 ^ 40 * 7142813 * 2
def baseEnd_7142813 : Nat := 1222565431394422481662769

theorem tailTrace_7142813 : CollatzResearch.WordTrace tailWord_7142813 prefixEnd_7142813 1222565431394422481662769 := by
  unfold tailWord_7142813
  simp only [CollatzResearch.WordTrace]
  refine ⟨260519792671815871184681093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173679861781210580789787395 260519792671815871184681093)
  ·
    refine ⟨48847461125965475847127705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260519792671815871184681093 48847461125965475847127705)
    ·
      refine ⟨36635595844474106885345779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48847461125965475847127705 36635595844474106885345779)
      ·
        refine ⟨54953393766711160328018669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36635595844474106885345779 54953393766711160328018669)
        ·
          refine ⟨20607522662516685123007001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54953393766711160328018669 20607522662516685123007001)
          ·
            refine ⟨15455641996887513842255251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20607522662516685123007001 15455641996887513842255251)
            ·
              refine ⟨23183462995331270763382877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15455641996887513842255251 23183462995331270763382877)
              ·
                refine ⟨8693798623249226536268579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23183462995331270763382877 8693798623249226536268579)
                ·
                  refine ⟨13040697934873839804402869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693798623249226536268579 13040697934873839804402869)
                  ·
                    refine ⟨1222565431394422481662769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13040697934873839804402869 1222565431394422481662769)
                    ·
                      rfl

theorem cell23_7142813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_7142813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142813 prefixEnd_7142813 := by exact prefixLift 7142813
  have htrace : WordTrace (prefixWord ++ tailWord_7142813) baseStart_7142813 baseEnd_7142813 := by
    simpa [prefixWord, tailWord_7142813, baseEnd_7142813] using wordTrace_append hprefix tailTrace_7142813
  have hstable : (prefixWord ++ tailWord_7142813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142813).length < 2 ^ (prefixWord ++ tailWord_7142813).sum := by decide
  have hdescent : baseEnd_7142813 < baseStart_7142813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142839 : List Nat := [1, 1, 3, 1, 3, 2, 2, 10]
def baseStart_7142839 : Nat := 118140960795 + 7142839 * 2 ^ 59
def prefixEnd_7142839 : Nat := 4983230072969 + 3 ^ 40 * 7142839 * 2
def baseEnd_7142839 : Nat := 135841097951121642343081

theorem tailTrace_7142839 : CollatzResearch.WordTrace tailWord_7142839 prefixEnd_7142839 135841097951121642343081 := by
  unfold tailWord_7142839
  simp only [CollatzResearch.WordTrace]
  refine ⟨260520740969721677625127571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173680493979814451750085047 260520740969721677625127571)
  ·
    refine ⟨390781111454582516437691357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260520740969721677625127571 390781111454582516437691357)
    ·
      refine ⟨146542916795468443664134259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390781111454582516437691357 146542916795468443664134259)
      ·
        refine ⟨219814375193202665496201389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146542916795468443664134259 219814375193202665496201389)
        ·
          refine ⟨82430390697450999561075521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219814375193202665496201389 82430390697450999561075521)
          ·
            refine ⟨61822793023088249670806641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82430390697450999561075521 61822793023088249670806641)
            ·
              refine ⟨46367094767316187253104981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61822793023088249670806641 46367094767316187253104981)
              ·
                refine ⟨135841097951121642343081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46367094767316187253104981 135841097951121642343081)
                ·
                  rfl

theorem cell23_7142839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 10].length) (baseStart_7142839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142839 prefixEnd_7142839 := by exact prefixLift 7142839
  have htrace : WordTrace (prefixWord ++ tailWord_7142839) baseStart_7142839 baseEnd_7142839 := by
    simpa [prefixWord, tailWord_7142839, baseEnd_7142839] using wordTrace_append hprefix tailTrace_7142839
  have hstable : (prefixWord ++ tailWord_7142839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142839).length < 2 ^ (prefixWord ++ tailWord_7142839).sum := by decide
  have hdescent : baseEnd_7142839 < baseStart_7142839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142870 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7142870 : Nat := 118140960795 + 7142870 * 2 ^ 59
def prefixEnd_7142870 : Nat := 4983230072969 + 3 ^ 40 * 7142870 * 2
def baseEnd_7142870 : Nat := 3667725562580573721975545

theorem tailTrace_7142870 : CollatzResearch.WordTrace tailWord_7142870 prefixEnd_7142870 3667725562580573721975545 := by
  unfold tailWord_7142870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282616977038085619969129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173681247755072913279670709 16282616977038085619969129)
  ·
    refine ⟨12211962732778564214976847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16282616977038085619969129 12211962732778564214976847)
    ·
      refine ⟨18317944099167846322465271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211962732778564214976847 18317944099167846322465271)
      ·
        refine ⟨27476916148751769483697907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18317944099167846322465271 27476916148751769483697907)
        ·
          refine ⟨41215374223127654225546861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27476916148751769483697907 41215374223127654225546861)
          ·
            refine ⟨15455765333672870334580073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41215374223127654225546861 15455765333672870334580073)
            ·
              refine ⟨11591824000254652750935055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15455765333672870334580073 11591824000254652750935055)
              ·
                refine ⟨17387736000381979126402583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591824000254652750935055 17387736000381979126402583)
                ·
                  refine ⟨26081604000572968689603875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17387736000381979126402583 26081604000572968689603875)
                  ·
                    refine ⟨39122406000859453034405813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26081604000572968689603875 39122406000859453034405813)
                    ·
                      refine ⟨3667725562580573721975545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39122406000859453034405813 3667725562580573721975545)
                      ·
                        rfl

theorem cell23_7142870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7142870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142870 prefixEnd_7142870 := by exact prefixLift 7142870
  have htrace : WordTrace (prefixWord ++ tailWord_7142870) baseStart_7142870 baseEnd_7142870 := by
    simpa [prefixWord, tailWord_7142870, baseEnd_7142870] using wordTrace_append hprefix tailTrace_7142870
  have hstable : (prefixWord ++ tailWord_7142870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142870).length < 2 ^ (prefixWord ++ tailWord_7142870).sum := by decide
  have hdescent : baseEnd_7142870 < baseStart_7142870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7142889 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_7142889 : Nat := 118140960795 + 7142889 * 2 ^ 59
def prefixEnd_7142889 : Nat := 4983230072969 + 3 ^ 40 * 7142889 * 2
def baseEnd_7142889 : Nat := 3667735318713009147637957

theorem tailTrace_7142889 : CollatzResearch.WordTrace tailWord_7142889 prefixEnd_7142889 3667735318713009147637957 := by
  unfold tailWord_7142889
  simp only [CollatzResearch.WordTrace]
  refine ⟨260522564619540536164447721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173681709746360357442965147 260522564619540536164447721)
  ·
    refine ⟨195391923464655402123335791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260522564619540536164447721 195391923464655402123335791)
    ·
      refine ⟨293087885196983103185003687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195391923464655402123335791 293087885196983103185003687)
      ·
        refine ⟨439631827795474654777505531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293087885196983103185003687 439631827795474654777505531)
        ·
          refine ⟨659447741693211982166258297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439631827795474654777505531 659447741693211982166258297)
          ·
            refine ⟨494585806269908986624693723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659447741693211982166258297 494585806269908986624693723)
            ·
              refine ⟨741878709404863479937040585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494585806269908986624693723 741878709404863479937040585)
              ·
                refine ⟨556409032053647609952780439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741878709404863479937040585 556409032053647609952780439)
                ·
                  refine ⟨834613548080471414929170659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556409032053647609952780439 834613548080471414929170659)
                  ·
                    refine ⟨1251920322120707122393755989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 834613548080471414929170659 1251920322120707122393755989)
                    ·
                      refine ⟨3667735318713009147637957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1251920322120707122393755989 3667735318713009147637957)
                      ·
                        rfl

theorem cell23_7142889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_7142889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7142889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7142889 prefixEnd_7142889 := by exact prefixLift 7142889
  have htrace : WordTrace (prefixWord ++ tailWord_7142889) baseStart_7142889 baseEnd_7142889 := by
    simpa [prefixWord, tailWord_7142889, baseEnd_7142889] using wordTrace_append hprefix tailTrace_7142889
  have hstable : (prefixWord ++ tailWord_7142889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7142889).length < 2 ^ (prefixWord ++ tailWord_7142889).sum := by decide
  have hdescent : baseEnd_7142889 < baseStart_7142889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7142889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143013 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_7143013 : Nat := 118140960795 + 7143013 * 2 ^ 59
def prefixEnd_7143013 : Nat := 4983230072969 + 3 ^ 40 * 7143013 * 2
def baseEnd_7143013 : Nat := 3667798990314166662487387

theorem tailTrace_7143013 : CollatzResearch.WordTrace tailWord_7143013 prefixEnd_7143013 3667798990314166662487387 := by
  unfold tailWord_7143013
  simp only [CollatzResearch.WordTrace]
  refine ⟨260527087271091305341961693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173684724847394203561307795 260527087271091305341961693)
  ·
    refine ⟨97697657726659239503235635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260527087271091305341961693 97697657726659239503235635)
    ·
      refine ⟨146546486589988859254853453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97697657726659239503235635 146546486589988859254853453)
      ·
        refine ⟨54954932471245822220570045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146546486589988859254853453 54954932471245822220570045)
        ·
          refine ⟨20608099676717183332713767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54954932471245822220570045 20608099676717183332713767)
          ·
            refine ⟨30912149515075774999070651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608099676717183332713767 30912149515075774999070651)
            ·
              refine ⟨46368224272613662498605977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30912149515075774999070651 46368224272613662498605977)
              ·
                refine ⟨34776168204460246873954483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46368224272613662498605977 34776168204460246873954483)
                ·
                  refine ⟨52164252306690370310931725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34776168204460246873954483 52164252306690370310931725)
                  ·
                    refine ⟨19561594615008888866599397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52164252306690370310931725 19561594615008888866599397)
                    ·
                      refine ⟨3667798990314166662487387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19561594615008888866599397 3667798990314166662487387)
                      ·
                        rfl

theorem cell23_7143013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_7143013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143013 prefixEnd_7143013 := by exact prefixLift 7143013
  have htrace : WordTrace (prefixWord ++ tailWord_7143013) baseStart_7143013 baseEnd_7143013 := by
    simpa [prefixWord, tailWord_7143013, baseEnd_7143013] using wordTrace_append hprefix tailTrace_7143013
  have hstable : (prefixWord ++ tailWord_7143013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143013).length < 2 ^ (prefixWord ++ tailWord_7143013).sum := by decide
  have hdescent : baseEnd_7143013 < baseStart_7143013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143030 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7143030 : Nat := 118140960795 + 7143030 * 2 ^ 59
def prefixEnd_7143030 : Nat := 4983230072969 + 3 ^ 40 * 7143030 * 2
def baseEnd_7143030 : Nat := 3667807719485293095974809

theorem tailTrace_7143030 : CollatzResearch.WordTrace tailWord_7143030 prefixEnd_7143030 3667807719485293095974809 := by
  unfold tailWord_7143030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282981707001857327833159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173685138208019811496887029 16282981707001857327833159)
  ·
    refine ⟨24424472560502785991749739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282981707001857327833159 24424472560502785991749739)
    ·
      refine ⟨36636708840754178987624609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24424472560502785991749739 36636708840754178987624609)
      ·
        refine ⟨27477531630565634240718457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36636708840754178987624609 27477531630565634240718457)
        ·
          refine ⟨20608148722924225680538843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27477531630565634240718457 20608148722924225680538843)
          ·
            refine ⟨30912223084386338520808265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608148722924225680538843 30912223084386338520808265)
            ·
              refine ⟨23184167313289753890606199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30912223084386338520808265 23184167313289753890606199)
              ·
                refine ⟨34776250969934630835909299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23184167313289753890606199 34776250969934630835909299)
                ·
                  refine ⟨52164376454901946253863949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34776250969934630835909299 52164376454901946253863949)
                  ·
                    refine ⟨19561641170588229845198981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52164376454901946253863949 19561641170588229845198981)
                    ·
                      refine ⟨3667807719485293095974809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19561641170588229845198981 3667807719485293095974809)
                      ·
                        rfl

theorem cell23_7143030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7143030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143030 prefixEnd_7143030 := by exact prefixLift 7143030
  have htrace : WordTrace (prefixWord ++ tailWord_7143030) baseStart_7143030 baseEnd_7143030 := by
    simpa [prefixWord, tailWord_7143030, baseEnd_7143030] using wordTrace_append hprefix tailTrace_7143030
  have hstable : (prefixWord ++ tailWord_7143030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143030).length < 2 ^ (prefixWord ++ tailWord_7143030).sum := by decide
  have hdescent : baseEnd_7143030 < baseStart_7143030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143033 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_7143033 : Nat := 118140960795 + 7143033 * 2 ^ 59
def prefixEnd_7143033 : Nat := 4983230072969 + 3 ^ 40 * 7143033 * 2
def baseEnd_7143033 : Nat := 3667809259927256584237295

theorem tailTrace_7143033 : CollatzResearch.WordTrace tailWord_7143033 prefixEnd_7143033 3667809259927256584237295 := by
  unfold tailWord_7143033
  simp only [CollatzResearch.WordTrace]
  refine ⟨260527816731018848757689753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173685211154012565838459835 260527816731018848757689753)
  ·
    refine ⟨195395862548264136568267315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260527816731018848757689753 195395862548264136568267315)
    ·
      refine ⟨293093793822396204852400973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195395862548264136568267315 293093793822396204852400973)
      ·
        refine ⟨109910172683398576819650365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293093793822396204852400973 109910172683398576819650365)
        ·
          refine ⟨41216314756274466307368887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109910172683398576819650365 41216314756274466307368887)
          ·
            refine ⟨61824472134411699461053331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41216314756274466307368887 61824472134411699461053331)
            ·
              refine ⟨92736708201617549191579997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61824472134411699461053331 92736708201617549191579997)
              ·
                refine ⟨34776265575606580946842499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92736708201617549191579997 34776265575606580946842499)
                ·
                  refine ⟨52164398363409871420263749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34776265575606580946842499 52164398363409871420263749)
                  ·
                    refine ⟨9780824693139350891299453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52164398363409871420263749 9780824693139350891299453)
                    ·
                      refine ⟨3667809259927256584237295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780824693139350891299453 3667809259927256584237295)
                      ·
                        rfl

theorem cell23_7143033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_7143033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143033 prefixEnd_7143033 := by exact prefixLift 7143033
  have htrace : WordTrace (prefixWord ++ tailWord_7143033) baseStart_7143033 baseEnd_7143033 := by
    simpa [prefixWord, tailWord_7143033, baseEnd_7143033] using wordTrace_append hprefix tailTrace_7143033
  have hstable : (prefixWord ++ tailWord_7143033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143033).length < 2 ^ (prefixWord ++ tailWord_7143033).sum := by decide
  have hdescent : baseEnd_7143033 < baseStart_7143033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143050 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_7143050 : Nat := 118140960795 + 7143050 * 2 ^ 59
def prefixEnd_7143050 : Nat := 4983230072969 + 3 ^ 40 * 7143050 * 2
def baseEnd_7143050 : Nat := 3667817989098383017724717

theorem tailTrace_7143050 : CollatzResearch.WordTrace tailWord_7143050 prefixEnd_7143050 3667817989098383017724717 := by
  unfold tailWord_7143050
  simp only [CollatzResearch.WordTrace]
  refine ⟨65132109192989315165264651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173685624514638173774039069 65132109192989315165264651)
  ·
    refine ⟨97698163789483972747896977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65132109192989315165264651 97698163789483972747896977)
    ·
      refine ⟨73273622842112979560922733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97698163789483972747896977 73273622842112979560922733)
      ·
        refine ⟨27477608565792367335346025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73273622842112979560922733 27477608565792367335346025)
        ·
          refine ⟨20608206424344275501509519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27477608565792367335346025 20608206424344275501509519)
          ·
            refine ⟨30912309636516413252264279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608206424344275501509519 30912309636516413252264279)
            ·
              refine ⟨46368464454774619878396419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30912309636516413252264279 46368464454774619878396419)
              ·
                refine ⟨69552696682161929817594629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46368464454774619878396419 69552696682161929817594629)
                ·
                  refine ⟨13041130627905361840798993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69552696682161929817594629 13041130627905361840798993)
                  ·
                    refine ⟨9780847970929021380599245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13041130627905361840798993 9780847970929021380599245)
                    ·
                      refine ⟨3667817989098383017724717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780847970929021380599245 3667817989098383017724717)
                      ·
                        rfl

theorem cell23_7143050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_7143050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143050 prefixEnd_7143050 := by exact prefixLift 7143050
  have htrace : WordTrace (prefixWord ++ tailWord_7143050) baseStart_7143050 baseEnd_7143050 := by
    simpa [prefixWord, tailWord_7143050, baseEnd_7143050] using wordTrace_append hprefix tailTrace_7143050
  have hstable : (prefixWord ++ tailWord_7143050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143050).length < 2 ^ (prefixWord ++ tailWord_7143050).sum := by decide
  have hdescent : baseEnd_7143050 < baseStart_7143050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143056 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_7143056 : Nat := 118140960795 + 7143056 * 2 ^ 59
def prefixEnd_7143056 : Nat := 4983230072969 + 3 ^ 40 * 7143056 * 2
def baseEnd_7143056 : Nat := 3667821069982309994249689

theorem tailTrace_7143056 : CollatzResearch.WordTrace tailWord_7143056 prefixEnd_7143056 3667821069982309994249689 := by
  unfold tailWord_7143056
  simp only [CollatzResearch.WordTrace]
  refine ⟨130264327804967761842888511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173685770406623682457184681 130264327804967761842888511)
  ·
    refine ⟨195396491707451642764332767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130264327804967761842888511 195396491707451642764332767)
    ·
      refine ⟨293094737561177464146499151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195396491707451642764332767 293094737561177464146499151)
      ·
        refine ⟨439642106341766196219748727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293094737561177464146499151 439642106341766196219748727)
        ·
          refine ⟨659463159512649294329623091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439642106341766196219748727 659463159512649294329623091)
          ·
            refine ⟨989194739268973941494434637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659463159512649294329623091 989194739268973941494434637)
            ·
              refine ⟨370948027225865228060412989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 989194739268973941494434637 370948027225865228060412989)
              ·
                refine ⟨139105510209699460522654871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370948027225865228060412989 139105510209699460522654871)
                ·
                  refine ⟨208658265314549190783982307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139105510209699460522654871 208658265314549190783982307)
                  ·
                    refine ⟨312987397971823786175973461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 208658265314549190783982307 312987397971823786175973461)
                    ·
                      refine ⟨3667821069982309994249689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 312987397971823786175973461 3667821069982309994249689)
                      ·
                        rfl

theorem cell23_7143056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_7143056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143056 prefixEnd_7143056 := by exact prefixLift 7143056
  have htrace : WordTrace (prefixWord ++ tailWord_7143056) baseStart_7143056 baseEnd_7143056 := by
    simpa [prefixWord, tailWord_7143056, baseEnd_7143056] using wordTrace_append hprefix tailTrace_7143056
  have hstable : (prefixWord ++ tailWord_7143056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143056).length < 2 ^ (prefixWord ++ tailWord_7143056).sum := by decide
  have hdescent : baseEnd_7143056 < baseStart_7143056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143090 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_7143090 : Nat := 118140960795 + 7143090 * 2 ^ 59
def prefixEnd_7143090 : Nat := 4983230072969 + 3 ^ 40 * 7143090 * 2
def baseEnd_7143090 : Nat := 3667838528324562861224533

theorem tailTrace_7143090 : CollatzResearch.WordTrace tailWord_7143090 prefixEnd_7143090 3667838528324562861224533 := by
  unfold tailWord_7143090
  simp only [CollatzResearch.WordTrace]
  refine ⟨65132473922953086873128681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173686597127874898328343149 65132473922953086873128681)
  ·
    refine ⟨48849355442214815154846511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65132473922953086873128681 48849355442214815154846511)
    ·
      refine ⟨73274033163322222732269767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48849355442214815154846511 73274033163322222732269767)
      ·
        refine ⟨109911049744983334098404651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73274033163322222732269767 109911049744983334098404651)
        ·
          refine ⟨164866574617475001147606977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109911049744983334098404651 164866574617475001147606977)
          ·
            refine ⟨123649930963106250860705233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164866574617475001147606977 123649930963106250860705233)
            ·
              refine ⟨92737448222329688145528925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123649930963106250860705233 92737448222329688145528925)
              ·
                refine ⟨34776543083373633054573347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92737448222329688145528925 34776543083373633054573347)
                ·
                  refine ⟨52164814625060449581860021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34776543083373633054573347 52164814625060449581860021)
                  ·
                    refine ⟨4890451371099417148299377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52164814625060449581860021 4890451371099417148299377)
                    ·
                      refine ⟨3667838528324562861224533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4890451371099417148299377 3667838528324562861224533)
                      ·
                        rfl

theorem cell23_7143090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_7143090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143090 prefixEnd_7143090 := by exact prefixLift 7143090
  have htrace : WordTrace (prefixWord ++ tailWord_7143090) baseStart_7143090 baseEnd_7143090 := by
    simpa [prefixWord, tailWord_7143090, baseEnd_7143090] using wordTrace_append hprefix tailTrace_7143090
  have hstable : (prefixWord ++ tailWord_7143090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143090).length < 2 ^ (prefixWord ++ tailWord_7143090).sum := by decide
  have hdescent : baseEnd_7143090 < baseStart_7143090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143117 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7143117 : Nat := 118140960795 + 7143117 * 2 ^ 59
def prefixEnd_7143117 : Nat := 4983230072969 + 3 ^ 40 * 7143117 * 2
def baseEnd_7143117 : Nat := 1222617464100744751862303

theorem tailTrace_7143117 : CollatzResearch.WordTrace tailWord_7143117 prefixEnd_7143117 1222617464100744751862303 := by
  unfold tailWord_7143117
  simp only [CollatzResearch.WordTrace]
  refine ⟨260530880462714531103747605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173687253641809687402498403 260530880462714531103747605)
  ·
    refine ⟨12212385021689743645488169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260530880462714531103747605 12212385021689743645488169)
    ·
      refine ⟨9159288766267307734116127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12212385021689743645488169 9159288766267307734116127)
      ·
        refine ⟨13738933149400961601174191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159288766267307734116127 13738933149400961601174191)
        ·
          refine ⟨20608399724101442401761287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13738933149400961601174191 20608399724101442401761287)
          ·
            refine ⟨30912599586152163602641931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608399724101442401761287 30912599586152163602641931)
            ·
              refine ⟨46368899379228245403962897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30912599586152163602641931 46368899379228245403962897)
              ·
                refine ⟨34776674534421184052972173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46368899379228245403962897 34776674534421184052972173)
                ·
                  refine ⟨13041252950407944019864565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34776674534421184052972173 13041252950407944019864565)
                  ·
                    refine ⟨1222617464100744751862303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13041252950407944019864565 1222617464100744751862303)
                    ·
                      rfl

theorem cell23_7143117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7143117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143117 prefixEnd_7143117 := by exact prefixLift 7143117
  have htrace : WordTrace (prefixWord ++ tailWord_7143117) baseStart_7143117 baseEnd_7143117 := by
    simpa [prefixWord, tailWord_7143117, baseEnd_7143117] using wordTrace_append hprefix tailTrace_7143117
  have hstable : (prefixWord ++ tailWord_7143117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143117).length < 2 ^ (prefixWord ++ tailWord_7143117).sum := by decide
  have hdescent : baseEnd_7143117 < baseStart_7143117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143130 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_7143130 : Nat := 118140960795 + 7143130 * 2 ^ 59
def prefixEnd_7143130 : Nat := 4983230072969 + 3 ^ 40 * 7143130 * 2
def baseEnd_7143130 : Nat := 1222619689183580901574783

theorem tailTrace_7143130 : CollatzResearch.WordTrace tailWord_7143130 prefixEnd_7143130 1222619689183580901574783 := by
  unfold tailWord_7143130
  simp only [CollatzResearch.WordTrace]
  refine ⟨65132838652916858580992711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173687569741111622882647229 65132838652916858580992711)
  ·
    refine ⟨97699257979375287871489067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65132838652916858580992711 97699257979375287871489067)
    ·
      refine ⟨146548886969062931807233601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97699257979375287871489067 146548886969062931807233601)
      ·
        refine ⟨109911665226797198855425201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146548886969062931807233601 109911665226797198855425201)
        ·
          refine ⟨82433748920097899141568901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109911665226797198855425201 82433748920097899141568901)
          ·
            refine ⟨15456327922518356089044169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82433748920097899141568901 15456327922518356089044169)
            ·
              refine ⟨11592245941888767066783127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15456327922518356089044169 11592245941888767066783127)
              ·
                refine ⟨17388368912833150600174691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11592245941888767066783127 17388368912833150600174691)
                ·
                  refine ⟨26082553369249725900262037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17388368912833150600174691 26082553369249725900262037)
                  ·
                    refine ⟨1222619689183580901574783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26082553369249725900262037 1222619689183580901574783)
                    ·
                      rfl

theorem cell23_7143130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_7143130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143130 prefixEnd_7143130 := by exact prefixLift 7143130
  have htrace : WordTrace (prefixWord ++ tailWord_7143130) baseStart_7143130 baseEnd_7143130 := by
    simpa [prefixWord, tailWord_7143130, baseEnd_7143130] using wordTrace_append hprefix tailTrace_7143130
  have hstable : (prefixWord ++ tailWord_7143130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143130).length < 2 ^ (prefixWord ++ tailWord_7143130).sum := by decide
  have hdescent : baseEnd_7143130 < baseStart_7143130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143140 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_7143140 : Nat := 118140960795 + 7143140 * 2 ^ 59
def prefixEnd_7143140 : Nat := 4983230072969 + 3 ^ 40 * 7143140 * 2
def baseEnd_7143140 : Nat := 3667864202357287665599303

theorem tailTrace_7143140 : CollatzResearch.WordTrace tailWord_7143140 prefixEnd_7143140 3667864202357287665599303 := by
  unfold tailWord_7143140
  simp only [CollatzResearch.WordTrace]
  refine ⟨130265859670815603015917437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173687812894420804021223249 130265859670815603015917437)
  ·
    refine ⟨48849697376555851130969039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130265859670815603015917437 48849697376555851130969039)
    ·
      refine ⟨73274546064833776696453559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48849697376555851130969039 73274546064833776696453559)
      ·
        refine ⟨109911819097250665044680339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73274546064833776696453559 109911819097250665044680339)
        ·
          refine ⟨164867728645875997567020509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109911819097250665044680339 164867728645875997567020509)
          ·
            refine ⟨61825398242203499087632691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164867728645875997567020509 61825398242203499087632691)
            ·
              refine ⟨92738097363305248631449037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61825398242203499087632691 92738097363305248631449037)
              ·
                refine ⟨34776786511239468236793389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92738097363305248631449037 34776786511239468236793389)
                ·
                  refine ⟨13041294941714800588797521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34776786511239468236793389 13041294941714800588797521)
                  ·
                    refine ⟨9780971206286100441598141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13041294941714800588797521 9780971206286100441598141)
                    ·
                      refine ⟨3667864202357287665599303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9780971206286100441598141 3667864202357287665599303)
                      ·
                        rfl

theorem cell23_7143140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_7143140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143140 prefixEnd_7143140 := by exact prefixLift 7143140
  have htrace : WordTrace (prefixWord ++ tailWord_7143140) baseStart_7143140 baseEnd_7143140 := by
    simpa [prefixWord, tailWord_7143140, baseEnd_7143140] using wordTrace_append hprefix tailTrace_7143140
  have hstable : (prefixWord ++ tailWord_7143140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143140).length < 2 ^ (prefixWord ++ tailWord_7143140).sum := by decide
  have hdescent : baseEnd_7143140 < baseStart_7143140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143150 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7143150 : Nat := 118140960795 + 7143150 * 2 ^ 59
def prefixEnd_7143150 : Nat := 4983230072969 + 3 ^ 40 * 7143150 * 2
def baseEnd_7143150 : Nat := 3667869337163832626474257

theorem tailTrace_7143150 : CollatzResearch.WordTrace tailWord_7143150 prefixEnd_7143150 3667869337163832626474257 := by
  unfold tailWord_7143150
  simp only [CollatzResearch.WordTrace]
  refine ⟨32566510508949372217462363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173688056047729985159799269 32566510508949372217462363)
  ·
    refine ⟨48849765763424058326193545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32566510508949372217462363 48849765763424058326193545)
    ·
      refine ⟨36637324322568043744645159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48849765763424058326193545 36637324322568043744645159)
      ·
        refine ⟨54955986483852065616967739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36637324322568043744645159 54955986483852065616967739)
        ·
          refine ⟨82433979725778098425451609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54955986483852065616967739 82433979725778098425451609)
          ·
            refine ⟨61825484794333573819088707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82433979725778098425451609 61825484794333573819088707)
            ·
              refine ⟨92738227191500360728633061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61825484794333573819088707 92738227191500360728633061)
              ·
                refine ⟨17388417598406317636618699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92738227191500360728633061 17388417598406317636618699)
                ·
                  refine ⟨26082626397609476454928049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17388417598406317636618699 26082626397609476454928049)
                  ·
                    refine ⟨19561969798207107341196037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26082626397609476454928049 19561969798207107341196037)
                    ·
                      refine ⟨3667869337163832626474257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19561969798207107341196037 3667869337163832626474257)
                      ·
                        rfl

theorem cell23_7143150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7143150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143150 prefixEnd_7143150 := by exact prefixLift 7143150
  have htrace : WordTrace (prefixWord ++ tailWord_7143150) baseStart_7143150 baseEnd_7143150 := by
    simpa [prefixWord, tailWord_7143150, baseEnd_7143150] using wordTrace_append hprefix tailTrace_7143150
  have hstable : (prefixWord ++ tailWord_7143150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143150).length < 2 ^ (prefixWord ++ tailWord_7143150).sum := by decide
  have hdescent : baseEnd_7143150 < baseStart_7143150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143188 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7143188 : Nat := 118140960795 + 7143188 * 2 ^ 59
def prefixEnd_7143188 : Nat := 4983230072969 + 3 ^ 40 * 7143188 * 2
def baseEnd_7143188 : Nat := 3667888849428703477799083

theorem tailTrace_7143188 : CollatzResearch.WordTrace tailWord_7143188 prefixEnd_7143188 3667888849428703477799083 := by
  unfold tailWord_7143188
  simp only [CollatzResearch.WordTrace]
  refine ⟨130266735022728655114791109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173688980030304873486388145 130266735022728655114791109)
  ·
    refine ⟨24425012816761622834023333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130266735022728655114791109 24425012816761622834023333)
    ·
      refine ⟨4579689903142804281379375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24425012816761622834023333 4579689903142804281379375)
      ·
        refine ⟨6869534854714206422069063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579689903142804281379375 6869534854714206422069063)
        ·
          refine ⟨10304302282071309633103595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869534854714206422069063 10304302282071309633103595)
          ·
            refine ⟨15456453423106964449655393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10304302282071309633103595 15456453423106964449655393)
            ·
              refine ⟨11592340067330223337241545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15456453423106964449655393 11592340067330223337241545)
              ·
                refine ⟨8694255050497667502931159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11592340067330223337241545 8694255050497667502931159)
                ·
                  refine ⟨13041382575746501254396739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8694255050497667502931159 13041382575746501254396739)
                  ·
                    refine ⟨19562073863619751881595109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13041382575746501254396739 19562073863619751881595109)
                    ·
                      refine ⟨3667888849428703477799083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19562073863619751881595109 3667888849428703477799083)
                      ·
                        rfl

theorem cell23_7143188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7143188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143188 prefixEnd_7143188 := by exact prefixLift 7143188
  have htrace : WordTrace (prefixWord ++ tailWord_7143188) baseStart_7143188 baseEnd_7143188 := by
    simpa [prefixWord, tailWord_7143188, baseEnd_7143188] using wordTrace_append hprefix tailTrace_7143188
  have hstable : (prefixWord ++ tailWord_7143188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143188).length < 2 ^ (prefixWord ++ tailWord_7143188).sum := by decide
  have hdescent : baseEnd_7143188 < baseStart_7143188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143193 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_7143193 : Nat := 118140960795 + 7143193 * 2 ^ 59
def prefixEnd_7143193 : Nat := 4983230072969 + 3 ^ 40 * 7143193 * 2
def baseEnd_7143193 : Nat := 3667891416831975958236559

theorem tailTrace_7143193 : CollatzResearch.WordTrace tailWord_7143193 prefixEnd_7143193 3667891416831975958236559 := by
  unfold tailWord_7143193
  simp only [CollatzResearch.WordTrace]
  refine ⟨260533652410439196083514233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173689101606959464055676155 260533652410439196083514233)
  ·
    refine ⟨195400239307829397062635675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260533652410439196083514233 195400239307829397062635675)
    ·
      refine ⟨293100358961744095593953513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195400239307829397062635675 293100358961744095593953513)
      ·
        refine ⟨219825269221308071695465135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293100358961744095593953513 219825269221308071695465135)
        ·
          refine ⟨329737903831962107543197703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219825269221308071695465135 329737903831962107543197703)
          ·
            refine ⟨494606855747943161314796555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329737903831962107543197703 494606855747943161314796555)
            ·
              refine ⟨741910283621914741972194833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494606855747943161314796555 741910283621914741972194833)
              ·
                refine ⟨556432712716436056479146125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741910283621914741972194833 556432712716436056479146125)
                ·
                  refine ⟨208662267268663521179679797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556432712716436056479146125 208662267268663521179679797)
                  ·
                    refine ⟨19562087556437205110594981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208662267268663521179679797 19562087556437205110594981)
                    ·
                      refine ⟨3667891416831975958236559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19562087556437205110594981 3667891416831975958236559)
                      ·
                        rfl

theorem cell23_7143193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_7143193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143193 prefixEnd_7143193 := by exact prefixLift 7143193
  have htrace : WordTrace (prefixWord ++ tailWord_7143193) baseStart_7143193 baseEnd_7143193 := by
    simpa [prefixWord, tailWord_7143193, baseEnd_7143193] using wordTrace_append hprefix tailTrace_7143193
  have hstable : (prefixWord ++ tailWord_7143193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143193).length < 2 ^ (prefixWord ++ tailWord_7143193).sum := by decide
  have hdescent : baseEnd_7143193 < baseStart_7143193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143203 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 8]
def baseStart_7143203 : Nat := 118140960795 + 7143203 * 2 ^ 59
def prefixEnd_7143203 : Nat := 4983230072969 + 3 ^ 40 * 7143203 * 2
def baseEnd_7143203 : Nat := 1222632183879506973037171

theorem tailTrace_7143203 : CollatzResearch.WordTrace tailWord_7143203 prefixEnd_7143203 1222632183879506973037171 := by
  unfold tailWord_7143203
  simp only [CollatzResearch.WordTrace]
  refine ⟨260534017140402967791378263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173689344760268645194252175 260534017140402967791378263)
  ·
    refine ⟨390801025710604451687067395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260534017140402967791378263 390801025710604451687067395)
    ·
      refine ⟨586201538565906677530601093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390801025710604451687067395 586201538565906677530601093)
      ·
        refine ⟨109912788481107502036987705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 586201538565906677530601093 109912788481107502036987705)
        ·
          refine ⟨82434591360830626527740779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109912788481107502036987705 82434591360830626527740779)
          ·
            refine ⟨123651887041245939791611169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82434591360830626527740779 123651887041245939791611169)
            ·
              refine ⟨92738915280934454843708377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123651887041245939791611169 92738915280934454843708377)
              ·
                refine ⟨69554186460700841132781283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92738915280934454843708377 69554186460700841132781283)
                ·
                  refine ⟨104331279691051261699171925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69554186460700841132781283 104331279691051261699171925)
                  ·
                    refine ⟨1222632183879506973037171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104331279691051261699171925 1222632183879506973037171)
                    ·
                      rfl

theorem cell23_7143203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_7143203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143203 prefixEnd_7143203 := by exact prefixLift 7143203
  have htrace : WordTrace (prefixWord ++ tailWord_7143203) baseStart_7143203 baseEnd_7143203 := by
    simpa [prefixWord, tailWord_7143203, baseEnd_7143203] using wordTrace_append hprefix tailTrace_7143203
  have hstable : (prefixWord ++ tailWord_7143203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143203).length < 2 ^ (prefixWord ++ tailWord_7143203).sum := by decide
  have hdescent : baseEnd_7143203 < baseStart_7143203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143223 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_7143223 : Nat := 118140960795 + 7143223 * 2 ^ 59
def prefixEnd_7143223 : Nat := 4983230072969 + 3 ^ 40 * 7143223 * 2
def baseEnd_7143223 : Nat := 3667906821251610840861421

theorem tailTrace_7143223 : CollatzResearch.WordTrace tailWord_7143223 prefixEnd_7143223 3667906821251610840861421 := by
  unfold tailWord_7143223
  simp only [CollatzResearch.WordTrace]
  refine ⟨260534746600330511207106323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173689831066887007471404215 260534746600330511207106323)
  ·
    refine ⟨390802119900495766810659485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260534746600330511207106323 390802119900495766810659485)
    ·
      refine ⟨146550794962685912553997307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390802119900495766810659485 146550794962685912553997307)
      ·
        refine ⟨219826192444028868830995961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146550794962685912553997307 219826192444028868830995961)
        ·
          refine ⟨164869644333021651623246971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219826192444028868830995961 164869644333021651623246971)
          ·
            refine ⟨247304466499532477434870457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164869644333021651623246971 247304466499532477434870457)
            ·
              refine ⟨185478349874649358076152843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247304466499532477434870457 185478349874649358076152843)
              ·
                refine ⟨278217524811974037114229265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185478349874649358076152843 278217524811974037114229265)
                ·
                  refine ⟨208663143608980527835671949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278217524811974037114229265 208663143608980527835671949)
                  ·
                    refine ⟨78248678853367697938376981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208663143608980527835671949 78248678853367697938376981)
                    ·
                      refine ⟨3667906821251610840861421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78248678853367697938376981 3667906821251610840861421)
                      ·
                        rfl

theorem cell23_7143223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_7143223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143223 prefixEnd_7143223 := by exact prefixLift 7143223
  have htrace : WordTrace (prefixWord ++ tailWord_7143223) baseStart_7143223 baseEnd_7143223 := by
    simpa [prefixWord, tailWord_7143223, baseEnd_7143223] using wordTrace_append hprefix tailTrace_7143223
  have hstable : (prefixWord ++ tailWord_7143223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143223).length < 2 ^ (prefixWord ++ tailWord_7143223).sum := by decide
  have hdescent : baseEnd_7143223 < baseStart_7143223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143238 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7143238 : Nat := 118140960795 + 7143238 * 2 ^ 59
def prefixEnd_7143238 : Nat := 4983230072969 + 3 ^ 40 * 7143238 * 2
def baseEnd_7143238 : Nat := 3667914523461428282173853

theorem tailTrace_7143238 : CollatzResearch.WordTrace tailWord_7143238 prefixEnd_7143238 3667914523461428282173853 := by
  unfold tailWord_7143238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141727927977380274028199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173690195796850779179268245 8141727927977380274028199)
  ·
    refine ⟨12212591891966070411042299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8141727927977380274028199 12212591891966070411042299)
    ·
      refine ⟨18318887837949105616563449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12212591891966070411042299 18318887837949105616563449)
      ·
        refine ⟨13739165878461829212422587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18318887837949105616563449 13739165878461829212422587)
        ·
          refine ⟨20608748817692743818633881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739165878461829212422587 20608748817692743818633881)
          ·
            refine ⟨15456561613269557863975411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20608748817692743818633881 15456561613269557863975411)
            ·
              refine ⟨23184842419904336795963117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15456561613269557863975411 23184842419904336795963117)
              ·
                refine ⟨8694315907464126298486169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23184842419904336795963117 8694315907464126298486169)
                ·
                  refine ⟨6520736930598094723864627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8694315907464126298486169 6520736930598094723864627)
                  ·
                    refine ⟨9781105395897142085796941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6520736930598094723864627 9781105395897142085796941)
                    ·
                      refine ⟨3667914523461428282173853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9781105395897142085796941 3667914523461428282173853)
                      ·
                        rfl

theorem cell23_7143238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7143238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143238 prefixEnd_7143238 := by exact prefixLift 7143238
  have htrace : WordTrace (prefixWord ++ tailWord_7143238) baseStart_7143238 baseEnd_7143238 := by
    simpa [prefixWord, tailWord_7143238, baseEnd_7143238] using wordTrace_append hprefix tailTrace_7143238
  have hstable : (prefixWord ++ tailWord_7143238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143238).length < 2 ^ (prefixWord ++ tailWord_7143238).sum := by decide
  have hdescent : baseEnd_7143238 < baseStart_7143238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143278 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_7143278 : Nat := 118140960795 + 7143278 * 2 ^ 59
def prefixEnd_7143278 : Nat := 4983230072969 + 3 ^ 40 * 7143278 * 2
def baseEnd_7143278 : Nat := 3667935062687608125673669

theorem tailTrace_7143278 : CollatzResearch.WordTrace tailWord_7143278 prefixEnd_7143278 3667935062687608125673669 := by
  unfold tailWord_7143278
  simp only [CollatzResearch.WordTrace]
  refine ⟨32567094076891406950044811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173691168410087503733572325 32567094076891406950044811)
  ·
    refine ⟨48850641115337110425067217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32567094076891406950044811 48850641115337110425067217)
    ·
      refine ⟨36637980836502832818800413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48850641115337110425067217 36637980836502832818800413)
      ·
        refine ⟨13739242813688562307050155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36637980836502832818800413 13739242813688562307050155)
        ·
          refine ⟨20608864220532843460575233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739242813688562307050155 20608864220532843460575233)
          ·
            refine ⟨15456648165399632595431425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20608864220532843460575233 15456648165399632595431425)
            ·
              refine ⟨11592486124049724446573569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15456648165399632595431425 11592486124049724446573569)
              ·
                refine ⟨8694364593037293334930177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11592486124049724446573569 8694364593037293334930177)
                ·
                  refine ⟨6520773444777970001197633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8694364593037293334930177 6520773444777970001197633)
                  ·
                    refine ⟨4890580083583477500898225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6520773444777970001197633 4890580083583477500898225)
                    ·
                      refine ⟨3667935062687608125673669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4890580083583477500898225 3667935062687608125673669)
                      ·
                        rfl

theorem cell23_7143278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_7143278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143278 prefixEnd_7143278 := by exact prefixLift 7143278
  have htrace : WordTrace (prefixWord ++ tailWord_7143278) baseStart_7143278 baseEnd_7143278 := by
    simpa [prefixWord, tailWord_7143278, baseEnd_7143278] using wordTrace_append hprefix tailTrace_7143278
  have hstable : (prefixWord ++ tailWord_7143278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143278).length < 2 ^ (prefixWord ++ tailWord_7143278).sum := by decide
  have hdescent : baseEnd_7143278 < baseStart_7143278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143290 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_7143290 : Nat := 118140960795 + 7143290 * 2 ^ 59
def prefixEnd_7143290 : Nat := 4983230072969 + 3 ^ 40 * 7143290 * 2
def baseEnd_7143290 : Nat := 3667941224455462078723613

theorem tailTrace_7143290 : CollatzResearch.WordTrace tailWord_7143290 prefixEnd_7143290 3667941224455462078723613 := by
  unfold tailWord_7143290
  simp only [CollatzResearch.WordTrace]
  refine ⟨65134297572771945412448831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173691460194058521099863549 65134297572771945412448831)
  ·
    refine ⟨97701446359157918118673247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65134297572771945412448831 97701446359157918118673247)
    ·
      refine ⟨146552169538736877178009871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97701446359157918118673247 146552169538736877178009871)
      ·
        refine ⟨219828254308105315767014807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146552169538736877178009871 219828254308105315767014807)
        ·
          refine ⟨329742381462157973650522211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219828254308105315767014807 329742381462157973650522211)
          ·
            refine ⟨494613572193236960475783317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329742381462157973650522211 494613572193236960475783317)
            ·
              refine ⟨23185011196557982522302343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 494613572193236960475783317 23185011196557982522302343)
              ·
                refine ⟨34777516794836973783453515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23185011196557982522302343 34777516794836973783453515)
                ·
                  refine ⟨52166275192255460675180273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34777516794836973783453515 52166275192255460675180273)
                  ·
                    refine ⟨39124706394191595506385205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52166275192255460675180273 39124706394191595506385205)
                    ·
                      refine ⟨3667941224455462078723613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39124706394191595506385205 3667941224455462078723613)
                      ·
                        rfl

theorem cell23_7143290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_7143290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143290 prefixEnd_7143290 := by exact prefixLift 7143290
  have htrace : WordTrace (prefixWord ++ tailWord_7143290) baseStart_7143290 baseEnd_7143290 := by
    simpa [prefixWord, tailWord_7143290, baseEnd_7143290] using wordTrace_append hprefix tailTrace_7143290
  have hstable : (prefixWord ++ tailWord_7143290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143290).length < 2 ^ (prefixWord ++ tailWord_7143290).sum := by decide
  have hdescent : baseEnd_7143290 < baseStart_7143290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143294 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7143294 : Nat := 118140960795 + 7143294 * 2 ^ 59
def prefixEnd_7143294 : Nat := 4983230072969 + 3 ^ 40 * 7143294 * 2
def baseEnd_7143294 : Nat := 3667943278378080063073595

theorem tailTrace_7143294 : CollatzResearch.WordTrace tailWord_7143294 prefixEnd_7143294 3667943278378080063073595 := by
  unfold tailWord_7143294
  simp only [CollatzResearch.WordTrace]
  refine ⟨32567167022884161291617617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173691557455382193555293957 32567167022884161291617617)
  ·
    refine ⟨24425375267163120968713213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32567167022884161291617617 24425375267163120968713213)
    ·
      refine ⟨9159515725186170363267455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24425375267163120968713213 9159515725186170363267455)
      ·
        refine ⟨13739273587779255544901183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159515725186170363267455 13739273587779255544901183)
        ·
          refine ⟨20608910381668883317351775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739273587779255544901183 20608910381668883317351775)
          ·
            refine ⟨30913365572503324976027663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608910381668883317351775 30913365572503324976027663)
            ·
              refine ⟨46370048358754987464041495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30913365572503324976027663 46370048358754987464041495)
              ·
                refine ⟨69555072538132481196062243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46370048358754987464041495 69555072538132481196062243)
                ·
                  refine ⟨104332608807198721794093365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69555072538132481196062243 104332608807198721794093365)
                  ·
                    refine ⟨9781182075674880168196253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104332608807198721794093365 9781182075674880168196253)
                    ·
                      refine ⟨3667943278378080063073595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9781182075674880168196253 3667943278378080063073595)
                      ·
                        rfl

theorem cell23_7143294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7143294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143294 prefixEnd_7143294 := by exact prefixLift 7143294
  have htrace : WordTrace (prefixWord ++ tailWord_7143294) baseStart_7143294 baseEnd_7143294 := by
    simpa [prefixWord, tailWord_7143294, baseEnd_7143294] using wordTrace_append hprefix tailTrace_7143294
  have hstable : (prefixWord ++ tailWord_7143294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143294).length < 2 ^ (prefixWord ++ tailWord_7143294).sum := by decide
  have hdescent : baseEnd_7143294 < baseStart_7143294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143314 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_7143314 : Nat := 118140960795 + 7143314 * 2 ^ 59
def prefixEnd_7143314 : Nat := 4983230072969 + 3 ^ 40 * 7143314 * 2
def baseEnd_7143314 : Nat := 1222651182663723328274501

theorem tailTrace_7143314 : CollatzResearch.WordTrace tailWord_7143314 prefixEnd_7143314 1222651182663723328274501 := by
  unfold tailWord_7143314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65134516410750208437167249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173692043762000555832445997 65134516410750208437167249)
  ·
    refine ⟨48850887308062656327875437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65134516410750208437167249 48850887308062656327875437)
    ·
      refine ⟨18319082740523496122953289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48850887308062656327875437 18319082740523496122953289)
      ·
        refine ⟨13739312055392622092214967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18319082740523496122953289 13739312055392622092214967)
        ·
          refine ⟨20608968083088933138322451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739312055392622092214967 20608968083088933138322451)
          ·
            refine ⟨30913452124633399707483677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608968083088933138322451 30913452124633399707483677)
            ·
              refine ⟨11592544546737524890306379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30913452124633399707483677 11592544546737524890306379)
              ·
                refine ⟨17388816820106287335459569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11592544546737524890306379 17388816820106287335459569)
                ·
                  refine ⟨13041612615079715501594677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17388816820106287335459569 13041612615079715501594677)
                  ·
                    refine ⟨1222651182663723328274501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13041612615079715501594677 1222651182663723328274501)
                    ·
                      rfl

theorem cell23_7143314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_7143314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143314 prefixEnd_7143314 := by exact prefixLift 7143314
  have htrace : WordTrace (prefixWord ++ tailWord_7143314) baseStart_7143314 baseEnd_7143314 := by
    simpa [prefixWord, tailWord_7143314, baseEnd_7143314] using wordTrace_append hprefix tailTrace_7143314
  have hstable : (prefixWord ++ tailWord_7143314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143314).length < 2 ^ (prefixWord ++ tailWord_7143314).sum := by decide
  have hdescent : baseEnd_7143314 < baseStart_7143314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143317 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_7143317 : Nat := 118140960795 + 7143317 * 2 ^ 59
def prefixEnd_7143317 : Nat := 4983230072969 + 3 ^ 40 * 7143317 * 2
def baseEnd_7143317 : Nat := 3667955088433133473085989

theorem tailTrace_7143317 : CollatzResearch.WordTrace tailWord_7143317 prefixEnd_7143317 3667955088433133473085989 := by
  unfold tailWord_7143317
  simp only [CollatzResearch.WordTrace]
  refine ⟨260538175061989965261028205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173692116707993310174018803 260538175061989965261028205)
  ·
    refine ⟨97701815648246236972885577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260538175061989965261028205 97701815648246236972885577)
    ·
      refine ⟨73276361736184677729664183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97701815648246236972885577 73276361736184677729664183)
      ·
        refine ⟨109914542604277016594496275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73276361736184677729664183 109914542604277016594496275)
        ·
          refine ⟨164871813906415524891744413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109914542604277016594496275 164871813906415524891744413)
          ·
            refine ⟨61826930214905821834404155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164871813906415524891744413 61826930214905821834404155)
            ·
              refine ⟨92740395322358732751606233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61826930214905821834404155 92740395322358732751606233)
              ·
                refine ⟨69555296491769049563704675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92740395322358732751606233 69555296491769049563704675)
                ·
                  refine ⟨104332944737653574345557013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69555296491769049563704675 104332944737653574345557013)
                  ·
                    refine ⟨4890606784577511297447985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104332944737653574345557013 4890606784577511297447985)
                    ·
                      refine ⟨3667955088433133473085989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4890606784577511297447985 3667955088433133473085989)
                      ·
                        rfl

theorem cell23_7143317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_7143317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143317 prefixEnd_7143317 := by exact prefixLift 7143317
  have htrace : WordTrace (prefixWord ++ tailWord_7143317) baseStart_7143317 baseEnd_7143317 := by
    simpa [prefixWord, tailWord_7143317, baseEnd_7143317] using wordTrace_append hprefix tailTrace_7143317
  have hstable : (prefixWord ++ tailWord_7143317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143317).length < 2 ^ (prefixWord ++ tailWord_7143317).sum := by decide
  have hdescent : baseEnd_7143317 < baseStart_7143317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143360 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_7143360 : Nat := 118140960795 + 7143360 * 2 ^ 59
def prefixEnd_7143360 : Nat := 4983230072969 + 3 ^ 40 * 7143360 * 2
def baseEnd_7143360 : Nat := 3667977168101276804848291

theorem tailTrace_7143360 : CollatzResearch.WordTrace tailWord_7143360 prefixEnd_7143360 3667977168101276804848291 := by
  unfold tailWord_7143360
  simp only [CollatzResearch.WordTrace]
  refine ⟨130269871700417091802421767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173693162267222789069895689 130269871700417091802421767)
  ·
    refine ⟨195404807550625637703632651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130269871700417091802421767 195404807550625637703632651)
    ·
      refine ⟨293107211325938456555448977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195404807550625637703632651 293107211325938456555448977)
      ·
        refine ⟨219830408494453842416586733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293107211325938456555448977 219830408494453842416586733)
        ·
          refine ⟨82436403185420190906220025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219830408494453842416586733 82436403185420190906220025)
          ·
            refine ⟨61827302389065143179665019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82436403185420190906220025 61827302389065143179665019)
            ·
              refine ⟨92740953583597714769497529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61827302389065143179665019 92740953583597714769497529)
              ·
                refine ⟨69555715187698286077123147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92740953583597714769497529 69555715187698286077123147)
                ·
                  refine ⟨104333572781547429115684721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69555715187698286077123147 104333572781547429115684721)
                  ·
                    refine ⟨78250179586160571836763541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104333572781547429115684721 78250179586160571836763541)
                    ·
                      refine ⟨3667977168101276804848291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78250179586160571836763541 3667977168101276804848291)
                      ·
                        rfl

theorem cell23_7143360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_7143360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143360 prefixEnd_7143360 := by exact prefixLift 7143360
  have htrace : WordTrace (prefixWord ++ tailWord_7143360) baseStart_7143360 baseEnd_7143360 := by
    simpa [prefixWord, tailWord_7143360, baseEnd_7143360] using wordTrace_append hprefix tailTrace_7143360
  have hstable : (prefixWord ++ tailWord_7143360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143360).length < 2 ^ (prefixWord ++ tailWord_7143360).sum := by decide
  have hdescent : baseEnd_7143360 < baseStart_7143360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143407 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_7143407 : Nat := 118140960795 + 7143407 * 2 ^ 59
def prefixEnd_7143407 : Nat := 4983230072969 + 3 ^ 40 * 7143407 * 2
def baseEnd_7143407 : Nat := 3668001301692038120960575

theorem tailTrace_7143407 : CollatzResearch.WordTrace tailWord_7143407 prefixEnd_7143407 3668001301692038120960575 := by
  unfold tailWord_7143407
  simp only [CollatzResearch.WordTrace]
  refine ⟨260541457631663910631804475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173694305087775940421202983 260541457631663910631804475)
  ·
    refine ⟨390812186447495865947706713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260541457631663910631804475 390812186447495865947706713)
    ·
      refine ⟨293109139835621899460780035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390812186447495865947706713 293109139835621899460780035)
      ·
        refine ⟨439663709753432849191170053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293109139835621899460780035 439663709753432849191170053)
        ·
          refine ⟨82436945578768659223344385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439663709753432849191170053 82436945578768659223344385)
          ·
            refine ⟨61827709184076494417508289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82436945578768659223344385 61827709184076494417508289)
            ·
              refine ⟨46370781888057370813131217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61827709184076494417508289 46370781888057370813131217)
              ·
                refine ⟨34778086416043028109848413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46370781888057370813131217 34778086416043028109848413)
                ·
                  refine ⟨13041782406016135541193155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34778086416043028109848413 13041782406016135541193155)
                  ·
                    refine ⟨19562673609024203311789733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13041782406016135541193155 19562673609024203311789733)
                    ·
                      refine ⟨3668001301692038120960575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19562673609024203311789733 3668001301692038120960575)
                      ·
                        rfl

theorem cell23_7143407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_7143407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143407 prefixEnd_7143407 := by exact prefixLift 7143407
  have htrace : WordTrace (prefixWord ++ tailWord_7143407) baseStart_7143407 baseEnd_7143407 := by
    simpa [prefixWord, tailWord_7143407, baseEnd_7143407] using wordTrace_append hprefix tailTrace_7143407
  have hstable : (prefixWord ++ tailWord_7143407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143407).length < 2 ^ (prefixWord ++ tailWord_7143407).sum := by decide
  have hdescent : baseEnd_7143407 < baseStart_7143407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143434 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_7143434 : Nat := 118140960795 + 7143434 * 2 ^ 59
def prefixEnd_7143434 : Nat := 4983230072969 + 3 ^ 40 * 7143434 * 2
def baseEnd_7143434 : Nat := 1222671721889903171774317

theorem tailTrace_7143434 : CollatzResearch.WordTrace tailWord_7143434 prefixEnd_7143434 1222671721889903171774317 := by
  unfold tailWord_7143434
  simp only [CollatzResearch.WordTrace]
  refine ⟨65135610600641523560759339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173694961601710729495358237 65135610600641523560759339)
  ·
    refine ⟨97703415900962285341139009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65135610600641523560759339 97703415900962285341139009)
    ·
      refine ⟨73277561925721714005854257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97703415900962285341139009 73277561925721714005854257)
      ·
        refine ⟨54958171444291285504390693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73277561925721714005854257 54958171444291285504390693)
        ·
          refine ⟨10304657145804616032073255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54958171444291285504390693 10304657145804616032073255)
          ·
            refine ⟨15456985718706924048109883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10304657145804616032073255 15456985718706924048109883)
            ·
              refine ⟨23185478578060386072164825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15456985718706924048109883 23185478578060386072164825)
              ·
                refine ⟨17389108933545289554123619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23185478578060386072164825 17389108933545289554123619)
                ·
                  refine ⟨26083663400317934331185429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17389108933545289554123619 26083663400317934331185429)
                  ·
                    refine ⟨1222671721889903171774317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26083663400317934331185429 1222671721889903171774317)
                    ·
                      rfl

theorem cell23_7143434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_7143434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143434 prefixEnd_7143434 := by exact prefixLift 7143434
  have htrace : WordTrace (prefixWord ++ tailWord_7143434) baseStart_7143434 baseEnd_7143434 := by
    simpa [prefixWord, tailWord_7143434, baseEnd_7143434] using wordTrace_append hprefix tailTrace_7143434
  have hstable : (prefixWord ++ tailWord_7143434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143434).length < 2 ^ (prefixWord ++ tailWord_7143434).sum := by decide
  have hdescent : baseEnd_7143434 < baseStart_7143434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143447 : List Nat := [1, 1, 3, 5, 2, 11]
def baseStart_7143447 : Nat := 118140960795 + 7143447 * 2 ^ 59
def prefixEnd_7143447 : Nat := 4983230072969 + 3 ^ 40 * 7143447 * 2
def baseEnd_7143447 : Nat := 15094740086083201499837

theorem tailTrace_7143447 : CollatzResearch.WordTrace tailWord_7143447 prefixEnd_7143447 15094740086083201499837 := by
  unfold tailWord_7143447
  simp only [CollatzResearch.WordTrace]
  refine ⟨260542916551518997463260595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173695277701012664975507063 260542916551518997463260595)
  ·
    refine ⟨390814374827278496194890893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260542916551518997463260595 390814374827278496194890893)
    ·
      refine ⟨146555390560229436073084085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390814374827278496194890893 146555390560229436073084085)
      ·
        refine ⟨13739567865021509631851633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146555390560229436073084085 13739567865021509631851633)
        ·
          refine ⟨10304675898766132223888725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13739567865021509631851633 10304675898766132223888725)
          ·
            refine ⟨15094740086083201499837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10304675898766132223888725 15094740086083201499837)
            ·
              rfl

theorem cell23_7143447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 11].length) (baseStart_7143447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143447 prefixEnd_7143447 := by exact prefixLift 7143447
  have htrace : WordTrace (prefixWord ++ tailWord_7143447) baseStart_7143447 baseEnd_7143447 := by
    simpa [prefixWord, tailWord_7143447, baseEnd_7143447] using wordTrace_append hprefix tailTrace_7143447
  have hstable : (prefixWord ++ tailWord_7143447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143447).length < 2 ^ (prefixWord ++ tailWord_7143447).sum := by decide
  have hdescent : baseEnd_7143447 < baseStart_7143447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143474 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_7143474 : Nat := 118140960795 + 7143474 * 2 ^ 59
def prefixEnd_7143474 : Nat := 4983230072969 + 3 ^ 40 * 7143474 * 2
def baseEnd_7143474 : Nat := 3668035704895889358822767

theorem tailTrace_7143474 : CollatzResearch.WordTrace tailWord_7143474 prefixEnd_7143474 3668035704895889358822767 := by
  unfold tailWord_7143474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65135975330605295268623369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173695934214947454049662317 65135975330605295268623369)
  ·
    refine ⟨48851981497953971451467527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65135975330605295268623369 48851981497953971451467527)
    ·
      refine ⟨73277972246930957177201291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48851981497953971451467527 73277972246930957177201291)
      ·
        refine ⟨109916958370396435765801937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73277972246930957177201291 109916958370396435765801937)
        ·
          refine ⟨82437718777797326824351453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109916958370396435765801937 82437718777797326824351453)
          ·
            refine ⟨30914144541673997559131795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82437718777797326824351453 30914144541673997559131795)
            ·
              refine ⟨46371216812510996338697693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30914144541673997559131795 46371216812510996338697693)
              ·
                refine ⟨17389206304691623627011635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46371216812510996338697693 17389206304691623627011635)
                ·
                  refine ⟨26083809457037435440517453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17389206304691623627011635 26083809457037435440517453)
                  ·
                    refine ⟨9781428546389038290194045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26083809457037435440517453 9781428546389038290194045)
                    ·
                      refine ⟨3668035704895889358822767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9781428546389038290194045 3668035704895889358822767)
                      ·
                        rfl

theorem cell23_7143474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_7143474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143474 prefixEnd_7143474 := by exact prefixLift 7143474
  have htrace : WordTrace (prefixWord ++ tailWord_7143474) baseStart_7143474 baseEnd_7143474 := by
    simpa [prefixWord, tailWord_7143474, baseEnd_7143474] using wordTrace_append hprefix tailTrace_7143474
  have hstable : (prefixWord ++ tailWord_7143474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143474).length < 2 ^ (prefixWord ++ tailWord_7143474).sum := by decide
  have hdescent : baseEnd_7143474 < baseStart_7143474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143534 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7143534 : Nat := 118140960795 + 7143534 * 2 ^ 59
def prefixEnd_7143534 : Nat := 4983230072969 + 3 ^ 40 * 7143534 * 2
def baseEnd_7143534 : Nat := 3668066513735159124072491

theorem tailTrace_7143534 : CollatzResearch.WordTrace tailWord_7143534 prefixEnd_7143534 3668066513735159124072491 := by
  unfold tailWord_7143534
  simp only [CollatzResearch.WordTrace]
  refine ⟨32568261212775476415209707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173697393134802540881118437 32568261212775476415209707)
  ·
    refine ⟨48852391819163214622814561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32568261212775476415209707 48852391819163214622814561)
    ·
      refine ⟨36639293864372410967110921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48852391819163214622814561 36639293864372410967110921)
      ·
        refine ⟨27479470398279308225333191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36639293864372410967110921 27479470398279308225333191)
        ·
          refine ⟨41219205597418962337999787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27479470398279308225333191 41219205597418962337999787)
          ·
            refine ⟨61828808396128443506999681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41219205597418962337999787 61828808396128443506999681)
            ·
              refine ⟨46371606297096332630249761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61828808396128443506999681 46371606297096332630249761)
              ·
                refine ⟨34778704722822249472687321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46371606297096332630249761 34778704722822249472687321)
                ·
                  refine ⟨26084028542116687104515491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34778704722822249472687321 26084028542116687104515491)
                  ·
                    refine ⟨39126042813175030656773237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26084028542116687104515491 39126042813175030656773237)
                    ·
                      refine ⟨3668066513735159124072491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39126042813175030656773237 3668066513735159124072491)
                      ·
                        rfl

theorem cell23_7143534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7143534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143534 prefixEnd_7143534 := by exact prefixLift 7143534
  have htrace : WordTrace (prefixWord ++ tailWord_7143534) baseStart_7143534 baseEnd_7143534 := by
    simpa [prefixWord, tailWord_7143534, baseEnd_7143534] using wordTrace_append hprefix tailTrace_7143534
  have hstable : (prefixWord ++ tailWord_7143534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143534).length < 2 ^ (prefixWord ++ tailWord_7143534).sum := by decide
  have hdescent : baseEnd_7143534 < baseStart_7143534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143537 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 7]
def baseStart_7143537 : Nat := 118140960795 + 7143537 * 2 ^ 59
def prefixEnd_7143537 : Nat := 4983230072969 + 3 ^ 40 * 7143537 * 2
def baseEnd_7143537 : Nat := 407563117130791401370553

theorem tailTrace_7143537 : CollatzResearch.WordTrace tailWord_7143537 prefixEnd_7143537 407563117130791401370553 := by
  unfold tailWord_7143537
  simp only [CollatzResearch.WordTrace]
  refine ⟨260546199121192942834036865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173697466080795295222691243 260546199121192942834036865)
  ·
    refine ⟨195409649340894707125527649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260546199121192942834036865 195409649340894707125527649)
    ·
      refine ⟨146557237005671030344145737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195409649340894707125527649 146557237005671030344145737)
      ·
        refine ⟨109917927754253272758109303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146557237005671030344145737 109917927754253272758109303)
        ·
          refine ⟨164876891631379909137163955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109917927754253272758109303 164876891631379909137163955)
          ·
            refine ⟨247315337447069863705745933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164876891631379909137163955 247315337447069863705745933)
            ·
              refine ⟨92743251542651198889654725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247315337447069863705745933 92743251542651198889654725)
              ·
                refine ⟨17389359664247099791810261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92743251542651198889654725 17389359664247099791810261)
                ·
                  refine ⟨407563117130791401370553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17389359664247099791810261 407563117130791401370553)
                  ·
                    rfl

theorem cell23_7143537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_7143537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143537 prefixEnd_7143537 := by exact prefixLift 7143537
  have htrace : WordTrace (prefixWord ++ tailWord_7143537) baseStart_7143537 baseEnd_7143537 := by
    simpa [prefixWord, tailWord_7143537, baseEnd_7143537] using wordTrace_append hprefix tailTrace_7143537
  have hstable : (prefixWord ++ tailWord_7143537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143537).length < 2 ^ (prefixWord ++ tailWord_7143537).sum := by decide
  have hdescent : baseEnd_7143537 < baseStart_7143537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143582 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_7143582 : Nat := 118140960795 + 7143582 * 2 ^ 59
def prefixEnd_7143582 : Nat := 4983230072969 + 3 ^ 40 * 7143582 * 2
def baseEnd_7143582 : Nat := 3668091160806574936272271

theorem tailTrace_7143582 : CollatzResearch.WordTrace tailWord_7143582 prefixEnd_7143582 3668091160806574936272271 := by
  unfold tailWord_7143582
  simp only [CollatzResearch.WordTrace]
  refine ⟨32568480050753739439928125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173698560270686610346283333 32568480050753739439928125)
  ·
    refine ⟨12213180019032652289973047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32568480050753739439928125 12213180019032652289973047)
    ·
      refine ⟨18319770028548978434959571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12213180019032652289973047 18319770028548978434959571)
      ·
        refine ⟨27479655042823467652439357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18319770028548978434959571 27479655042823467652439357)
        ·
          refine ⟨10304870641058800369664759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27479655042823467652439357 10304870641058800369664759)
          ·
            refine ⟨15457305961588200554497139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10304870641058800369664759 15457305961588200554497139)
            ·
              refine ⟨23185958942382300831745709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15457305961588200554497139 23185958942382300831745709)
              ·
                refine ⟨8694734603393362811904641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23185958942382300831745709 8694734603393362811904641)
                ·
                  refine ⟨6521050952545022108928481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8694734603393362811904641 6521050952545022108928481)
                  ·
                    refine ⟨4890788214408766581696361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6521050952545022108928481 4890788214408766581696361)
                    ·
                      refine ⟨3668091160806574936272271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4890788214408766581696361 3668091160806574936272271)
                      ·
                        rfl

theorem cell23_7143582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_7143582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143582 prefixEnd_7143582 := by exact prefixLift 7143582
  have htrace : WordTrace (prefixWord ++ tailWord_7143582) baseStart_7143582 baseEnd_7143582 := by
    simpa [prefixWord, tailWord_7143582, baseEnd_7143582] using wordTrace_append hprefix tailTrace_7143582
  have hstable : (prefixWord ++ tailWord_7143582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143582).length < 2 ^ (prefixWord ++ tailWord_7143582).sum := by decide
  have hdescent : baseEnd_7143582 < baseStart_7143582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143624 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_7143624 : Nat := 118140960795 + 7143624 * 2 ^ 59
def prefixEnd_7143624 : Nat := 4983230072969 + 3 ^ 40 * 7143624 * 2
def baseEnd_7143624 : Nat := 3668112726994063771947077

theorem tailTrace_7143624 : CollatzResearch.WordTrace tailWord_7143624 prefixEnd_7143624 3668112726994063771947077 := by
  unfold tailWord_7143624
  simp only [CollatzResearch.WordTrace]
  refine ⟨130274686135938878346226963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173699581514585171128302617 130274686135938878346226963)
  ·
    refine ⟨195412029203908317519340445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130274686135938878346226963 195412029203908317519340445)
    ·
      refine ⟨73279510951465619069752667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195412029203908317519340445 73279510951465619069752667)
      ·
        refine ⟨109919266427198428604629001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73279510951465619069752667 109919266427198428604629001)
        ·
          refine ⟨82439449820398821453471751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109919266427198428604629001 82439449820398821453471751)
          ·
            refine ⟨123659174730598232180207627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82439449820398821453471751 123659174730598232180207627)
            ·
              refine ⟨185488762095897348270311441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123659174730598232180207627 185488762095897348270311441)
              ·
                refine ⟨139116571571923011202733581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185488762095897348270311441 139116571571923011202733581)
                ·
                  refine ⟨52168714339471129201025093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139116571571923011202733581 52168714339471129201025093)
                  ·
                    refine ⟨9781633938650836725192205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52168714339471129201025093 9781633938650836725192205)
                    ·
                      refine ⟨3668112726994063771947077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9781633938650836725192205 3668112726994063771947077)
                      ·
                        rfl

theorem cell23_7143624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_7143624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143624 prefixEnd_7143624 := by exact prefixLift 7143624
  have htrace : WordTrace (prefixWord ++ tailWord_7143624) baseStart_7143624 baseEnd_7143624 := by
    simpa [prefixWord, tailWord_7143624, baseEnd_7143624] using wordTrace_append hprefix tailTrace_7143624
  have hstable : (prefixWord ++ tailWord_7143624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143624).length < 2 ^ (prefixWord ++ tailWord_7143624).sum := by decide
  have hdescent : baseEnd_7143624 < baseStart_7143624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143688 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_7143688 : Nat := 118140960795 + 7143688 * 2 ^ 59
def prefixEnd_7143688 : Nat := 4983230072969 + 3 ^ 40 * 7143688 * 2
def baseEnd_7143688 : Nat := 3668145589755951521546783

theorem tailTrace_7143688 : CollatzResearch.WordTrace tailWord_7143688 prefixEnd_7143688 3668145589755951521546783 := by
  unfold tailWord_7143688
  simp only [CollatzResearch.WordTrace]
  refine ⟨130275853271822947811391859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173701137695763930415189145 130275853271822947811391859)
  ·
    refine ⟨195413779907734421717087789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130275853271822947811391859 195413779907734421717087789)
    ·
      refine ⟨73280167465400408143907921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195413779907734421717087789 73280167465400408143907921)
      ·
        refine ⟨54960125599050306107930941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73280167465400408143907921 54960125599050306107930941)
        ·
          refine ⟨20610047099643864790474103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54960125599050306107930941 20610047099643864790474103)
          ·
            refine ⟨30915070649465797185711155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20610047099643864790474103 30915070649465797185711155)
            ·
              refine ⟨46372605974198695778566733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30915070649465797185711155 46372605974198695778566733)
              ·
                refine ⟨17389727240324510916962525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46372605974198695778566733 17389727240324510916962525)
                ·
                  refine ⟨6521147715121691593860947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17389727240324510916962525 6521147715121691593860947)
                  ·
                    refine ⟨9781721572682537390791421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6521147715121691593860947 9781721572682537390791421)
                    ·
                      refine ⟨3668145589755951521546783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9781721572682537390791421 3668145589755951521546783)
                      ·
                        rfl

theorem cell23_7143688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_7143688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143688 prefixEnd_7143688 := by exact prefixLift 7143688
  have htrace : WordTrace (prefixWord ++ tailWord_7143688) baseStart_7143688 baseEnd_7143688 := by
    simpa [prefixWord, tailWord_7143688, baseEnd_7143688] using wordTrace_append hprefix tailTrace_7143688
  have hstable : (prefixWord ++ tailWord_7143688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143688).length < 2 ^ (prefixWord ++ tailWord_7143688).sum := by decide
  have hdescent : baseEnd_7143688 < baseStart_7143688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143731 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 5]
def baseStart_7143731 : Nat := 118140960795 + 7143731 * 2 ^ 59
def prefixEnd_7143731 : Nat := 4983230072969 + 3 ^ 40 * 7143731 * 2
def baseEnd_7143731 : Nat := 3668167669424094853309085

theorem tailTrace_7143731 : CollatzResearch.WordTrace tailWord_7143731 prefixEnd_7143731 3668167669424094853309085 := by
  unfold tailWord_7143731
  simp only [CollatzResearch.WordTrace]
  refine ⟨260553274882490113966599047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173702183254993409311066031 260553274882490113966599047)
  ·
    refine ⟨390829912323735170949898571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260553274882490113966599047 390829912323735170949898571)
    ·
      refine ⟨586244868485602756424847857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390829912323735170949898571 586244868485602756424847857)
      ·
        refine ⟨439683651364202067318635893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586244868485602756424847857 439683651364202067318635893)
        ·
          refine ⟨41220342315393943811122115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 439683651364202067318635893 41220342315393943811122115)
          ·
            refine ⟨61830513473090915716683173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41220342315393943811122115 61830513473090915716683173)
            ·
              refine ⟨11593221276204546696878095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61830513473090915716683173 11593221276204546696878095)
              ·
                refine ⟨17389831914306820045317143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11593221276204546696878095 17389831914306820045317143)
                ·
                  refine ⟨26084747871460230067975715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17389831914306820045317143 26084747871460230067975715)
                  ·
                    refine ⟨39127121807190345101963573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26084747871460230067975715 39127121807190345101963573)
                    ·
                      refine ⟨3668167669424094853309085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39127121807190345101963573 3668167669424094853309085)
                      ·
                        rfl

theorem cell23_7143731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_7143731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143731 prefixEnd_7143731 := by exact prefixLift 7143731
  have htrace : WordTrace (prefixWord ++ tailWord_7143731) baseStart_7143731 baseEnd_7143731 := by
    simpa [prefixWord, tailWord_7143731, baseEnd_7143731] using wordTrace_append hprefix tailTrace_7143731
  have hstable : (prefixWord ++ tailWord_7143731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143731).length < 2 ^ (prefixWord ++ tailWord_7143731).sum := by decide
  have hdescent : baseEnd_7143731 < baseStart_7143731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143778 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7143778 : Nat := 118140960795 + 7143778 * 2 ^ 59
def prefixEnd_7143778 : Nat := 4983230072969 + 3 ^ 40 * 7143778 * 2
def baseEnd_7143778 : Nat := 3668191803014856169421369

theorem tailTrace_7143778 : CollatzResearch.WordTrace tailWord_7143778 prefixEnd_7143778 3668191803014856169421369 := by
  unfold tailWord_7143778
  simp only [CollatzResearch.WordTrace]
  refine ⟨65138747278329960248389997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173703326075546560662373325 65138747278329960248389997)
  ·
    refine ⟨24427030229373735093146249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65138747278329960248389997 24427030229373735093146249)
    ·
      refine ⟨18320272672030301319859687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24427030229373735093146249 18320272672030301319859687)
      ·
        refine ⟨27480409008045451979789531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18320272672030301319859687 27480409008045451979789531)
        ·
          refine ⟨41220613512068177969684297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27480409008045451979789531 41220613512068177969684297)
          ·
            refine ⟨30915460134051133477263223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41220613512068177969684297 30915460134051133477263223)
            ·
              refine ⟨46373190201076700215894835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30915460134051133477263223 46373190201076700215894835)
              ·
                refine ⟨69559785301615050323842253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46373190201076700215894835 69559785301615050323842253)
                ·
                  refine ⟨26084919488105643871440845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69559785301615050323842253 26084919488105643871440845)
                  ·
                    refine ⟨9781844808039616451790317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26084919488105643871440845 9781844808039616451790317)
                    ·
                      refine ⟨3668191803014856169421369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9781844808039616451790317 3668191803014856169421369)
                      ·
                        rfl

theorem cell23_7143778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7143778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143778 prefixEnd_7143778 := by exact prefixLift 7143778
  have htrace : WordTrace (prefixWord ++ tailWord_7143778) baseStart_7143778 baseEnd_7143778 := by
    simpa [prefixWord, tailWord_7143778, baseEnd_7143778] using wordTrace_append hprefix tailTrace_7143778
  have hstable : (prefixWord ++ tailWord_7143778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143778).length < 2 ^ (prefixWord ++ tailWord_7143778).sum := by decide
  have hdescent : baseEnd_7143778 < baseStart_7143778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143830 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7143830 : Nat := 118140960795 + 7143830 * 2 ^ 59
def prefixEnd_7143830 : Nat := 4983230072969 + 3 ^ 40 * 7143830 * 2
def baseEnd_7143830 : Nat := 3668218504008889965971131

theorem tailTrace_7143830 : CollatzResearch.WordTrace tailWord_7143830 prefixEnd_7143830 3668218504008889965971131 := by
  unfold tailWord_7143830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284805356820715867153309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173704590472754302582968629 16284805356820715867153309)
  ·
    refine ⟨6106802008807768450182491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16284805356820715867153309 6106802008807768450182491)
    ·
      refine ⟨9160203013211652675273737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106802008807768450182491 9160203013211652675273737)
      ·
        refine ⟨6870152259908739506455303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9160203013211652675273737 6870152259908739506455303)
        ·
          refine ⟨10305228389863109259682955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870152259908739506455303 10305228389863109259682955)
          ·
            refine ⟨15457842584794663889524433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305228389863109259682955 15457842584794663889524433)
            ·
              refine ⟨11593381938595997917143325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15457842584794663889524433 11593381938595997917143325)
              ·
                refine ⟨4347518226973499218928747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11593381938595997917143325 4347518226973499218928747)
                ·
                  refine ⟨6521277340460248828393121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347518226973499218928747 6521277340460248828393121)
                  ·
                    refine ⟨4890958005345186621294841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6521277340460248828393121 4890958005345186621294841)
                    ·
                      refine ⟨3668218504008889965971131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4890958005345186621294841 3668218504008889965971131)
                      ·
                        rfl

theorem cell23_7143830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7143830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143830 prefixEnd_7143830 := by exact prefixLift 7143830
  have htrace : WordTrace (prefixWord ++ tailWord_7143830) baseStart_7143830 baseEnd_7143830 := by
    simpa [prefixWord, tailWord_7143830, baseEnd_7143830] using wordTrace_append hprefix tailTrace_7143830
  have hstable : (prefixWord ++ tailWord_7143830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143830).length < 2 ^ (prefixWord ++ tailWord_7143830).sum := by decide
  have hdescent : baseEnd_7143830 < baseStart_7143830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143858 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_7143858 : Nat := 118140960795 + 7143858 * 2 ^ 59
def prefixEnd_7143858 : Nat := 4983230072969 + 3 ^ 40 * 7143858 * 2
def baseEnd_7143858 : Nat := 407581431274135095157889

theorem tailTrace_7143858 : CollatzResearch.WordTrace tailWord_7143858 prefixEnd_7143858 407581431274135095157889 := by
  unfold tailWord_7143858
  simp only [CollatzResearch.WordTrace]
  refine ⟨65139476738257503664118057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173705271302020009770981485 65139476738257503664118057)
  ·
    refine ⟨48854607553693127748088543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65139476738257503664118057 48854607553693127748088543)
    ·
      refine ⟨73281911330539691622132815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48854607553693127748088543 73281911330539691622132815)
      ·
        refine ⟨109922866995809537433199223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73281911330539691622132815 109922866995809537433199223)
        ·
          refine ⟨164884300493714306149798835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109922866995809537433199223 164884300493714306149798835)
          ·
            refine ⟨247326450740571459224698253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164884300493714306149798835 247326450740571459224698253)
            ·
              refine ⟨92747419027714297209261845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247326450740571459224698253 92747419027714297209261845)
              ·
                refine ⟨4347535266924107681684149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92747419027714297209261845 4347535266924107681684149)
                ·
                  refine ⟨407581431274135095157889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4347535266924107681684149 407581431274135095157889)
                  ·
                    rfl

theorem cell23_7143858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_7143858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143858 prefixEnd_7143858 := by exact prefixLift 7143858
  have htrace : WordTrace (prefixWord ++ tailWord_7143858) baseStart_7143858 baseEnd_7143858 := by
    simpa [prefixWord, tailWord_7143858, baseEnd_7143858] using wordTrace_append hprefix tailTrace_7143858
  have hstable : (prefixWord ++ tailWord_7143858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143858).length < 2 ^ (prefixWord ++ tailWord_7143858).sum := by decide
  have hdescent : baseEnd_7143858 < baseStart_7143858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143869 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_7143869 : Nat := 118140960795 + 7143869 * 2 ^ 59
def prefixEnd_7143869 : Nat := 4983230072969 + 3 ^ 40 * 7143869 * 2
def baseEnd_7143869 : Nat := 3668238529754415313383451

theorem tailTrace_7143869 : CollatzResearch.WordTrace tailWord_7143869 prefixEnd_7143869 3668238529754415313383451 := by
  unfold tailWord_7143869
  simp only [CollatzResearch.WordTrace]
  refine ⟨260558308155990163535122661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173705538770660109023415107 260558308155990163535122661)
  ·
    refine ⟨48854682779248155662835499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260558308155990163535122661 48854682779248155662835499)
    ·
      refine ⟨73282024168872233494253249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48854682779248155662835499 73282024168872233494253249)
      ·
        refine ⟨54961518126654175120689937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73282024168872233494253249 54961518126654175120689937)
        ·
          refine ⟨41221138594990631340517453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54961518126654175120689937 41221138594990631340517453)
          ·
            refine ⟨15457926973121486752694045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41221138594990631340517453 15457926973121486752694045)
            ·
              refine ⟨5796722614920557532260267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15457926973121486752694045 5796722614920557532260267)
              ·
                refine ⟨8695083922380836298390401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5796722614920557532260267 8695083922380836298390401)
                ·
                  refine ⟨6521312941785627223792801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8695083922380836298390401 6521312941785627223792801)
                  ·
                    refine ⟨4890984706339220417844601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6521312941785627223792801 4890984706339220417844601)
                    ·
                      refine ⟨3668238529754415313383451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4890984706339220417844601 3668238529754415313383451)
                      ·
                        rfl

theorem cell23_7143869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_7143869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143869 prefixEnd_7143869 := by exact prefixLift 7143869
  have htrace : WordTrace (prefixWord ++ tailWord_7143869) baseStart_7143869 baseEnd_7143869 := by
    simpa [prefixWord, tailWord_7143869, baseEnd_7143869] using wordTrace_append hprefix tailTrace_7143869
  have hstable : (prefixWord ++ tailWord_7143869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143869).length < 2 ^ (prefixWord ++ tailWord_7143869).sum := by decide
  have hdescent : baseEnd_7143869 < baseStart_7143869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143892 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 5]
def baseStart_7143892 : Nat := 118140960795 + 7143892 * 2 ^ 59
def prefixEnd_7143892 : Nat := 4983230072969 + 3 ^ 40 * 7143892 * 2
def baseEnd_7143892 : Nat := 407583371089940969266205

theorem tailTrace_7143892 : CollatzResearch.WordTrace tailWord_7143892 prefixEnd_7143892 407583371089940969266205 := by
  unfold tailWord_7143892
  simp only [CollatzResearch.WordTrace]
  refine ⟨130279573517453419231604965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173706098023271225642139953 130279573517453419231604965)
  ·
    refine ⟨24427420034522516105925931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130279573517453419231604965 24427420034522516105925931)
    ·
      refine ⟨36641130051783774158888897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24427420034522516105925931 36641130051783774158888897)
      ·
        refine ⟨27480847538837830619166673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36641130051783774158888897 27480847538837830619166673)
        ·
          refine ⟨20610635654128372964375005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27480847538837830619166673 20610635654128372964375005)
          ·
            refine ⟨7728988370298139861640627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20610635654128372964375005 7728988370298139861640627)
            ·
              refine ⟨11593482555447209792460941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728988370298139861640627 11593482555447209792460941)
              ·
                refine ⟨4347555958292703672172853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11593482555447209792460941 4347555958292703672172853)
                ·
                  refine ⟨407583371089940969266205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4347555958292703672172853 407583371089940969266205)
                  ·
                    rfl

theorem cell23_7143892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_7143892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143892 prefixEnd_7143892 := by exact prefixLift 7143892
  have htrace : WordTrace (prefixWord ++ tailWord_7143892) baseStart_7143892 baseEnd_7143892 := by
    simpa [prefixWord, tailWord_7143892, baseEnd_7143892] using wordTrace_append hprefix tailTrace_7143892
  have hstable : (prefixWord ++ tailWord_7143892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143892).length < 2 ^ (prefixWord ++ tailWord_7143892).sum := by decide
  have hdescent : baseEnd_7143892 < baseStart_7143892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143928 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_7143928 : Nat := 118140960795 + 7143928 * 2 ^ 59
def prefixEnd_7143928 : Nat := 4983230072969 + 3 ^ 40 * 7143928 * 2
def baseEnd_7143928 : Nat := 3668268825113030582545679

theorem tailTrace_7143928 : CollatzResearch.WordTrace tailWord_7143928 prefixEnd_7143928 3668268825113030582545679 := by
  unfold tailWord_7143928
  simp only [CollatzResearch.WordTrace]
  refine ⟨130280230031388208305760219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173706973375184277741013625 130280230031388208305760219)
  ·
    refine ⟨195420345047082312458640329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130280230031388208305760219 195420345047082312458640329)
    ·
      refine ⟨146565258785311734343980247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195420345047082312458640329 146565258785311734343980247)
      ·
        refine ⟨219847888177967601515970371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146565258785311734343980247 219847888177967601515970371)
        ·
          refine ⟨329771832266951402273955557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219847888177967601515970371 329771832266951402273955557)
          ·
            refine ⟨61832218550053387926366667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329771832266951402273955557 61832218550053387926366667)
            ·
              refine ⟨92748327825080081889550001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61832218550053387926366667 92748327825080081889550001)
              ·
                refine ⟨69561245868810061417162501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92748327825080081889550001 69561245868810061417162501)
                ·
                  refine ⟨13042733600401886515717969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69561245868810061417162501 13042733600401886515717969)
                  ·
                    refine ⟨9782050200301414886788477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13042733600401886515717969 9782050200301414886788477)
                    ·
                      refine ⟨3668268825113030582545679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9782050200301414886788477 3668268825113030582545679)
                      ·
                        rfl

theorem cell23_7143928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_7143928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143928 prefixEnd_7143928 := by exact prefixLift 7143928
  have htrace : WordTrace (prefixWord ++ tailWord_7143928) baseStart_7143928 baseEnd_7143928 := by
    simpa [prefixWord, tailWord_7143928, baseEnd_7143928] using wordTrace_append hprefix tailTrace_7143928
  have hstable : (prefixWord ++ tailWord_7143928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143928).length < 2 ^ (prefixWord ++ tailWord_7143928).sum := by decide
  have hdescent : baseEnd_7143928 < baseStart_7143928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143965 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 6]
def baseStart_7143965 : Nat := 118140960795 + 7143965 * 2 ^ 59
def prefixEnd_7143965 : Nat := 4983230072969 + 3 ^ 40 * 7143965 * 2
def baseEnd_7143965 : Nat := 407587535988582993087001

theorem tailTrace_7143965 : CollatzResearch.WordTrace tailWord_7143965 prefixEnd_7143965 407587535988582993087001 := by
  unfold tailWord_7143965
  simp only [CollatzResearch.WordTrace]
  refine ⟨260561809563642371930617349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173707873042428247953744899 260561809563642371930617349)
  ·
    refine ⟨48855339293182944736990753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260561809563642371930617349 48855339293182944736990753)
    ·
      refine ⟨36641504469887208552743065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48855339293182944736990753 36641504469887208552743065)
      ·
        refine ⟨27481128352415406414557299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36641504469887208552743065 27481128352415406414557299)
        ·
          refine ⟨41221692528623109621835949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27481128352415406414557299 41221692528623109621835949)
          ·
            refine ⟨15458134698233666108188481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41221692528623109621835949 15458134698233666108188481)
            ·
              refine ⟨11593601023675249581141361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15458134698233666108188481 11593601023675249581141361)
              ·
                refine ⟨8695200767756437185856021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11593601023675249581141361 8695200767756437185856021)
                ·
                  refine ⟨407587535988582993087001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8695200767756437185856021 407587535988582993087001)
                  ·
                    rfl

theorem cell23_7143965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_7143965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143965 prefixEnd_7143965 := by exact prefixLift 7143965
  have htrace : WordTrace (prefixWord ++ tailWord_7143965) baseStart_7143965 baseEnd_7143965 := by
    simpa [prefixWord, tailWord_7143965, baseEnd_7143965] using wordTrace_append hprefix tailTrace_7143965
  have hstable : (prefixWord ++ tailWord_7143965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143965).length < 2 ^ (prefixWord ++ tailWord_7143965).sum := by decide
  have hdescent : baseEnd_7143965 < baseStart_7143965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7143985 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 4, 3, 2]
def baseStart_7143985 : Nat := 118140960795 + 7143985 * 2 ^ 59
def prefixEnd_7143985 : Nat := 4983230072969 + 3 ^ 40 * 7143985 * 2
def baseEnd_7143985 : Nat := 3668298093510336859532917

theorem tailTrace_7143985 : CollatzResearch.WordTrace tailWord_7143985 prefixEnd_7143985 3668298093510336859532917 := by
  unfold tailWord_7143985
  simp only [CollatzResearch.WordTrace]
  refine ⟨260562539023569915346345409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173708359349046610230896939 260562539023569915346345409)
  ·
    refine ⟨195421904267677436509759057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260562539023569915346345409 195421904267677436509759057)
    ·
      refine ⟨146566428200758077382319293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195421904267677436509759057 146566428200758077382319293)
      ·
        refine ⟨54962410575284279018369735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146566428200758077382319293 54962410575284279018369735)
        ·
          refine ⟨82443615862926418527554603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54962410575284279018369735 82443615862926418527554603)
          ·
            refine ⟨123665423794389627791331905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82443615862926418527554603 123665423794389627791331905)
            ·
              refine ⟨92749067845792220843498929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123665423794389627791331905 92749067845792220843498929)
              ·
                refine ⟨69561800884344165632624197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92749067845792220843498929 69561800884344165632624197)
                ·
                  refine ⟨13042837665814531056117037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69561800884344165632624197 13042837665814531056117037)
                  ·
                    refine ⟨4891064124680449146043889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13042837665814531056117037 4891064124680449146043889)
                    ·
                      refine ⟨3668298093510336859532917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891064124680449146043889 3668298093510336859532917)
                      ·
                        rfl

theorem cell23_7143985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_7143985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7143985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7143985 prefixEnd_7143985 := by exact prefixLift 7143985
  have htrace : WordTrace (prefixWord ++ tailWord_7143985) baseStart_7143985 baseEnd_7143985 := by
    simpa [prefixWord, tailWord_7143985, baseEnd_7143985] using wordTrace_append hprefix tailTrace_7143985
  have hstable : (prefixWord ++ tailWord_7143985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7143985).length < 2 ^ (prefixWord ++ tailWord_7143985).sum := by decide
  have hdescent : baseEnd_7143985 < baseStart_7143985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7143985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144032 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 3, 2, 2]
def baseStart_7144032 : Nat := 118140960795 + 7144032 * 2 ^ 59
def prefixEnd_7144032 : Nat := 4983230072969 + 3 ^ 40 * 7144032 * 2
def baseEnd_7144032 : Nat := 3668322227101098175645201

theorem tailTrace_7144032 : CollatzResearch.WordTrace tailWord_7144032 prefixEnd_7144032 3668322227101098175645201 := by
  unfold tailWord_7144032
  simp only [CollatzResearch.WordTrace]
  refine ⟨130282126627199821186653175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173709502169599761582204233 130282126627199821186653175)
  ·
    refine ⟨195423189940799731779979763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130282126627199821186653175 195423189940799731779979763)
    ·
      refine ⟨293134784911199597669969645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195423189940799731779979763 293134784911199597669969645)
      ·
        refine ⟨109925544341699849126238617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293134784911199597669969645 109925544341699849126238617)
        ·
          refine ⟨82444158256274886844678963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109925544341699849126238617 82444158256274886844678963)
          ·
            refine ⟨123666237384412330267018445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82444158256274886844678963 123666237384412330267018445)
            ·
              refine ⟨46374839019154623850131917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123666237384412330267018445 46374839019154623850131917)
              ·
                refine ⟨17390564632182983943799469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46374839019154623850131917 17390564632182983943799469)
                ·
                  refine ⟨6521461737068618978924801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17390564632182983943799469 6521461737068618978924801)
                  ·
                    refine ⟨4891096302801464234193601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6521461737068618978924801 4891096302801464234193601)
                    ·
                      refine ⟨3668322227101098175645201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891096302801464234193601 3668322227101098175645201)
                      ·
                        rfl

theorem cell23_7144032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_7144032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144032 prefixEnd_7144032 := by exact prefixLift 7144032
  have htrace : WordTrace (prefixWord ++ tailWord_7144032) baseStart_7144032 baseEnd_7144032 := by
    simpa [prefixWord, tailWord_7144032, baseEnd_7144032] using wordTrace_append hprefix tailTrace_7144032
  have hstable : (prefixWord ++ tailWord_7144032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144032).length < 2 ^ (prefixWord ++ tailWord_7144032).sum := by decide
  have hdescent : baseEnd_7144032 < baseStart_7144032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144045 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7144045 : Nat := 118140960795 + 7144045 * 2 ^ 59
def prefixEnd_7144045 : Nat := 4983230072969 + 3 ^ 40 * 7144045 * 2
def baseEnd_7144045 : Nat := 3668328902349606624782641

theorem tailTrace_7144045 : CollatzResearch.WordTrace tailWord_7144045 prefixEnd_7144045 3668328902349606624782641 := by
  unfold tailWord_7144045
  simp only [CollatzResearch.WordTrace]
  refine ⟨260564727403352545593529589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173709818268901697062353059 260564727403352545593529589)
  ·
    refine ⟨24427943194064301149393399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260564727403352545593529589 24427943194064301149393399)
    ·
      refine ⟨36641914791096451724090099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24427943194064301149393399 36641914791096451724090099)
      ·
        refine ⟨54962872186644677586135149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36641914791096451724090099 54962872186644677586135149)
        ·
          refine ⟨20611077069991754094800681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54962872186644677586135149 20611077069991754094800681)
          ·
            refine ⟨15458307802493815571100511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20611077069991754094800681 15458307802493815571100511)
            ·
              refine ⟨23187461703740723356650767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15458307802493815571100511 23187461703740723356650767)
              ·
                refine ⟨34781192555611085034976151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23187461703740723356650767 34781192555611085034976151)
                ·
                  refine ⟨52171788833416627552464227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34781192555611085034976151 52171788833416627552464227)
                  ·
                    refine ⟨78257683250124941328696341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52171788833416627552464227 78257683250124941328696341)
                    ·
                      refine ⟨3668328902349606624782641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78257683250124941328696341 3668328902349606624782641)
                      ·
                        rfl

theorem cell23_7144045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7144045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144045 prefixEnd_7144045 := by exact prefixLift 7144045
  have htrace : WordTrace (prefixWord ++ tailWord_7144045) baseStart_7144045 baseEnd_7144045 := by
    simpa [prefixWord, tailWord_7144045, baseEnd_7144045] using wordTrace_append hprefix tailTrace_7144045
  have hstable : (prefixWord ++ tailWord_7144045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144045).length < 2 ^ (prefixWord ++ tailWord_7144045).sum := by decide
  have hdescent : baseEnd_7144045 < baseStart_7144045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144065 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_7144065 : Nat := 118140960795 + 7144065 * 2 ^ 59
def prefixEnd_7144065 : Nat := 4983230072969 + 3 ^ 40 * 7144065 * 2
def baseEnd_7144065 : Nat := 3668339171962696546532549

theorem tailTrace_7144065 : CollatzResearch.WordTrace tailWord_7144065 prefixEnd_7144065 3668339171962696546532549 := by
  unfold tailWord_7144065
  simp only [CollatzResearch.WordTrace]
  refine ⟨260565456863280089009257649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173710304575520059339505099 260565456863280089009257649)
  ·
    refine ⟨195424092647460066756943237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260565456863280089009257649 195424092647460066756943237)
    ·
      refine ⟨36642017371398762516926857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195424092647460066756943237 36642017371398762516926857)
      ·
        refine ⟨27481513028549071887695143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36642017371398762516926857 27481513028549071887695143)
        ·
          refine ⟨41222269542823607831542715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27481513028549071887695143 41222269542823607831542715)
          ·
            refine ⟨61833404314235411747314073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41222269542823607831542715 61833404314235411747314073)
            ·
              refine ⟨46375053235676558810485555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61833404314235411747314073 46375053235676558810485555)
              ·
                refine ⟨69562579853514838215728333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46375053235676558810485555 69562579853514838215728333)
                ·
                  refine ⟨26085967445068064330898125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69562579853514838215728333 26085967445068064330898125)
                  ·
                    refine ⟨9782237791900524124086797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26085967445068064330898125 9782237791900524124086797)
                    ·
                      refine ⟨3668339171962696546532549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9782237791900524124086797 3668339171962696546532549)
                      ·
                        rfl

theorem cell23_7144065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_7144065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144065 prefixEnd_7144065 := by exact prefixLift 7144065
  have htrace : WordTrace (prefixWord ++ tailWord_7144065) baseStart_7144065 baseEnd_7144065 := by
    simpa [prefixWord, tailWord_7144065, baseEnd_7144065] using wordTrace_append hprefix tailTrace_7144065
  have hstable : (prefixWord ++ tailWord_7144065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144065).length < 2 ^ (prefixWord ++ tailWord_7144065).sum := by decide
  have hdescent : baseEnd_7144065 < baseStart_7144065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144103 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7144103 : Nat := 118140960795 + 7144103 * 2 ^ 59
def prefixEnd_7144103 : Nat := 4983230072969 + 3 ^ 40 * 7144103 * 2
def baseEnd_7144103 : Nat := 3668358684227567397857375

theorem tailTrace_7144103 : CollatzResearch.WordTrace tailWord_7144103 prefixEnd_7144103 3668358684227567397857375 := by
  unfold tailWord_7144103
  simp only [CollatzResearch.WordTrace]
  refine ⟨260566842837142421499140963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173711228558094947666093975 260566842837142421499140963)
  ·
    refine ⟨390850264255713632248711445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260566842837142421499140963 390850264255713632248711445)
    ·
      refine ⟨18321106136986576511658349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 390850264255713632248711445 18321106136986576511658349)
      ·
        refine ⟨6870414801369966191871881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18321106136986576511658349 6870414801369966191871881)
        ·
          refine ⟨5152811101027474643903911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6870414801369966191871881 5152811101027474643903911)
          ·
            refine ⟨7729216651541211965855867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152811101027474643903911 7729216651541211965855867)
            ·
              refine ⟨11593824977311817948783801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729216651541211965855867 11593824977311817948783801)
              ·
                refine ⟨8695368732983863461587851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11593824977311817948783801 8695368732983863461587851)
                ·
                  refine ⟨13043053099475795192381777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8695368732983863461587851 13043053099475795192381777)
                  ·
                    refine ⟨9782289824606846394286333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13043053099475795192381777 9782289824606846394286333)
                    ·
                      refine ⟨3668358684227567397857375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9782289824606846394286333 3668358684227567397857375)
                      ·
                        rfl

theorem cell23_7144103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7144103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144103 prefixEnd_7144103 := by exact prefixLift 7144103
  have htrace : WordTrace (prefixWord ++ tailWord_7144103) baseStart_7144103 baseEnd_7144103 := by
    simpa [prefixWord, tailWord_7144103, baseEnd_7144103] using wordTrace_append hprefix tailTrace_7144103
  have hstable : (prefixWord ++ tailWord_7144103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144103).length < 2 ^ (prefixWord ++ tailWord_7144103).sum := by decide
  have hdescent : baseEnd_7144103 < baseStart_7144103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144109 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7144109 : Nat := 118140960795 + 7144109 * 2 ^ 59
def prefixEnd_7144109 : Nat := 4983230072969 + 3 ^ 40 * 7144109 * 2
def baseEnd_7144109 : Nat := 3668361765111494374382347

theorem tailTrace_7144109 : CollatzResearch.WordTrace tailWord_7144109 prefixEnd_7144109 3668361765111494374382347 := by
  unfold tailWord_7144109
  simp only [CollatzResearch.WordTrace]
  refine ⟨260567061675120684523859381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173711374450080456349239587 260567061675120684523859381)
  ·
    refine ⟨24428162032042564174111817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260567061675120684523859381 24428162032042564174111817)
    ·
      refine ⟨18321121524031923130583863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24428162032042564174111817 18321121524031923130583863)
      ·
        refine ⟨27481682286047884695875795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18321121524031923130583863 27481682286047884695875795)
        ·
          refine ⟨41222523429071827043813693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27481682286047884695875795 41222523429071827043813693)
          ·
            refine ⟨15458446285901935141430135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41222523429071827043813693 15458446285901935141430135)
            ·
              refine ⟨23187669428852902712145203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15458446285901935141430135 23187669428852902712145203)
              ·
                refine ⟨34781504143279354068217805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23187669428852902712145203 34781504143279354068217805)
                ·
                  refine ⟨13043064053729757775581677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34781504143279354068217805 13043064053729757775581677)
                  ·
                    refine ⟨4891149020148659165843129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13043064053729757775581677 4891149020148659165843129)
                    ·
                      refine ⟨3668361765111494374382347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891149020148659165843129 3668361765111494374382347)
                      ·
                        rfl

theorem cell23_7144109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7144109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144109 prefixEnd_7144109 := by exact prefixLift 7144109
  have htrace : WordTrace (prefixWord ++ tailWord_7144109) baseStart_7144109 baseEnd_7144109 := by
    simpa [prefixWord, tailWord_7144109, baseEnd_7144109] using wordTrace_append hprefix tailTrace_7144109
  have hstable : (prefixWord ++ tailWord_7144109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144109).length < 2 ^ (prefixWord ++ tailWord_7144109).sum := by decide
  have hdescent : baseEnd_7144109 < baseStart_7144109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144122 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2]
def baseStart_7144122 : Nat := 118140960795 + 7144122 * 2 ^ 59
def prefixEnd_7144122 : Nat := 4983230072969 + 3 ^ 40 * 7144122 * 2
def baseEnd_7144122 : Nat := 3668368440360002823519787

theorem tailTrace_7144122 : CollatzResearch.WordTrace tailWord_7144122 prefixEnd_7144122 3668368440360002823519787 := by
  unfold tailWord_7144122
  simp only [CollatzResearch.WordTrace]
  refine ⟨65141883956018396936020655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173711690549382391829388413 65141883956018396936020655)
  ·
    refine ⟨97712825934027595404030983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65141883956018396936020655 97712825934027595404030983)
    ·
      refine ⟨146569238901041393106046475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97712825934027595404030983 146569238901041393106046475)
      ·
        refine ⟨219853858351562089659069713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146569238901041393106046475 219853858351562089659069713)
        ·
          refine ⟨164890393763671567244302285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219853858351562089659069713 164890393763671567244302285)
          ·
            refine ⟨61833897661376837716613357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164890393763671567244302285 61833897661376837716613357)
            ·
              refine ⟨23187711623016314143730009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61833897661376837716613357 23187711623016314143730009)
              ·
                refine ⟨17390783717262235607797507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23187711623016314143730009 17390783717262235607797507)
                ·
                  refine ⟨26086175575893353411696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17390783717262235607797507 26086175575893353411696261)
                  ·
                    refine ⟨4891157920480003764693049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26086175575893353411696261 4891157920480003764693049)
                    ·
                      refine ⟨3668368440360002823519787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891157920480003764693049 3668368440360002823519787)
                      ·
                        rfl

theorem cell23_7144122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_7144122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144122 prefixEnd_7144122 := by exact prefixLift 7144122
  have htrace : WordTrace (prefixWord ++ tailWord_7144122) baseStart_7144122 baseEnd_7144122 := by
    simpa [prefixWord, tailWord_7144122, baseEnd_7144122] using wordTrace_append hprefix tailTrace_7144122
  have hstable : (prefixWord ++ tailWord_7144122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144122).length < 2 ^ (prefixWord ++ tailWord_7144122).sum := by decide
  have hdescent : baseEnd_7144122 < baseStart_7144122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144125 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_7144125 : Nat := 118140960795 + 7144125 * 2 ^ 59
def prefixEnd_7144125 : Nat := 4983230072969 + 3 ^ 40 * 7144125 * 2
def baseEnd_7144125 : Nat := 3668369980801966311782273

theorem tailTrace_7144125 : CollatzResearch.WordTrace tailWord_7144125 prefixEnd_7144125 3668369980801966311782273 := by
  unfold tailWord_7144125
  simp only [CollatzResearch.WordTrace]
  refine ⟨260567645243062719256441829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173711763495375146170961219 260567645243062719256441829)
  ·
    refine ⟨48856433483074259860582843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260567645243062719256441829 48856433483074259860582843)
    ·
      refine ⟨73284650224611389790874265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48856433483074259860582843 73284650224611389790874265)
      ·
        refine ⟨54963487668458542343155699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73284650224611389790874265 54963487668458542343155699)
        ·
          refine ⟨82445231502687813514733549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54963487668458542343155699 82445231502687813514733549)
          ·
            refine ⟨30916961813507930068025081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82445231502687813514733549 30916961813507930068025081)
            ·
              refine ⟨23187721360130947551018811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30916961813507930068025081 23187721360130947551018811)
              ·
                refine ⟨34781582040196421326528217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23187721360130947551018811 34781582040196421326528217)
                ·
                  refine ⟨26086186530147315994896163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34781582040196421326528217 26086186530147315994896163)
                  ·
                    refine ⟨39129279795220973992344245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26086186530147315994896163 39129279795220973992344245)
                    ·
                      refine ⟨3668369980801966311782273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39129279795220973992344245 3668369980801966311782273)
                      ·
                        rfl

theorem cell23_7144125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_7144125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144125 prefixEnd_7144125 := by exact prefixLift 7144125
  have htrace : WordTrace (prefixWord ++ tailWord_7144125) baseStart_7144125 baseEnd_7144125 := by
    simpa [prefixWord, tailWord_7144125, baseEnd_7144125] using wordTrace_append hprefix tailTrace_7144125
  have hstable : (prefixWord ++ tailWord_7144125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144125).length < 2 ^ (prefixWord ++ tailWord_7144125).sum := by decide
  have hdescent : baseEnd_7144125 < baseStart_7144125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144126 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_7144126 : Nat := 118140960795 + 7144126 * 2 ^ 59
def prefixEnd_7144126 : Nat := 4983230072969 + 3 ^ 40 * 7144126 * 2
def baseEnd_7144126 : Nat := 3668370494282620807869769

theorem tailTrace_7144126 : CollatzResearch.WordTrace tailWord_7144126 prefixEnd_7144126 3668370494282620807869769 := by
  unfold tailWord_7144126
  simp only [CollatzResearch.WordTrace]
  refine ⟨32570960214507387053403529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173711787810706064284818821 32570960214507387053403529)
  ·
    refine ⟨24428220160880540290052647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32570960214507387053403529 24428220160880540290052647)
    ·
      refine ⟨36642330241320810435078971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24428220160880540290052647 36642330241320810435078971)
      ·
        refine ⟨54963495361981215652618457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36642330241320810435078971 54963495361981215652618457)
        ·
          refine ⟨41222621521485911739463843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54963495361981215652618457 41222621521485911739463843)
          ·
            refine ⟨61833932282228867609195765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41222621521485911739463843 61833932282228867609195765)
            ·
              refine ⟨5796931151458956338362103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61833932282228867609195765 5796931151458956338362103)
              ·
                refine ⟨8695396727188434507543155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5796931151458956338362103 8695396727188434507543155)
                ·
                  refine ⟨13043095090782651761314733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8695396727188434507543155 13043095090782651761314733)
                  ·
                    refine ⟨4891160659043494410493025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13043095090782651761314733 4891160659043494410493025)
                    ·
                      refine ⟨3668370494282620807869769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891160659043494410493025 3668370494282620807869769)
                      ·
                        rfl

theorem cell23_7144126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_7144126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144126 prefixEnd_7144126 := by exact prefixLift 7144126
  have htrace : WordTrace (prefixWord ++ tailWord_7144126) baseStart_7144126 baseEnd_7144126 := by
    simpa [prefixWord, tailWord_7144126, baseEnd_7144126] using wordTrace_append hprefix tailTrace_7144126
  have hstable : (prefixWord ++ tailWord_7144126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144126).length < 2 ^ (prefixWord ++ tailWord_7144126).sum := by decide
  have hdescent : baseEnd_7144126 < baseStart_7144126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144134 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7144134 : Nat := 118140960795 + 7144134 * 2 ^ 59
def prefixEnd_7144134 : Nat := 4983230072969 + 3 ^ 40 * 7144134 * 2
def baseEnd_7144134 : Nat := 3668374602127856776569733

theorem tailTrace_7144134 : CollatzResearch.WordTrace tailWord_7144134 prefixEnd_7144134 3668374602127856776569733 := by
  unfold tailWord_7144134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142749171875941056047483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173711982333353409195679637 8142749171875941056047483)
  ·
    refine ⟨12214123757813911584071225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8142749171875941056047483 12214123757813911584071225)
    ·
      refine ⟨9160592818360433688053419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12214123757813911584071225 9160592818360433688053419)
      ·
        refine ⟨13740889227540650532080129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9160592818360433688053419 13740889227540650532080129)
        ·
          refine ⟨10305666920655487899060097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13740889227540650532080129 10305666920655487899060097)
          ·
            refine ⟨7729250190491615924295073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305666920655487899060097 7729250190491615924295073)
            ·
              refine ⟨5796937642868711943221305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7729250190491615924295073 5796937642868711943221305)
              ·
                refine ⟨4347703232151533957415979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796937642868711943221305 4347703232151533957415979)
                ·
                  refine ⟨6521554848227300936123969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347703232151533957415979 6521554848227300936123969)
                  ·
                    refine ⟨4891166136170475702092977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6521554848227300936123969 4891166136170475702092977)
                    ·
                      refine ⟨3668374602127856776569733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891166136170475702092977 3668374602127856776569733)
                      ·
                        rfl

theorem cell23_7144134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7144134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144134 prefixEnd_7144134 := by exact prefixLift 7144134
  have htrace : WordTrace (prefixWord ++ tailWord_7144134) baseStart_7144134 baseEnd_7144134 := by
    simpa [prefixWord, tailWord_7144134, baseEnd_7144134] using wordTrace_append hprefix tailTrace_7144134
  have hstable : (prefixWord ++ tailWord_7144134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144134).length < 2 ^ (prefixWord ++ tailWord_7144134).sum := by decide
  have hdescent : baseEnd_7144134 < baseStart_7144134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144156 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7144156 : Nat := 118140960795 + 7144156 * 2 ^ 59
def prefixEnd_7144156 : Nat := 4983230072969 + 3 ^ 40 * 7144156 * 2
def baseEnd_7144156 : Nat := 3668385898702255690494631

theorem tailTrace_7144156 : CollatzResearch.WordTrace tailWord_7144156 prefixEnd_7144156 3668385898702255690494631 := by
  unfold tailWord_7144156
  simp only [CollatzResearch.WordTrace]
  refine ⟨130284387952975205775410161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173712517270633607700546881 130284387952975205775410161)
  ·
    refine ⟨97713290964731404331557621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130284387952975205775410161 97713290964731404331557621)
    ·
      refine ⟨9160621027943569156083527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97713290964731404331557621 9160621027943569156083527)
      ·
        refine ⟨13740931541915353734125291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9160621027943569156083527 13740931541915353734125291)
        ·
          refine ⟨20611397312873030601187937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13740931541915353734125291 20611397312873030601187937)
          ·
            refine ⟨15458547984654772950890953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20611397312873030601187937 15458547984654772950890953)
            ·
              refine ⟨11593910988491079713168215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15458547984654772950890953 11593910988491079713168215)
              ·
                refine ⟨17390866482736619569752323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11593910988491079713168215 17390866482736619569752323)
                ·
                  refine ⟨26086299724104929354628485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17390866482736619569752323 26086299724104929354628485)
                  ·
                    refine ⟨4891181198269674253992841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26086299724104929354628485 4891181198269674253992841)
                    ·
                      refine ⟨3668385898702255690494631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891181198269674253992841 3668385898702255690494631)
                      ·
                        rfl

theorem cell23_7144156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7144156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144156 prefixEnd_7144156 := by exact prefixLift 7144156
  have htrace : WordTrace (prefixWord ++ tailWord_7144156) baseStart_7144156 baseEnd_7144156 := by
    simpa [prefixWord, tailWord_7144156, baseEnd_7144156] using wordTrace_append hprefix tailTrace_7144156
  have hstable : (prefixWord ++ tailWord_7144156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144156).length < 2 ^ (prefixWord ++ tailWord_7144156).sum := by decide
  have hdescent : baseEnd_7144156 < baseStart_7144156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144175 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 1, 7]
def baseStart_7144175 : Nat := 118140960795 + 7144175 * 2 ^ 59
def prefixEnd_7144175 : Nat := 4983230072969 + 3 ^ 40 * 7144175 * 2
def baseEnd_7144175 : Nat := 1222798551611563705385681

theorem tailTrace_7144175 : CollatzResearch.WordTrace tailWord_7144175 prefixEnd_7144175 1222798551611563705385681 := by
  unfold tailWord_7144175
  simp only [CollatzResearch.WordTrace]
  refine ⟨260569468892881577795761979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173712979261921051863841319 260569468892881577795761979)
  ·
    refine ⟨390854203339322366693642969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260569468892881577795761979 390854203339322366693642969)
    ·
      refine ⟨293140652504491775020232227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390854203339322366693642969 293140652504491775020232227)
      ·
        refine ⟨439710978756737662530348341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293140652504491775020232227 439710978756737662530348341)
        ·
          refine ⟨41222904258444155862220157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 439710978756737662530348341 41222904258444155862220157)
          ·
            refine ⟨15458589096916558448332559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41222904258444155862220157 15458589096916558448332559)
            ·
              refine ⟨23187883645374837672498839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15458589096916558448332559 23187883645374837672498839)
              ·
                refine ⟨34781825468062256508748259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23187883645374837672498839 34781825468062256508748259)
                ·
                  refine ⟨52172738202093384763122389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34781825468062256508748259 52172738202093384763122389)
                  ·
                    refine ⟨1222798551611563705385681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52172738202093384763122389 1222798551611563705385681)
                    ·
                      rfl

theorem cell23_7144175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_7144175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144175 prefixEnd_7144175 := by exact prefixLift 7144175
  have htrace : WordTrace (prefixWord ++ tailWord_7144175) baseStart_7144175 baseEnd_7144175 := by
    simpa [prefixWord, tailWord_7144175, baseEnd_7144175] using wordTrace_append hprefix tailTrace_7144175
  have hstable : (prefixWord ++ tailWord_7144175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144175).length < 2 ^ (prefixWord ++ tailWord_7144175).sum := by decide
  have hdescent : baseEnd_7144175 < baseStart_7144175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144195 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 4]
def baseStart_7144195 : Nat := 118140960795 + 7144195 * 2 ^ 59
def prefixEnd_7144195 : Nat := 4983230072969 + 3 ^ 40 * 7144195 * 2
def baseEnd_7144195 : Nat := 3668405924447781037906951

theorem tailTrace_7144195 : CollatzResearch.WordTrace tailWord_7144195 prefixEnd_7144195 3668405924447781037906951 := by
  unfold tailWord_7144195
  simp only [CollatzResearch.WordTrace]
  refine ⟨260570198352809121211490039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173713465568539414140993359 260570198352809121211490039)
  ·
    refine ⟨390855297529213681817235059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260570198352809121211490039 390855297529213681817235059)
    ·
      refine ⟨586282946293820522725852589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390855297529213681817235059 586282946293820522725852589)
      ·
        refine ⟨219856104860182696022194721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586282946293820522725852589 219856104860182696022194721)
        ·
          refine ⟨164892078645137022016646041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219856104860182696022194721 164892078645137022016646041)
          ·
            refine ⟨123669058983852766512484531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164892078645137022016646041 123669058983852766512484531)
            ·
              refine ⟨185503588475779149768726797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123669058983852766512484531 185503588475779149768726797)
              ·
                refine ⟨69563845678417181163272549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185503588475779149768726797 69563845678417181163272549)
                ·
                  refine ⟨13043221064703221468113603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69563845678417181163272549 13043221064703221468113603)
                  ·
                    refine ⟨19564831597054832202170405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13043221064703221468113603 19564831597054832202170405)
                    ·
                      refine ⟨3668405924447781037906951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19564831597054832202170405 3668405924447781037906951)
                      ·
                        rfl

theorem cell23_7144195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_7144195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144195 prefixEnd_7144195 := by exact prefixLift 7144195
  have htrace : WordTrace (prefixWord ++ tailWord_7144195) baseStart_7144195 baseEnd_7144195 := by
    simpa [prefixWord, tailWord_7144195, baseEnd_7144195] using wordTrace_append hprefix tailTrace_7144195
  have hstable : (prefixWord ++ tailWord_7144195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144195).length < 2 ^ (prefixWord ++ tailWord_7144195).sum := by decide
  have hdescent : baseEnd_7144195 < baseStart_7144195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144225 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7144225 : Nat := 118140960795 + 7144225 * 2 ^ 59
def prefixEnd_7144225 : Nat := 4983230072969 + 3 ^ 40 * 7144225 * 2
def baseEnd_7144225 : Nat := 3668421328867415920531813

theorem tailTrace_7144225 : CollatzResearch.WordTrace tailWord_7144225 prefixEnd_7144225 3668421328867415920531813 := by
  unfold tailWord_7144225
  simp only [CollatzResearch.WordTrace]
  refine ⟨260571292542700436335082129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173714195028466957556721419 260571292542700436335082129)
  ·
    refine ⟨195428469407025327251311597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260571292542700436335082129 195428469407025327251311597)
    ·
      refine ⟨73285676027634497719241849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195428469407025327251311597 73285676027634497719241849)
      ·
        refine ⟨54964257020725873289431387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73285676027634497719241849 54964257020725873289431387)
        ·
          refine ⟨82446385531088809934147081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54964257020725873289431387 82446385531088809934147081)
          ·
            refine ⟨61834789148316607450610311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82446385531088809934147081 61834789148316607450610311)
            ·
              refine ⟨92752183722474911175915467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61834789148316607450610311 92752183722474911175915467)
              ·
                refine ⟨139128275583712366763873201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92752183722474911175915467 139128275583712366763873201)
                ·
                  refine ⟨104346206687784275072904901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139128275583712366763873201 104346206687784275072904901)
                  ·
                    refine ⟨19564913753959551576169669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104346206687784275072904901 19564913753959551576169669)
                    ·
                      refine ⟨3668421328867415920531813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19564913753959551576169669 3668421328867415920531813)
                      ·
                        rfl

theorem cell23_7144225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7144225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144225 prefixEnd_7144225 := by exact prefixLift 7144225
  have htrace : WordTrace (prefixWord ++ tailWord_7144225) baseStart_7144225 baseEnd_7144225 := by
    simpa [prefixWord, tailWord_7144225, baseEnd_7144225] using wordTrace_append hprefix tailTrace_7144225
  have hstable : (prefixWord ++ tailWord_7144225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144225).length < 2 ^ (prefixWord ++ tailWord_7144225).sum := by decide
  have hdescent : baseEnd_7144225 < baseStart_7144225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144232 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_7144232 : Nat := 118140960795 + 7144232 * 2 ^ 59
def prefixEnd_7144232 : Nat := 4983230072969 + 3 ^ 40 * 7144232 * 2
def baseEnd_7144232 : Nat := 3668424923231997393144281

theorem tailTrace_7144232 : CollatzResearch.WordTrace tailWord_7144232 prefixEnd_7144232 3668424923231997393144281 := by
  unfold tailWord_7144232
  simp only [CollatzResearch.WordTrace]
  refine ⟨130285773926837538265293475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173714365235783384353724633 130285773926837538265293475)
  ·
    refine ⟨195428660890256307397940213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130285773926837538265293475 195428660890256307397940213)
    ·
      refine ⟨18321436958461528818556895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195428660890256307397940213 18321436958461528818556895)
      ·
        refine ⟨27482155437692293227835343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18321436958461528818556895 27482155437692293227835343)
        ·
          refine ⟨41223233156538439841753015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27482155437692293227835343 41223233156538439841753015)
          ·
            refine ⟨61834849734807659762629523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41223233156538439841753015 61834849734807659762629523)
            ·
              refine ⟨92752274602211489643944285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61834849734807659762629523 92752274602211489643944285)
              ·
                refine ⟨34782102975829308616479107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92752274602211489643944285 34782102975829308616479107)
                ·
                  refine ⟨52173154463743962924718661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34782102975829308616479107 52173154463743962924718661)
                  ·
                    refine ⟨9782466461951993048384749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52173154463743962924718661 9782466461951993048384749)
                    ·
                      refine ⟨3668424923231997393144281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9782466461951993048384749 3668424923231997393144281)
                      ·
                        rfl

theorem cell23_7144232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_7144232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144232 prefixEnd_7144232 := by exact prefixLift 7144232
  have htrace : WordTrace (prefixWord ++ tailWord_7144232) baseStart_7144232 baseEnd_7144232 := by
    simpa [prefixWord, tailWord_7144232, baseEnd_7144232] using wordTrace_append hprefix tailTrace_7144232
  have hstable : (prefixWord ++ tailWord_7144232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144232).length < 2 ^ (prefixWord ++ tailWord_7144232).sum := by decide
  have hdescent : baseEnd_7144232 < baseStart_7144232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144246 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7144246 : Nat := 118140960795 + 7144246 * 2 ^ 59
def prefixEnd_7144246 : Nat := 4983230072969 + 3 ^ 40 * 7144246 * 2
def baseEnd_7144246 : Nat := 3668432111961160338369217

theorem tailTrace_7144246 : CollatzResearch.WordTrace tailWord_7144246 prefixEnd_7144246 3668432111961160338369217 := by
  unfold tailWord_7144246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16285753654726522307599787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173714705650416237947731061 16285753654726522307599787)
  ·
    refine ⟨24428630482089783461399681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16285753654726522307599787 24428630482089783461399681)
    ·
      refine ⟨18321472861567337596049761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24428630482089783461399681 18321472861567337596049761)
      ·
        refine ⟨13741104646175503197037321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18321472861567337596049761 13741104646175503197037321)
        ·
          refine ⟨10305828484631627397777991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13741104646175503197037321 10305828484631627397777991)
          ·
            refine ⟨15458742726947441096666987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305828484631627397777991 15458742726947441096666987)
            ·
              refine ⟨23188114090421161645000481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15458742726947441096666987 23188114090421161645000481)
              ·
                refine ⟨17391085567815871233750361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23188114090421161645000481 17391085567815871233750361)
                ·
                  refine ⟨13043314175861903425312771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17391085567815871233750361 13043314175861903425312771)
                  ·
                    refine ⟨19564971263792855137969157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13043314175861903425312771 19564971263792855137969157)
                    ·
                      refine ⟨3668432111961160338369217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19564971263792855137969157 3668432111961160338369217)
                      ·
                        rfl

theorem cell23_7144246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7144246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144246 prefixEnd_7144246 := by exact prefixLift 7144246
  have htrace : WordTrace (prefixWord ++ tailWord_7144246) baseStart_7144246 baseEnd_7144246 := by
    simpa [prefixWord, tailWord_7144246, baseEnd_7144246] using wordTrace_append hprefix tailTrace_7144246
  have hstable : (prefixWord ++ tailWord_7144246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144246).length < 2 ^ (prefixWord ++ tailWord_7144246).sum := by decide
  have hdescent : baseEnd_7144246 < baseStart_7144246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144272 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 3, 5, 2]
def baseStart_7144272 : Nat := 118140960795 + 7144272 * 2 ^ 59
def prefixEnd_7144272 : Nat := 4983230072969 + 3 ^ 40 * 7144272 * 2
def baseEnd_7144272 : Nat := 3668445462458177236644097

theorem tailTrace_7144272 : CollatzResearch.WordTrace tailWord_7144272 prefixEnd_7144272 3668445462458177236644097 := by
  unfold tailWord_7144272
  simp only [CollatzResearch.WordTrace]
  refine ⟨130286503386765081681021535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173715337849020108908028713 130286503386765081681021535)
  ·
    refine ⟨195429755080147622521532303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130286503386765081681021535 195429755080147622521532303)
    ·
      refine ⟨293144632620221433782298455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195429755080147622521532303 293144632620221433782298455)
      ·
        refine ⟨439716948930332150673447683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293144632620221433782298455 439716948930332150673447683)
        ·
          refine ⟨659575423395498226010171525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439716948930332150673447683 659575423395498226010171525)
          ·
            refine ⟨123670391886655917376907161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 659575423395498226010171525 123670391886655917376907161)
            ·
              refine ⟨92752793914991938032680371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123670391886655917376907161 92752793914991938032680371)
              ·
                refine ⟨139129190872487907049020557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92752793914991938032680371 139129190872487907049020557)
                ·
                  refine ⟨52173446577182965143382709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139129190872487907049020557 52173446577182965143382709)
                  ·
                    refine ⟨4891260616610902982192129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52173446577182965143382709 4891260616610902982192129)
                    ·
                      refine ⟨3668445462458177236644097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891260616610902982192129 3668445462458177236644097)
                      ·
                        rfl

theorem cell23_7144272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 5, 2].length) (baseStart_7144272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144272 prefixEnd_7144272 := by exact prefixLift 7144272
  have htrace : WordTrace (prefixWord ++ tailWord_7144272) baseStart_7144272 baseEnd_7144272 := by
    simpa [prefixWord, tailWord_7144272, baseEnd_7144272] using wordTrace_append hprefix tailTrace_7144272
  have hstable : (prefixWord ++ tailWord_7144272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144272).length < 2 ^ (prefixWord ++ tailWord_7144272).sum := by decide
  have hdescent : baseEnd_7144272 < baseStart_7144272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144282 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_7144282 : Nat := 118140960795 + 7144282 * 2 ^ 59
def prefixEnd_7144282 : Nat := 4983230072969 + 3 ^ 40 * 7144282 * 2
def baseEnd_7144282 : Nat := 1222816865754907399173017

theorem tailTrace_7144282 : CollatzResearch.WordTrace tailWord_7144282 prefixEnd_7144282 1222816865754907399173017 := by
  unfold tailWord_7144282
  simp only [CollatzResearch.WordTrace]
  refine ⟨65143342875873483767476775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173715581002329290046604733 65143342875873483767476775)
  ·
    refine ⟨97715014313810225651215163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65143342875873483767476775 97715014313810225651215163)
    ·
      refine ⟨146572521470715338476822745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97715014313810225651215163 146572521470715338476822745)
      ·
        refine ⟨109929391103036503857617059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146572521470715338476822745 109929391103036503857617059)
        ·
          refine ⟨164894086654554755786425589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109929391103036503857617059 164894086654554755786425589)
          ·
            refine ⟨15458820623864508354977399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164894086654554755786425589 15458820623864508354977399)
            ·
              refine ⟨23188230935796762532466099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15458820623864508354977399 23188230935796762532466099)
              ·
                refine ⟨34782346403695143798699149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23188230935796762532466099 34782346403695143798699149)
                ·
                  refine ⟨13043379901385678924512181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34782346403695143798699149 13043379901385678924512181)
                  ·
                    refine ⟨1222816865754907399173017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13043379901385678924512181 1222816865754907399173017)
                    ·
                      rfl

theorem cell23_7144282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_7144282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144282 prefixEnd_7144282 := by exact prefixLift 7144282
  have htrace : WordTrace (prefixWord ++ tailWord_7144282) baseStart_7144282 baseEnd_7144282 := by
    simpa [prefixWord, tailWord_7144282, baseEnd_7144282] using wordTrace_append hprefix tailTrace_7144282
  have hstable : (prefixWord ++ tailWord_7144282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144282).length < 2 ^ (prefixWord ++ tailWord_7144282).sum := by decide
  have hdescent : baseEnd_7144282 < baseStart_7144282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
