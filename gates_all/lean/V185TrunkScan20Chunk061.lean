import V185TrunkScan20Chunk060

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_371543 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_371543 : Nat := 118140960795 + 371543 * 2 ^ 59
def prefixEnd_371543 : Nat := 4983230072969 + 3 ^ 40 * 371543 * 2
def baseEnd_371543 : Nat := 169582349167595617781165

theorem tailTrace_371543 : CollatzResearch.WordTrace tailWord_371543 prefixEnd_371543 169582349167595617781165 := by
  unfold tailWord_371543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551286492970640337639283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9034190995313760225092855 13551286492970640337639283)
  ·
    refine ⟨20326929739455960506458925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13551286492970640337639283 20326929739455960506458925)
    ·
      refine ⟨7622598652295985189922097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20326929739455960506458925 7622598652295985189922097)
      ·
        refine ⟨5716948989221988892441573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7622598652295985189922097 5716948989221988892441573)
        ·
          refine ⟨1071927935479122917332795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5716948989221988892441573 1071927935479122917332795)
          ·
            refine ⟨1607891903218684375999193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071927935479122917332795 1607891903218684375999193)
            ·
              refine ⟨1205918927414013281999395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1607891903218684375999193 1205918927414013281999395)
              ·
                refine ⟨1808878391121019922999093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205918927414013281999395 1808878391121019922999093)
                ·
                  refine ⟨169582349167595617781165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1808878391121019922999093 169582349167595617781165)
                  ·
                    rfl

theorem cell20_371543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_371543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371543 prefixEnd_371543 := by exact prefixLift 371543
  have htrace : WordTrace (prefixWord ++ tailWord_371543) baseStart_371543 baseEnd_371543 := by
    simpa [prefixWord, tailWord_371543, baseEnd_371543] using wordTrace_append hprefix tailTrace_371543
  have hstable : (prefixWord ++ tailWord_371543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371543).length < 2 ^ (prefixWord ++ tailWord_371543).sum := by decide
  have hdescent : baseEnd_371543 < baseStart_371543 := by decide
  rcases family_descends (prefixWord ++ tailWord_371543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371557 : List Nat := [1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_371557 : Nat := 118140960795 + 371557 * 2 ^ 59
def prefixEnd_371557 : Nat := 4983230072969 + 3 ^ 40 * 371557 * 2
def baseEnd_371557 : Nat := 56529579716357930438147

theorem tailTrace_371557 : CollatzResearch.WordTrace tailWord_371557 prefixEnd_371557 56529579716357930438147 := by
  unfold tailWord_371557
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551797114919920728648925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9034531409946613819099283 13551797114919920728648925)
  ·
    refine ⟨5081923918094970273243347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13551797114919920728648925 5081923918094970273243347)
    ·
      refine ⟨7622885877142455409865021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5081923918094970273243347 7622885877142455409865021)
      ·
        refine ⟨2858582203928420778699383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7622885877142455409865021 2858582203928420778699383)
        ·
          refine ⟨4287873305892631168049075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858582203928420778699383 4287873305892631168049075)
          ·
            refine ⟨6431809958838946752073613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287873305892631168049075 6431809958838946752073613)
            ·
              refine ⟨2411928734564605032027605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6431809958838946752073613 2411928734564605032027605)
              ·
                refine ⟨56529579716357930438147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2411928734564605032027605 56529579716357930438147)
                ·
                  rfl

theorem cell20_371557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_371557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371557 prefixEnd_371557 := by exact prefixLift 371557
  have htrace : WordTrace (prefixWord ++ tailWord_371557) baseStart_371557 baseEnd_371557 := by
    simpa [prefixWord, tailWord_371557, baseEnd_371557] using wordTrace_append hprefix tailTrace_371557
  have hstable : (prefixWord ++ tailWord_371557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371557).length < 2 ^ (prefixWord ++ tailWord_371557).sum := by decide
  have hdescent : baseEnd_371557 < baseStart_371557 := by decide
  rcases family_descends (prefixWord ++ tailWord_371557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371560 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_371560 : Nat := 118140960795 + 371560 * 2 ^ 59
def prefixEnd_371560 : Nat := 4983230072969 + 3 ^ 40 * 371560 * 2
def baseEnd_371560 : Nat := 169590108430819114214429

theorem tailTrace_371560 : CollatzResearch.WordTrace tailWord_371560 prefixEnd_371560 169590108430819114214429 := by
  unfold tailWord_371560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775953266954526120504067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9034604355939368160672089 6775953266954526120504067)
  ·
    refine ⟨10163929900431789180756101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6775953266954526120504067 10163929900431789180756101)
    ·
      refine ⟨1905736856330960471391769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10163929900431789180756101 1905736856330960471391769)
      ·
        refine ⟨1429302642248220353543827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1905736856330960471391769 1429302642248220353543827)
        ·
          refine ⟨2143953963372330530315741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429302642248220353543827 2143953963372330530315741)
          ·
            refine ⟨803982736264623948868403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2143953963372330530315741 803982736264623948868403)
            ·
              refine ⟨1205974104396935923302605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803982736264623948868403 1205974104396935923302605)
              ·
                refine ⟨452240289148850971238477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1205974104396935923302605 452240289148850971238477)
                ·
                  refine ⟨169590108430819114214429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452240289148850971238477 169590108430819114214429)
                  ·
                    rfl

theorem cell20_371560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_371560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371560 prefixEnd_371560 := by exact prefixLift 371560
  have htrace : WordTrace (prefixWord ++ tailWord_371560) baseStart_371560 baseEnd_371560 := by
    simpa [prefixWord, tailWord_371560, baseEnd_371560] using wordTrace_append hprefix tailTrace_371560
  have hstable : (prefixWord ++ tailWord_371560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371560).length < 2 ^ (prefixWord ++ tailWord_371560).sum := by decide
  have hdescent : baseEnd_371560 < baseStart_371560 := by decide
  rcases family_descends (prefixWord ++ tailWord_371560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371619 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_371619 : Nat := 118140960795 + 371619 * 2 ^ 59
def prefixEnd_371619 : Nat := 4983230072969 + 3 ^ 40 * 371619 * 2
def baseEnd_371619 : Nat := 169617037638477131247521

theorem tailTrace_371619 : CollatzResearch.WordTrace tailWord_371619 prefixEnd_371619 169617037638477131247521 := by
  unfold tailWord_371619
  simp only [CollatzResearch.WordTrace]
  refine ⟨13554058440695305317405911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9036038960463536878270607 13554058440695305317405911)
  ·
    refine ⟨20331087661042957976108867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13554058440695305317405911 20331087661042957976108867)
    ·
      refine ⟨30496631491564436964163301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20331087661042957976108867 30496631491564436964163301)
      ·
        refine ⟨5718118404668331930780619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30496631491564436964163301 5718118404668331930780619)
        ·
          refine ⟨8577177607002497896170929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718118404668331930780619 8577177607002497896170929)
          ·
            refine ⟨6432883205251873422128197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8577177607002497896170929 6432883205251873422128197)
            ·
              refine ⟨1206165600984726266649037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6432883205251873422128197 1206165600984726266649037)
              ·
                refine ⟨452312100369272349993389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1206165600984726266649037 452312100369272349993389)
                ·
                  refine ⟨169617037638477131247521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452312100369272349993389 169617037638477131247521)
                  ·
                    rfl

theorem cell20_371619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_371619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371619 prefixEnd_371619 := by exact prefixLift 371619
  have htrace : WordTrace (prefixWord ++ tailWord_371619) baseStart_371619 baseEnd_371619 := by
    simpa [prefixWord, tailWord_371619, baseEnd_371619] using wordTrace_append hprefix tailTrace_371619
  have hstable : (prefixWord ++ tailWord_371619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371619).length < 2 ^ (prefixWord ++ tailWord_371619).sum := by decide
  have hdescent : baseEnd_371619 < baseStart_371619 := by decide
  rcases family_descends (prefixWord ++ tailWord_371619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371670 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_371670 : Nat := 118140960795 + 371670 * 2 ^ 59
def prefixEnd_371670 : Nat := 4983230072969 + 3 ^ 40 * 371670 * 2
def baseEnd_371670 : Nat := 169640315428147620547313

theorem tailTrace_371670 : CollatzResearch.WordTrace tailWord_371670 prefixEnd_371670 169640315428147620547313 := by
  unfold tailWord_371670
  simp only [CollatzResearch.WordTrace]
  refine ⟨847244910219408814219529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9037279042340360685008309 847244910219408814219529)
  ·
    refine ⟨635433682664556610664647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 847244910219408814219529 635433682664556610664647)
    ·
      refine ⟨953150523996834915996971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635433682664556610664647 953150523996834915996971)
      ·
        refine ⟨1429725785995252373995457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953150523996834915996971 1429725785995252373995457)
        ·
          refine ⟨1072294339496439280496593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1429725785995252373995457 1072294339496439280496593)
          ·
            refine ⟨804220754622329460372445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072294339496439280496593 804220754622329460372445)
            ·
              refine ⟨301582782983373547639667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 804220754622329460372445 301582782983373547639667)
              ·
                refine ⟨452374174475060321459501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301582782983373547639667 452374174475060321459501)
                ·
                  refine ⟨169640315428147620547313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452374174475060321459501 169640315428147620547313)
                  ·
                    rfl

theorem cell20_371670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_371670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371670 prefixEnd_371670 := by exact prefixLift 371670
  have htrace : WordTrace (prefixWord ++ tailWord_371670) baseStart_371670 baseEnd_371670 := by
    simpa [prefixWord, tailWord_371670, baseEnd_371670] using wordTrace_append hprefix tailTrace_371670
  have hstable : (prefixWord ++ tailWord_371670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371670).length < 2 ^ (prefixWord ++ tailWord_371670).sum := by decide
  have hdescent : baseEnd_371670 < baseStart_371670 := by decide
  rcases family_descends (prefixWord ++ tailWord_371670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371688 : List Nat := [2, 1, 4, 1, 1, 1, 6, 4]
def baseStart_371688 : Nat := 118140960795 + 371688 * 2 ^ 59
def prefixEnd_371688 : Nat := 4983230072969 + 3 ^ 40 * 371688 * 2
def baseEnd_371688 : Nat := 56549510372873185982413

theorem tailTrace_371688 : CollatzResearch.WordTrace tailWord_371688 prefixEnd_371688 56549510372873185982413 := by
  unfold tailWord_371688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778287538722665050833859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9037716718296886734445145 6778287538722665050833859)
  ·
    refine ⟨10167431308083997576250789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6778287538722665050833859 10167431308083997576250789)
    ·
      refine ⟨1906393370265749545547023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10167431308083997576250789 1906393370265749545547023)
      ·
        refine ⟨2859590055398624318320535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906393370265749545547023 2859590055398624318320535)
        ·
          refine ⟨4289385083097936477480803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859590055398624318320535 4289385083097936477480803)
          ·
            refine ⟨6434077624646904716221205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4289385083097936477480803 6434077624646904716221205)
            ·
              refine ⟨301597388655323658572869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6434077624646904716221205 301597388655323658572869)
              ·
                refine ⟨56549510372873185982413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301597388655323658572869 56549510372873185982413)
                ·
                  rfl

theorem cell20_371688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_371688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371688 prefixEnd_371688 := by exact prefixLift 371688
  have htrace : WordTrace (prefixWord ++ tailWord_371688) baseStart_371688 baseEnd_371688 := by
    simpa [prefixWord, tailWord_371688, baseEnd_371688] using wordTrace_append hprefix tailTrace_371688
  have hstable : (prefixWord ++ tailWord_371688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371688).length < 2 ^ (prefixWord ++ tailWord_371688).sum := by decide
  have hdescent : baseEnd_371688 < baseStart_371688 := by decide
  rcases family_descends (prefixWord ++ tailWord_371688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371694 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_371694 : Nat := 118140960795 + 371694 * 2 ^ 59
def prefixEnd_371694 : Nat := 4983230072969 + 3 ^ 40 * 371694 * 2
def baseEnd_371694 : Nat := 169651269682110203747215

theorem tailTrace_371694 : CollatzResearch.WordTrace tailWord_371694 prefixEnd_371694 169651269682110203747215 := by
  unfold tailWord_371694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694599239427949140798267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9037862610282395417590757 1694599239427949140798267)
  ·
    refine ⟨2541898859141923711197401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694599239427949140798267 2541898859141923711197401)
    ·
      refine ⟨1906424144356442783398051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2541898859141923711197401 1906424144356442783398051)
      ·
        refine ⟨2859636216534664175097077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906424144356442783398051 2859636216534664175097077)
        ·
          refine ⟨268090895300124766415351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2859636216534664175097077 268090895300124766415351)
          ·
            refine ⟨402136342950187149623027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268090895300124766415351 402136342950187149623027)
            ·
              refine ⟨603204514425280724434541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402136342950187149623027 603204514425280724434541)
              ·
                refine ⟨226201692909480271662953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 603204514425280724434541 226201692909480271662953)
                ·
                  refine ⟨169651269682110203747215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226201692909480271662953 169651269682110203747215)
                  ·
                    rfl

theorem cell20_371694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_371694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371694 prefixEnd_371694 := by exact prefixLift 371694
  have htrace : WordTrace (prefixWord ++ tailWord_371694) baseStart_371694 baseEnd_371694 := by
    simpa [prefixWord, tailWord_371694, baseEnd_371694] using wordTrace_append hprefix tailTrace_371694
  have hstable : (prefixWord ++ tailWord_371694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371694).length < 2 ^ (prefixWord ++ tailWord_371694).sum := by decide
  have hdescent : baseEnd_371694 < baseStart_371694 := by decide
  rcases family_descends (prefixWord ++ tailWord_371694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371726 : List Nat := [4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_371726 : Nat := 118140960795 + 371726 * 2 ^ 59
def prefixEnd_371726 : Nat := 4983230072969 + 3 ^ 40 * 371726 * 2
def baseEnd_371726 : Nat := 56555291784686771560139

theorem tailTrace_371726 : CollatzResearch.WordTrace tailWord_371726 prefixEnd_371726 56555291784686771560139 := by
  unfold tailWord_371726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694745131413457823943879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9038640700871775061034021 1694745131413457823943879)
  ·
    refine ⟨2542117697120186735915819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694745131413457823943879 2542117697120186735915819)
    ·
      refine ⟨3813176545680280103873729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542117697120186735915819 3813176545680280103873729)
      ·
        refine ⟨2859882409260210077905297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813176545680280103873729 2859882409260210077905297)
        ·
          refine ⟨2144911806945157558428973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2859882409260210077905297 2144911806945157558428973)
          ·
            refine ⟨804341927604434084410865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2144911806945157558428973 804341927604434084410865)
            ·
              refine ⟨603256445703325563308149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804341927604434084410865 603256445703325563308149)
              ·
                refine ⟨56555291784686771560139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603256445703325563308149 56555291784686771560139)
                ·
                  rfl

theorem cell20_371726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_371726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371726 prefixEnd_371726 := by exact prefixLift 371726
  have htrace : WordTrace (prefixWord ++ tailWord_371726) baseStart_371726 baseEnd_371726 := by
    simpa [prefixWord, tailWord_371726, baseEnd_371726] using wordTrace_append hprefix tailTrace_371726
  have hstable : (prefixWord ++ tailWord_371726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371726).length < 2 ^ (prefixWord ++ tailWord_371726).sum := by decide
  have hdescent : baseEnd_371726 < baseStart_371726 := by decide
  rcases family_descends (prefixWord ++ tailWord_371726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371747 : List Nat := [1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_371747 : Nat := 118140960795 + 371747 * 2 ^ 59
def prefixEnd_371747 : Nat := 4983230072969 + 3 ^ 40 * 371747 * 2
def baseEnd_371747 : Nat := 56558486775425858326777

theorem tailTrace_371747 : CollatzResearch.WordTrace tailWord_371747 prefixEnd_371747 56558486775425858326777 := by
  unfold tailWord_371747
  simp only [CollatzResearch.WordTrace]
  refine ⟨13558726984231583178065495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9039151322821055452043663 13558726984231583178065495)
  ·
    refine ⟨20338090476347374767098243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13558726984231583178065495 20338090476347374767098243)
    ·
      refine ⟨30507135714521062150647365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20338090476347374767098243 30507135714521062150647365)
      ·
        refine ⟨5720087946472699153246381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30507135714521062150647365 5720087946472699153246381)
        ·
          refine ⟨2145032979927262182467393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5720087946472699153246381 2145032979927262182467393)
          ·
            refine ⟨1608774734945446636850545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145032979927262182467393 1608774734945446636850545)
            ·
              refine ⟨1206581051209084977637909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608774734945446636850545 1206581051209084977637909)
              ·
                refine ⟨56558486775425858326777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1206581051209084977637909 56558486775425858326777)
                ·
                  rfl

theorem cell20_371747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_371747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371747 prefixEnd_371747 := by exact prefixLift 371747
  have htrace : WordTrace (prefixWord ++ tailWord_371747) baseStart_371747 baseEnd_371747 := by
    simpa [prefixWord, tailWord_371747, baseEnd_371747] using wordTrace_append hprefix tailTrace_371747
  have hstable : (prefixWord ++ tailWord_371747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371747).length < 2 ^ (prefixWord ++ tailWord_371747).sum := by decide
  have hdescent : baseEnd_371747 < baseStart_371747 := by decide
  rcases family_descends (prefixWord ++ tailWord_371747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371764 : List Nat := [2, 5, 1, 2, 1, 9]
def baseStart_371764 : Nat := 118140960795 + 371764 * 2 ^ 59
def prefixEnd_371764 : Nat := 4983230072969 + 3 ^ 40 * 371764 * 2
def baseEnd_371764 : Nat := 6284563688500039681985

theorem tailTrace_371764 : CollatzResearch.WordTrace tailWord_371764 prefixEnd_371764 6284563688500039681985 := by
  unfold tailWord_371764
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779673512584997540717173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9039564683446663387622897 6779673512584997540717173)
  ·
    refine ⟨635594391804843519442235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6779673512584997540717173 635594391804843519442235)
    ·
      refine ⟨953391587707265279163353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635594391804843519442235 953391587707265279163353)
      ·
        refine ⟨715043690780448959372515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953391587707265279163353 715043690780448959372515)
        ·
          refine ⟨1072565536170673439058773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715043690780448959372515 1072565536170673439058773)
          ·
            refine ⟨6284563688500039681985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1072565536170673439058773 6284563688500039681985)
            ·
              rfl

theorem cell20_371764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 9].length) (baseStart_371764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371764 prefixEnd_371764 := by exact prefixLift 371764
  have htrace : WordTrace (prefixWord ++ tailWord_371764) baseStart_371764 baseEnd_371764 := by
    simpa [prefixWord, tailWord_371764, baseEnd_371764] using wordTrace_append hprefix tailTrace_371764
  have hstable : (prefixWord ++ tailWord_371764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371764).length < 2 ^ (prefixWord ++ tailWord_371764).sum := by decide
  have hdescent : baseEnd_371764 < baseStart_371764 := by decide
  rcases family_descends (prefixWord ++ tailWord_371764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371833 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_371833 : Nat := 118140960795 + 371833 * 2 ^ 59
def prefixEnd_371833 : Nat := 4983230072969 + 3 ^ 40 * 371833 * 2
def baseEnd_371833 : Nat := 169714713069643498113313

theorem tailTrace_371833 : CollatzResearch.WordTrace tailWord_371833 prefixEnd_371833 169714713069643498113313 := by
  unfold tailWord_371833
  simp only [CollatzResearch.WordTrace]
  refine ⟨13561863661920019865696153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9041242441280013243797435 13561863661920019865696153)
  ·
    refine ⟨10171397746440014899272115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13561863661920019865696153 10171397746440014899272115)
    ·
      refine ⟨15257096619660022348908173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10171397746440014899272115 15257096619660022348908173)
      ·
        refine ⟨5721411232372508380840565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15257096619660022348908173 5721411232372508380840565)
        ·
          refine ⟨536382303034922660703803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5721411232372508380840565 536382303034922660703803)
          ·
            refine ⟨804573454552383991055705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536382303034922660703803 804573454552383991055705)
            ·
              refine ⟨603430090914287993291779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804573454552383991055705 603430090914287993291779)
              ·
                refine ⟨905145136371431989937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603430090914287993291779 905145136371431989937669)
                ·
                  refine ⟨169714713069643498113313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905145136371431989937669 169714713069643498113313)
                  ·
                    rfl

theorem cell20_371833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_371833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371833 prefixEnd_371833 := by exact prefixLift 371833
  have htrace : WordTrace (prefixWord ++ tailWord_371833) baseStart_371833 baseEnd_371833 := by
    simpa [prefixWord, tailWord_371833, baseEnd_371833] using wordTrace_append hprefix tailTrace_371833
  have hstable : (prefixWord ++ tailWord_371833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371833).length < 2 ^ (prefixWord ++ tailWord_371833).sum := by decide
  have hdescent : baseEnd_371833 < baseStart_371833 := by decide
  rcases family_descends (prefixWord ++ tailWord_371833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371875 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_371875 : Nat := 118140960795 + 371875 * 2 ^ 59
def prefixEnd_371875 : Nat := 4983230072969 + 3 ^ 40 * 371875 * 2
def baseEnd_371875 : Nat := 169733883014078018713141

theorem tailTrace_371875 : CollatzResearch.WordTrace tailWord_371875 prefixEnd_371875 169733883014078018713141 := by
  unfold tailWord_371875
  simp only [CollatzResearch.WordTrace]
  refine ⟨13563395527767861038725079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9042263685178574025816719 13563395527767861038725079)
  ·
    refine ⟨20345093291651791558087619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13563395527767861038725079 20345093291651791558087619)
    ·
      refine ⟨30517639937477687337131429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20345093291651791558087619 30517639937477687337131429)
      ·
        refine ⟨5722057488277066375712143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30517639937477687337131429 5722057488277066375712143)
        ·
          refine ⟨8583086232415599563568215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722057488277066375712143 8583086232415599563568215)
          ·
            refine ⟨12874629348623399345352323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8583086232415599563568215 12874629348623399345352323)
            ·
              refine ⟨19311944022935099018028485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12874629348623399345352323 19311944022935099018028485)
              ·
                refine ⟨3620989504300331065880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19311944022935099018028485 3620989504300331065880341)
                ·
                  refine ⟨169733883014078018713141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3620989504300331065880341 169733883014078018713141)
                  ·
                    rfl

theorem cell20_371875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_371875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371875 prefixEnd_371875 := by exact prefixLift 371875
  have htrace : WordTrace (prefixWord ++ tailWord_371875) baseStart_371875 baseEnd_371875 := by
    simpa [prefixWord, tailWord_371875, baseEnd_371875] using wordTrace_append hprefix tailTrace_371875
  have hstable : (prefixWord ++ tailWord_371875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371875).length < 2 ^ (prefixWord ++ tailWord_371875).sum := by decide
  have hdescent : baseEnd_371875 < baseStart_371875 := by decide
  rcases family_descends (prefixWord ++ tailWord_371875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371894 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_371894 : Nat := 118140960795 + 371894 * 2 ^ 59
def prefixEnd_371894 : Nat := 4983230072969 + 3 ^ 40 * 371894 * 2
def baseEnd_371894 : Nat := 169742555131798397079731

theorem tailTrace_371894 : CollatzResearch.WordTrace tailWord_371894 prefixEnd_371894 169742555131798397079731 := by
  unfold tailWord_371894
  simp only [CollatzResearch.WordTrace]
  refine ⟨847755532168689205229171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9042725676466018189111157 847755532168689205229171)
  ·
    refine ⟨1271633298253033807843757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847755532168689205229171 1271633298253033807843757)
    ·
      refine ⟨476862486844887677941409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1271633298253033807843757 476862486844887677941409)
      ·
        refine ⟨357646865133665758456057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476862486844887677941409 357646865133665758456057)
        ·
          refine ⟨268235148850249318842043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357646865133665758456057 268235148850249318842043)
          ·
            refine ⟨402352723275373978263065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268235148850249318842043 402352723275373978263065)
            ·
              refine ⟨301764542456530483697299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402352723275373978263065 301764542456530483697299)
              ·
                refine ⟨452646813684795725545949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301764542456530483697299 452646813684795725545949)
                ·
                  refine ⟨169742555131798397079731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452646813684795725545949 169742555131798397079731)
                  ·
                    rfl

theorem cell20_371894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_371894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371894 prefixEnd_371894 := by exact prefixLift 371894
  have htrace : WordTrace (prefixWord ++ tailWord_371894) baseStart_371894 baseEnd_371894 := by
    simpa [prefixWord, tailWord_371894, baseEnd_371894] using wordTrace_append hprefix tailTrace_371894
  have hstable : (prefixWord ++ tailWord_371894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371894).length < 2 ^ (prefixWord ++ tailWord_371894).sum := by decide
  have hdescent : baseEnd_371894 < baseStart_371894 := by decide
  rcases family_descends (prefixWord ++ tailWord_371894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371902 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_371902 : Nat := 118140960795 + 371902 * 2 ^ 59
def prefixEnd_371902 : Nat := 4983230072969 + 3 ^ 40 * 371902 * 2
def baseEnd_371902 : Nat := 169746206549785924813031

theorem tailTrace_371902 : CollatzResearch.WordTrace tailWord_371902 prefixEnd_371902 169746206549785924813031 := by
  unfold tailWord_371902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695547537333755581244745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9042920199113363099971973 1695547537333755581244745)
  ·
    refine ⟨1271660653000316685933559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1695547537333755581244745 1271660653000316685933559)
    ·
      refine ⟨1907490979500475028900339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271660653000316685933559 1907490979500475028900339)
      ·
        refine ⟨2861236469250712543350509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907490979500475028900339 2861236469250712543350509)
        ·
          refine ⟨1072963675969017203756441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2861236469250712543350509 1072963675969017203756441)
          ·
            refine ⟨804722756976762902817331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072963675969017203756441 804722756976762902817331)
            ·
              refine ⟨1207084135465144354225997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804722756976762902817331 1207084135465144354225997)
              ·
                refine ⟨452656550799429132834749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207084135465144354225997 452656550799429132834749)
                ·
                  refine ⟨169746206549785924813031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452656550799429132834749 169746206549785924813031)
                  ·
                    rfl

theorem cell20_371902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_371902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371902 prefixEnd_371902 := by exact prefixLift 371902
  have htrace : WordTrace (prefixWord ++ tailWord_371902) baseStart_371902 baseEnd_371902 := by
    simpa [prefixWord, tailWord_371902, baseEnd_371902] using wordTrace_append hprefix tailTrace_371902
  have hstable : (prefixWord ++ tailWord_371902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371902).length < 2 ^ (prefixWord ++ tailWord_371902).sum := by decide
  have hdescent : baseEnd_371902 < baseStart_371902 := by decide
  rcases family_descends (prefixWord ++ tailWord_371902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371947 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 2]
def baseStart_371947 : Nat := 118140960795 + 371947 * 2 ^ 59
def prefixEnd_371947 : Nat := 4983230072969 + 3 ^ 40 * 371947 * 2
def baseEnd_371947 : Nat := 169766745775965768312847

theorem tailTrace_371947 : CollatzResearch.WordTrace tailWord_371947 prefixEnd_371947 169766745775965768312847 := by
  unfold tailWord_371947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13566021583507017335346095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9044014389004678223564063 13566021583507017335346095)
  ·
    refine ⟨20349032375260526003019143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13566021583507017335346095 20349032375260526003019143)
    ·
      refine ⟨30523548562890789004528715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20349032375260526003019143 30523548562890789004528715)
      ·
        refine ⟨45785322844336183506793073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30523548562890789004528715 45785322844336183506793073)
        ·
          refine ⟨34338992133252137630094805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45785322844336183506793073 34338992133252137630094805)
          ·
            refine ⟨804820128123096975705347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34338992133252137630094805 804820128123096975705347)
            ·
              refine ⟨1207230192184645463558021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804820128123096975705347 1207230192184645463558021)
              ·
                refine ⟨226355661034621024417129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1207230192184645463558021 226355661034621024417129)
                ·
                  refine ⟨169766745775965768312847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226355661034621024417129 169766745775965768312847)
                  ·
                    rfl

theorem cell20_371947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 2].length) (baseStart_371947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371947 prefixEnd_371947 := by exact prefixLift 371947
  have htrace : WordTrace (prefixWord ++ tailWord_371947) baseStart_371947 baseEnd_371947 := by
    simpa [prefixWord, tailWord_371947, baseEnd_371947] using wordTrace_append hprefix tailTrace_371947
  have hstable : (prefixWord ++ tailWord_371947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371947).length < 2 ^ (prefixWord ++ tailWord_371947).sum := by decide
  have hdescent : baseEnd_371947 < baseStart_371947 := by decide
  rcases family_descends (prefixWord ++ tailWord_371947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371985 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 2]
def baseStart_371985 : Nat := 118140960795 + 371985 * 2 ^ 59
def prefixEnd_371985 : Nat := 4983230072969 + 3 ^ 40 * 371985 * 2
def baseEnd_371985 : Nat := 169784090011406525046025

theorem tailTrace_371985 : CollatzResearch.WordTrace tailWord_371985 prefixEnd_371985 169784090011406525046025 := by
  unfold tailWord_371985
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567407557369349825229409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9044938371579566550152939 13567407557369349825229409)
  ·
    refine ⟨10175555668027012368922057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13567407557369349825229409 10175555668027012368922057)
    ·
      refine ⟨7631666751020259276691543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10175555668027012368922057 7631666751020259276691543)
      ·
        refine ⟨11447500126530388915037315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7631666751020259276691543 11447500126530388915037315)
        ·
          refine ⟨17171250189795583372555973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11447500126530388915037315 17171250189795583372555973)
          ·
            refine ⟨3219609410586671882354245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17171250189795583372555973 3219609410586671882354245)
            ·
              refine ⟨603676764485000977941421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3219609410586671882354245 603676764485000977941421)
              ·
                refine ⟨226378786681875366728033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 603676764485000977941421 226378786681875366728033)
                ·
                  refine ⟨169784090011406525046025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226378786681875366728033 169784090011406525046025)
                  ·
                    rfl

theorem cell20_371985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_371985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371985 prefixEnd_371985 := by exact prefixLift 371985
  have htrace : WordTrace (prefixWord ++ tailWord_371985) baseStart_371985 baseEnd_371985 := by
    simpa [prefixWord, tailWord_371985, baseEnd_371985] using wordTrace_append hprefix tailTrace_371985
  have hstable : (prefixWord ++ tailWord_371985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371985).length < 2 ^ (prefixWord ++ tailWord_371985).sum := by decide
  have hdescent : baseEnd_371985 < baseStart_371985 := by decide
  rcases family_descends (prefixWord ++ tailWord_371985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371989 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_371989 : Nat := 118140960795 + 371989 * 2 ^ 59
def prefixEnd_371989 : Nat := 4983230072969 + 3 ^ 40 * 371989 * 2
def baseEnd_371989 : Nat := 169785915720400288912675

theorem tailTrace_371989 : CollatzResearch.WordTrace tailWord_371989 prefixEnd_371989 169785915720400288912675 := by
  unfold tailWord_371989
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567553449354858508375021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9045035632903239005583347 13567553449354858508375021)
  ·
    refine ⟨5087832543508071940640633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13567553449354858508375021 5087832543508071940640633)
    ·
      refine ⟨3815874407631053955480475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5087832543508071940640633 3815874407631053955480475)
      ·
        refine ⟨5723811611446580933220713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815874407631053955480475 5723811611446580933220713)
        ·
          refine ⟨4292858708584935699915535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5723811611446580933220713 4292858708584935699915535)
          ·
            refine ⟨6439288062877403549873303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292858708584935699915535 6439288062877403549873303)
            ·
              refine ⟨9658932094316105324809955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439288062877403549873303 9658932094316105324809955)
              ·
                refine ⟨14488398141474157987214933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9658932094316105324809955 14488398141474157987214933)
                ·
                  refine ⟨169785915720400288912675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14488398141474157987214933 169785915720400288912675)
                  ·
                    rfl

theorem cell20_371989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_371989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371989 prefixEnd_371989 := by exact prefixLift 371989
  have htrace : WordTrace (prefixWord ++ tailWord_371989) baseStart_371989 baseEnd_371989 := by
    simpa [prefixWord, tailWord_371989, baseEnd_371989] using wordTrace_append hprefix tailTrace_371989
  have hstable : (prefixWord ++ tailWord_371989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371989).length < 2 ^ (prefixWord ++ tailWord_371989).sum := by decide
  have hdescent : baseEnd_371989 < baseStart_371989 := by decide
  rcases family_descends (prefixWord ++ tailWord_371989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371999 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_371999 : Nat := 118140960795 + 371999 * 2 ^ 59
def prefixEnd_371999 : Nat := 4983230072969 + 3 ^ 40 * 371999 * 2
def baseEnd_371999 : Nat := 169790479992884698579301

theorem tailTrace_371999 : CollatzResearch.WordTrace tailWord_371999 prefixEnd_371999 169790479992884698579301 := by
  unfold tailWord_371999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567918179318630216239051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9045278786212420144159367 13567918179318630216239051)
  ·
    refine ⟨20351877268977945324358577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13567918179318630216239051 20351877268977945324358577)
    ·
      refine ⟨15263907951733458993268933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20351877268977945324358577 15263907951733458993268933)
      ·
        refine ⟨2861982740950023561237925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15263907951733458993268933 2861982740950023561237925)
        ·
          refine ⟨536621763928129417732111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2861982740950023561237925 536621763928129417732111)
          ·
            refine ⟨804932645892194126598167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536621763928129417732111 804932645892194126598167)
            ·
              refine ⟨1207398968838291189897251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804932645892194126598167 1207398968838291189897251)
              ·
                refine ⟨1811098453257436784845877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207398968838291189897251 1811098453257436784845877)
                ·
                  refine ⟨169790479992884698579301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1811098453257436784845877 169790479992884698579301)
                  ·
                    rfl

theorem cell20_371999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_371999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_371999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_371999 prefixEnd_371999 := by exact prefixLift 371999
  have htrace : WordTrace (prefixWord ++ tailWord_371999) baseStart_371999 baseEnd_371999 := by
    simpa [prefixWord, tailWord_371999, baseEnd_371999] using wordTrace_append hprefix tailTrace_371999
  have hstable : (prefixWord ++ tailWord_371999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371999).length < 2 ^ (prefixWord ++ tailWord_371999).sum := by decide
  have hdescent : baseEnd_371999 < baseStart_371999 := by decide
  rcases family_descends (prefixWord ++ tailWord_371999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372058 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_372058 : Nat := 118140960795 + 372058 * 2 ^ 59
def prefixEnd_372058 : Nat := 4983230072969 + 3 ^ 40 * 372058 * 2
def baseEnd_372058 : Nat := 169817409200542715612393

theorem tailTrace_372058 : CollatzResearch.WordTrace tailWord_372058 prefixEnd_372058 169817409200542715612393 := by
  unfold tailWord_372058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392517521526220823159207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9046713390736588861757885 3392517521526220823159207)
  ·
    refine ⟨5088776282289331234738811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392517521526220823159207 5088776282289331234738811)
    ·
      refine ⟨7633164423433996852108217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5088776282289331234738811 7633164423433996852108217)
      ·
        refine ⟨5724873317575497639081163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7633164423433996852108217 5724873317575497639081163)
        ·
          refine ⟨8587309976363246458621745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5724873317575497639081163 8587309976363246458621745)
          ·
            refine ⟨6440482482272434843966309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8587309976363246458621745 6440482482272434843966309)
            ·
              refine ⟨1207590465426081533243683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6440482482272434843966309 1207590465426081533243683)
              ·
                refine ⟨1811385698139122299865525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207590465426081533243683 1811385698139122299865525)
                ·
                  refine ⟨169817409200542715612393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1811385698139122299865525 169817409200542715612393)
                  ·
                    rfl

theorem cell20_372058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_372058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372058 prefixEnd_372058 := by exact prefixLift 372058
  have htrace : WordTrace (prefixWord ++ tailWord_372058) baseStart_372058 baseEnd_372058 := by
    simpa [prefixWord, tailWord_372058, baseEnd_372058] using wordTrace_append hprefix tailTrace_372058
  have hstable : (prefixWord ++ tailWord_372058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372058).length < 2 ^ (prefixWord ++ tailWord_372058).sum := by decide
  have hdescent : baseEnd_372058 < baseStart_372058 := by decide
  rcases family_descends (prefixWord ++ tailWord_372058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372071 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 3]
def baseStart_372071 : Nat := 118140960795 + 372071 * 2 ^ 59
def prefixEnd_372071 : Nat := 4983230072969 + 3 ^ 40 * 372071 * 2
def baseEnd_372071 : Nat := 169823342754772448179007

theorem tailTrace_372071 : CollatzResearch.WordTrace tailWord_372071 prefixEnd_372071 169823342754772448179007 := by
  unfold tailWord_372071
  simp only [CollatzResearch.WordTrace]
  refine ⟨13570544235057786512860067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9047029490038524341906711 13570544235057786512860067)
  ·
    refine ⟨20355816352586679769290101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13570544235057786512860067 20355816352586679769290101)
    ·
      refine ⟨1908357783055001228370947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20355816352586679769290101 1908357783055001228370947)
      ·
        refine ⟨2862536674582501842556421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908357783055001228370947 2862536674582501842556421)
        ·
          refine ⟨536725626484219095479329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2862536674582501842556421 536725626484219095479329)
          ·
            refine ⟨402544219863164321609497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536725626484219095479329 402544219863164321609497)
            ·
              refine ⟨301908164897373241207123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402544219863164321609497 301908164897373241207123)
              ·
                refine ⟨452862247346059861810685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301908164897373241207123 452862247346059861810685)
                ·
                  refine ⟨169823342754772448179007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452862247346059861810685 169823342754772448179007)
                  ·
                    rfl

theorem cell20_372071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_372071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372071 prefixEnd_372071 := by exact prefixLift 372071
  have htrace : WordTrace (prefixWord ++ tailWord_372071) baseStart_372071 baseEnd_372071 := by
    simpa [prefixWord, tailWord_372071, baseEnd_372071] using wordTrace_append hprefix tailTrace_372071
  have hstable : (prefixWord ++ tailWord_372071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372071).length < 2 ^ (prefixWord ++ tailWord_372071).sum := by decide
  have hdescent : baseEnd_372071 < baseStart_372071 := by decide
  rcases family_descends (prefixWord ++ tailWord_372071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372116 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 2]
def baseStart_372116 : Nat := 118140960795 + 372116 * 2 ^ 59
def prefixEnd_372116 : Nat := 4983230072969 + 3 ^ 40 * 372116 * 2
def baseEnd_372116 : Nat := 169843881980952291678823

theorem tailTrace_372116 : CollatzResearch.WordTrace tailWord_372116 prefixEnd_372116 169843881980952291678823 := by
  unfold tailWord_372116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786092759947379599124101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9048123679929839465498801 6786092759947379599124101)
  ·
    refine ⟨1272392392490133674835769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6786092759947379599124101 1272392392490133674835769)
    ·
      refine ⟨954294294367600256126827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1272392392490133674835769 954294294367600256126827)
      ·
        refine ⟨1431441441551400384190241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954294294367600256126827 1431441441551400384190241)
        ·
          refine ⟨1073581081163550288142681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1431441441551400384190241 1073581081163550288142681)
          ·
            refine ⟨805185810872662716107011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073581081163550288142681 805185810872662716107011)
            ·
              refine ⟨1207778716308994074160517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805185810872662716107011 1207778716308994074160517)
              ·
                refine ⟨226458509307936388905097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1207778716308994074160517 226458509307936388905097)
                ·
                  refine ⟨169843881980952291678823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226458509307936388905097 169843881980952291678823)
                  ·
                    rfl

theorem cell20_372116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_372116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372116 prefixEnd_372116 := by exact prefixLift 372116
  have htrace : WordTrace (prefixWord ++ tailWord_372116) baseStart_372116 baseEnd_372116 := by
    simpa [prefixWord, tailWord_372116, baseEnd_372116] using wordTrace_append hprefix tailTrace_372116
  have hstable : (prefixWord ++ tailWord_372116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372116).length < 2 ^ (prefixWord ++ tailWord_372116).sum := by decide
  have hdescent : baseEnd_372116 < baseStart_372116 := by decide
  rcases family_descends (prefixWord ++ tailWord_372116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372127 : List Nat := [1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_372127 : Nat := 118140960795 + 372127 * 2 ^ 59
def prefixEnd_372127 : Nat := 4983230072969 + 3 ^ 40 * 372127 * 2
def baseEnd_372127 : Nat := 56616300893561714104037

theorem tailTrace_372127 : CollatzResearch.WordTrace tailWord_372127 prefixEnd_372127 56616300893561714104037 := by
  unfold tailWord_372127
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572586722854908076898635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9048391148569938717932423 13572586722854908076898635)
  ·
    refine ⟨20358880084282362115347953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13572586722854908076898635 20358880084282362115347953)
    ·
      refine ⟨15269160063211771586510965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20358880084282362115347953 15269160063211771586510965)
      ·
        refine ⟨1431483755926103586235403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15269160063211771586510965 1431483755926103586235403)
        ·
          refine ⟨2147225633889155379353105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431483755926103586235403 2147225633889155379353105)
          ·
            refine ⟨1610419225416866534514829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147225633889155379353105 1610419225416866534514829)
            ·
              refine ⟨603907209531324950443061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1610419225416866534514829 603907209531324950443061)
              ·
                refine ⟨56616300893561714104037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603907209531324950443061 56616300893561714104037)
                ·
                  rfl

theorem cell20_372127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_372127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372127 prefixEnd_372127 := by exact prefixLift 372127
  have htrace : WordTrace (prefixWord ++ tailWord_372127) baseStart_372127 baseEnd_372127 := by
    simpa [prefixWord, tailWord_372127, baseEnd_372127] using wordTrace_append hprefix tailTrace_372127
  have hstable : (prefixWord ++ tailWord_372127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372127).length < 2 ^ (prefixWord ++ tailWord_372127).sum := by decide
  have hdescent : baseEnd_372127 < baseStart_372127 := by decide
  rcases family_descends (prefixWord ++ tailWord_372127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372234 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_372234 : Nat := 118140960795 + 372234 * 2 ^ 59
def prefixEnd_372234 : Nat := 4983230072969 + 3 ^ 40 * 372234 * 2
def baseEnd_372234 : Nat := 169897740396268325745007

theorem tailTrace_372234 : CollatzResearch.WordTrace tailWord_372234 prefixEnd_372234 169897740396268325745007 := by
  unfold tailWord_372234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3394122333366816337760939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9050992888978176900695837 3394122333366816337760939)
  ·
    refine ⟨5091183500050224506641409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3394122333366816337760939 5091183500050224506641409)
    ·
      refine ⟨3818387625037668379981057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5091183500050224506641409 3818387625037668379981057)
      ·
        refine ⟨2863790718778251284985793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3818387625037668379981057 2863790718778251284985793)
        ·
          refine ⟨2147843039083688463739345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2863790718778251284985793 2147843039083688463739345)
          ·
            refine ⟨1610882279312766347804509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147843039083688463739345 1610882279312766347804509)
            ·
              refine ⟨604080854742287380426691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1610882279312766347804509 604080854742287380426691)
              ·
                refine ⟨906121282113431070640037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604080854742287380426691 906121282113431070640037)
                ·
                  refine ⟨169897740396268325745007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906121282113431070640037 169897740396268325745007)
                  ·
                    rfl

theorem cell20_372234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_372234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372234 prefixEnd_372234 := by exact prefixLift 372234
  have htrace : WordTrace (prefixWord ++ tailWord_372234) baseStart_372234 baseEnd_372234 := by
    simpa [prefixWord, tailWord_372234, baseEnd_372234] using wordTrace_append hprefix tailTrace_372234
  have hstable : (prefixWord ++ tailWord_372234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372234).length < 2 ^ (prefixWord ++ tailWord_372234).sum := by decide
  have hdescent : baseEnd_372234 < baseStart_372234 := by decide
  rcases family_descends (prefixWord ++ tailWord_372234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372255 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_372255 : Nat := 118140960795 + 372255 * 2 ^ 59
def prefixEnd_372255 : Nat := 4983230072969 + 3 ^ 40 * 372255 * 2
def baseEnd_372255 : Nat := 169907325368485586044921

theorem tailTrace_372255 : CollatzResearch.WordTrace tailWord_372255 prefixEnd_372255 169907325368485586044921 := by
  unfold tailWord_372255
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577255266391185937558219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9051503510927457291705479 13577255266391185937558219)
  ·
    refine ⟨20365882899586778906337329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13577255266391185937558219 20365882899586778906337329)
    ·
      refine ⟨15274412174690084179752997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20365882899586778906337329 15274412174690084179752997)
      ·
        refine ⟨2863952282754390783703687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15274412174690084179752997 2863952282754390783703687)
        ·
          refine ⟨4295928424131586175555531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863952282754390783703687 4295928424131586175555531)
          ·
            refine ⟨6443892636197379263333297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295928424131586175555531 6443892636197379263333297)
            ·
              refine ⟨4832919477148034447499973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443892636197379263333297 4832919477148034447499973)
              ·
                refine ⟨906172401965256458906245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4832919477148034447499973 906172401965256458906245)
                ·
                  refine ⟨169907325368485586044921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906172401965256458906245 169907325368485586044921)
                  ·
                    rfl

theorem cell20_372255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_372255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372255 prefixEnd_372255 := by exact prefixLift 372255
  have htrace : WordTrace (prefixWord ++ tailWord_372255) baseStart_372255 baseEnd_372255 := by
    simpa [prefixWord, tailWord_372255, baseEnd_372255] using wordTrace_append hprefix tailTrace_372255
  have hstable : (prefixWord ++ tailWord_372255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372255).length < 2 ^ (prefixWord ++ tailWord_372255).sum := by decide
  have hdescent : baseEnd_372255 < baseStart_372255 := by decide
  rcases family_descends (prefixWord ++ tailWord_372255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372272 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 2]
def baseStart_372272 : Nat := 118140960795 + 372272 * 2 ^ 59
def prefixEnd_372272 : Nat := 4983230072969 + 3 ^ 40 * 372272 * 2
def baseEnd_372272 : Nat := 169915084631709082478185

theorem tailTrace_372272 : CollatzResearch.WordTrace tailWord_372272 prefixEnd_372272 169915084631709082478185 := by
  unfold tailWord_372272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6788937653664798920463535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9051916871553065227284713 6788937653664798920463535)
  ·
    refine ⟨10183406480497198380695303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6788937653664798920463535 10183406480497198380695303)
    ·
      refine ⟨15275109720745797571042955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10183406480497198380695303 15275109720745797571042955)
      ·
        refine ⟨22912664581118696356564433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15275109720745797571042955 22912664581118696356564433)
        ·
          refine ⟨17184498435839022267423325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22912664581118696356564433 17184498435839022267423325)
          ·
            refine ⟨6444186913439633350283747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17184498435839022267423325 6444186913439633350283747)
            ·
              refine ⟨9666280370159450025425621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6444186913439633350283747 9666280370159450025425621)
              ·
                refine ⟨226553446175612109970913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9666280370159450025425621 226553446175612109970913)
                ·
                  refine ⟨169915084631709082478185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226553446175612109970913 169915084631709082478185)
                  ·
                    rfl

theorem cell20_372272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_372272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372272 prefixEnd_372272 := by exact prefixLift 372272
  have htrace : WordTrace (prefixWord ++ tailWord_372272) baseStart_372272 baseEnd_372272 := by
    simpa [prefixWord, tailWord_372272, baseEnd_372272] using wordTrace_append hprefix tailTrace_372272
  have hstable : (prefixWord ++ tailWord_372272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372272).length < 2 ^ (prefixWord ++ tailWord_372272).sum := by decide
  have hdescent : baseEnd_372272 < baseStart_372272 := by decide
  rcases family_descends (prefixWord ++ tailWord_372272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372285 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 2]
def baseStart_372285 : Nat := 118140960795 + 372285 * 2 ^ 59
def prefixEnd_372285 : Nat := 4983230072969 + 3 ^ 40 * 372285 * 2
def baseEnd_372285 : Nat := 169921018185938815044799

theorem tailTrace_372285 : CollatzResearch.WordTrace tailWord_372285 prefixEnd_372285 169921018185938815044799 := by
  unfold tailWord_372285
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578349456282501061150309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052232970855000707433539 13578349456282501061150309)
  ·
    refine ⟨2545940523052968948965683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13578349456282501061150309 2545940523052968948965683)
    ·
      refine ⟨3818910784579453423448525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2545940523052968948965683 3818910784579453423448525)
      ·
        refine ⟨1432091544217295033793197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3818910784579453423448525 1432091544217295033793197)
        ·
          refine ⟨537034329081485637672449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1432091544217295033793197 537034329081485637672449)
          ·
            refine ⟨402775746811114228254337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537034329081485637672449 402775746811114228254337)
            ·
              refine ⟨302081810108335671190753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402775746811114228254337 302081810108335671190753)
              ·
                refine ⟨226561357581251753393065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302081810108335671190753 226561357581251753393065)
                ·
                  refine ⟨169921018185938815044799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226561357581251753393065 169921018185938815044799)
                  ·
                    rfl

theorem cell20_372285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_372285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372285 prefixEnd_372285 := by exact prefixLift 372285
  have htrace : WordTrace (prefixWord ++ tailWord_372285) baseStart_372285 baseEnd_372285 := by
    simpa [prefixWord, tailWord_372285, baseEnd_372285] using wordTrace_append hprefix tailTrace_372285
  have hstable : (prefixWord ++ tailWord_372285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372285).length < 2 ^ (prefixWord ++ tailWord_372285).sum := by decide
  have hdescent : baseEnd_372285 < baseStart_372285 := by decide
  rcases family_descends (prefixWord ++ tailWord_372285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372289 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 2]
def baseStart_372289 : Nat := 118140960795 + 372289 * 2 ^ 59
def prefixEnd_372289 : Nat := 4983230072969 + 3 ^ 40 * 372289 * 2
def baseEnd_372289 : Nat := 169922843894932578911449

theorem tailTrace_372289 : CollatzResearch.WordTrace tailWord_372289 prefixEnd_372289 169922843894932578911449 := by
  unfold tailWord_372289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578495348268009744295921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052330232178673162863947 13578495348268009744295921)
  ·
    refine ⟨10183871511201007308221941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13578495348268009744295921 10183871511201007308221941)
    ·
      refine ⟨954737954175094435145807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10183871511201007308221941 954737954175094435145807)
      ·
        refine ⟨1432106931262641652718711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954737954175094435145807 1432106931262641652718711)
        ·
          refine ⟨2148160396893962479078067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432106931262641652718711 2148160396893962479078067)
          ·
            refine ⟨3222240595340943718617101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148160396893962479078067 3222240595340943718617101)
            ·
              refine ⟨1208340223252853894481413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3222240595340943718617101 1208340223252853894481413)
              ·
                refine ⟨226563791859910105215265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1208340223252853894481413 226563791859910105215265)
                ·
                  refine ⟨169922843894932578911449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226563791859910105215265 169922843894932578911449)
                  ·
                    rfl

theorem cell20_372289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_372289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372289 prefixEnd_372289 := by exact prefixLift 372289
  have htrace : WordTrace (prefixWord ++ tailWord_372289) baseStart_372289 baseEnd_372289 := by
    simpa [prefixWord, tailWord_372289, baseEnd_372289] using wordTrace_append hprefix tailTrace_372289
  have hstable : (prefixWord ++ tailWord_372289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372289).length < 2 ^ (prefixWord ++ tailWord_372289).sum := by decide
  have hdescent : baseEnd_372289 < baseStart_372289 := by decide
  rcases family_descends (prefixWord ++ tailWord_372289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372293 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_372293 : Nat := 118140960795 + 372293 * 2 ^ 59
def prefixEnd_372293 : Nat := 4983230072969 + 3 ^ 40 * 372293 * 2
def baseEnd_372293 : Nat := 169924669603926342778099

theorem tailTrace_372293 : CollatzResearch.WordTrace tailWord_372293 prefixEnd_372293 169924669603926342778099 := by
  unfold tailWord_372293
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578641240253518427441533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052427493502345618294355 13578641240253518427441533)
  ·
    refine ⟨5091990465095069410290575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13578641240253518427441533 5091990465095069410290575)
    ·
      refine ⟨7637985697642604115435863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5091990465095069410290575 7637985697642604115435863)
      ·
        refine ⟨11456978546463906173153795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7637985697642604115435863 11456978546463906173153795)
        ·
          refine ⟨17185467819695859259730693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11456978546463906173153795 17185467819695859259730693)
          ·
            refine ⟨3222275216192973611199505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17185467819695859259730693 3222275216192973611199505)
            ·
              refine ⟨2416706412144730208399629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222275216192973611199505 2416706412144730208399629)
              ·
                refine ⟨906264904554273828149861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2416706412144730208399629 906264904554273828149861)
                ·
                  refine ⟨169924669603926342778099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906264904554273828149861 169924669603926342778099)
                  ·
                    rfl

theorem cell20_372293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_372293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372293 prefixEnd_372293 := by exact prefixLift 372293
  have htrace : WordTrace (prefixWord ++ tailWord_372293) baseStart_372293 baseEnd_372293 := by
    simpa [prefixWord, tailWord_372293, baseEnd_372293] using wordTrace_append hprefix tailTrace_372293
  have hstable : (prefixWord ++ tailWord_372293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372293).length < 2 ^ (prefixWord ++ tailWord_372293).sum := by decide
  have hdescent : baseEnd_372293 < baseStart_372293 := by decide
  rcases family_descends (prefixWord ++ tailWord_372293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372341 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_372341 : Nat := 118140960795 + 372341 * 2 ^ 59
def prefixEnd_372341 : Nat := 4983230072969 + 3 ^ 40 * 372341 * 2
def baseEnd_372341 : Nat := 169946578111851509177903

theorem tailTrace_372341 : CollatzResearch.WordTrace tailWord_372341 prefixEnd_372341 169946578111851509177903 := by
  unfold tailWord_372341
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580391944079622625188877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9053594629386415083459251 13580391944079622625188877)
  ·
    refine ⟨5092646979029858484445829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13580391944079622625188877 5092646979029858484445829)
    ·
      refine ⟨954871308568098465833593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5092646979029858484445829 954871308568098465833593)
      ·
        refine ⟨716153481426073849375195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954871308568098465833593 716153481426073849375195)
        ·
          refine ⟨1074230222139110774062793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716153481426073849375195 1074230222139110774062793)
          ·
            refine ⟨805672666604333080547095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074230222139110774062793 805672666604333080547095)
            ·
              refine ⟨1208508999906499620820643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805672666604333080547095 1208508999906499620820643)
              ·
                refine ⟨1812763499859749431230965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208508999906499620820643 1812763499859749431230965)
                ·
                  refine ⟨169946578111851509177903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1812763499859749431230965 169946578111851509177903)
                  ·
                    rfl

theorem cell20_372341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_372341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372341 prefixEnd_372341 := by exact prefixLift 372341
  have htrace : WordTrace (prefixWord ++ tailWord_372341) baseStart_372341 baseEnd_372341 := by
    simpa [prefixWord, tailWord_372341, baseEnd_372341] using wordTrace_append hprefix tailTrace_372341
  have hstable : (prefixWord ++ tailWord_372341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372341).length < 2 ^ (prefixWord ++ tailWord_372341).sum := by decide
  have hdescent : baseEnd_372341 < baseStart_372341 := by decide
  rcases family_descends (prefixWord ++ tailWord_372341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372372 : List Nat := [2, 4, 2, 2, 2, 1, 1, 6]
def baseStart_372372 : Nat := 118140960795 + 372372 * 2 ^ 59
def prefixEnd_372372 : Nat := 4983230072969 + 3 ^ 40 * 372372 * 2
def baseEnd_372372 : Nat := 56653575785517726381481

theorem tailTrace_372372 : CollatzResearch.WordTrace tailWord_372372 prefixEnd_372372 56653575785517726381481 := by
  unfold tailWord_372372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790761303483657459783685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9054348404644876613044913 6790761303483657459783685)
  ·
    refine ⟨1273267744403185773709441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6790761303483657459783685 1273267744403185773709441)
    ·
      refine ⟨954950808302389330282081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1273267744403185773709441 954950808302389330282081)
      ·
        refine ⟨716213106226791997711561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954950808302389330282081 716213106226791997711561)
        ·
          refine ⟨537159829670093998283671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716213106226791997711561 537159829670093998283671)
          ·
            refine ⟨805739744505140997425507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537159829670093998283671 805739744505140997425507)
            ·
              refine ⟨1208609616757711496138261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805739744505140997425507 1208609616757711496138261)
              ·
                refine ⟨56653575785517726381481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1208609616757711496138261 56653575785517726381481)
                ·
                  rfl

theorem cell20_372372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_372372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372372 prefixEnd_372372 := by exact prefixLift 372372
  have htrace : WordTrace (prefixWord ++ tailWord_372372) baseStart_372372 baseEnd_372372 := by
    simpa [prefixWord, tailWord_372372, baseEnd_372372] using wordTrace_append hprefix tailTrace_372372
  have hstable : (prefixWord ++ tailWord_372372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372372).length < 2 ^ (prefixWord ++ tailWord_372372).sum := by decide
  have hdescent : baseEnd_372372 < baseStart_372372 := by decide
  rcases family_descends (prefixWord ++ tailWord_372372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372382 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_372382 : Nat := 118140960795 + 372382 * 2 ^ 59
def prefixEnd_372382 : Nat := 4983230072969 + 3 ^ 40 * 372382 * 2
def baseEnd_372382 : Nat := 169965291629037588811069

theorem tailTrace_372382 : CollatzResearch.WordTrace tailWord_372382 prefixEnd_372382 169965291629037588811069 := by
  unfold tailWord_372382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1697735917116385828428925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9054591557954057751620933 1697735917116385828428925)
  ·
    refine ⟨636650968918644685660847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1697735917116385828428925 636650968918644685660847)
    ·
      refine ⟨954976453377967028491271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636650968918644685660847 954976453377967028491271)
      ·
        refine ⟨1432464680066950542736907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954976453377967028491271 1432464680066950542736907)
        ·
          refine ⟨2148697020100425814105361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432464680066950542736907 2148697020100425814105361)
          ·
            refine ⟨1611522765075319360579021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2148697020100425814105361 1611522765075319360579021)
            ·
              refine ⟨604321036903244760217133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1611522765075319360579021 604321036903244760217133)
              ·
                refine ⟨226620388838716785081425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604321036903244760217133 226620388838716785081425)
                ·
                  refine ⟨169965291629037588811069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226620388838716785081425 169965291629037588811069)
                  ·
                    rfl

theorem cell20_372382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_372382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372382 prefixEnd_372382 := by exact prefixLift 372382
  have htrace : WordTrace (prefixWord ++ tailWord_372382) baseStart_372382 baseEnd_372382 := by
    simpa [prefixWord, tailWord_372382, baseEnd_372382] using wordTrace_append hprefix tailTrace_372382
  have hstable : (prefixWord ++ tailWord_372382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372382).length < 2 ^ (prefixWord ++ tailWord_372382).sum := by decide
  have hdescent : baseEnd_372382 < baseStart_372382 := by decide
  rcases family_descends (prefixWord ++ tailWord_372382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372403 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 2]
def baseStart_372403 : Nat := 118140960795 + 372403 * 2 ^ 59
def prefixEnd_372403 : Nat := 4983230072969 + 3 ^ 40 * 372403 * 2
def baseEnd_372403 : Nat := 169974876601254849110983

theorem tailTrace_372403 : CollatzResearch.WordTrace tailWord_372403 prefixEnd_372403 169974876601254849110983 := by
  unfold tailWord_372403
  simp only [CollatzResearch.WordTrace]
  refine ⟨13582653269855007213945863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9055102179903338142630575 13582653269855007213945863)
  ·
    refine ⟨20373979904782510820918795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13582653269855007213945863 20373979904782510820918795)
    ·
      refine ⟨30560969857173766231378193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20373979904782510820918795 30560969857173766231378193)
      ·
        refine ⟨22920727392880324673533645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30560969857173766231378193 22920727392880324673533645)
        ·
          refine ⟨8595272772330121752575117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22920727392880324673533645 8595272772330121752575117)
          ·
            refine ⟨3223227289623795657215669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8595272772330121752575117 3223227289623795657215669)
            ·
              refine ⟨302177558402230842863969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3223227289623795657215669 302177558402230842863969)
              ·
                refine ⟨226633168801673132147977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302177558402230842863969 226633168801673132147977)
                ·
                  refine ⟨169974876601254849110983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226633168801673132147977 169974876601254849110983)
                  ·
                    rfl

theorem cell20_372403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 2].length) (baseStart_372403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372403 prefixEnd_372403 := by exact prefixLift 372403
  have htrace : WordTrace (prefixWord ++ tailWord_372403) baseStart_372403 baseEnd_372403 := by
    simpa [prefixWord, tailWord_372403, baseEnd_372403] using wordTrace_append hprefix tailTrace_372403
  have hstable : (prefixWord ++ tailWord_372403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372403).length < 2 ^ (prefixWord ++ tailWord_372403).sum := by decide
  have hdescent : baseEnd_372403 < baseStart_372403 := by decide
  rcases family_descends (prefixWord ++ tailWord_372403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372459 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_372459 : Nat := 118140960795 + 372459 * 2 ^ 59
def prefixEnd_372459 : Nat := 4983230072969 + 3 ^ 40 * 372459 * 2
def baseEnd_372459 : Nat := 170000436527167543244087

theorem tailTrace_372459 : CollatzResearch.WordTrace tailWord_372459 prefixEnd_372459 170000436527167543244087 := by
  unfold tailWord_372459
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584695757652128777984431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9056463838434752518656287 13584695757652128777984431)
  ·
    refine ⟨20377043636478193166976647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13584695757652128777984431 20377043636478193166976647)
    ·
      refine ⟨30565565454717289750464971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20377043636478193166976647 30565565454717289750464971)
      ·
        refine ⟨45848348182075934625697457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30565565454717289750464971 45848348182075934625697457)
        ·
          refine ⟨34386261136556950969273093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45848348182075934625697457 34386261136556950969273093)
          ·
            refine ⟨6447423963104428306738705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34386261136556950969273093 6447423963104428306738705)
            ·
              refine ⟨4835567972328321230054029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447423963104428306738705 4835567972328321230054029)
              ·
                refine ⟨1813337989623120461270261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835567972328321230054029 1813337989623120461270261)
                ·
                  refine ⟨170000436527167543244087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813337989623120461270261 170000436527167543244087)
                  ·
                    rfl

theorem cell20_372459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_372459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372459 prefixEnd_372459 := by exact prefixLift 372459
  have htrace : WordTrace (prefixWord ++ tailWord_372459) baseStart_372459 baseEnd_372459 := by
    simpa [prefixWord, tailWord_372459, baseEnd_372459] using wordTrace_append hprefix tailTrace_372459
  have hstable : (prefixWord ++ tailWord_372459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372459).length < 2 ^ (prefixWord ++ tailWord_372459).sum := by decide
  have hdescent : baseEnd_372459 < baseStart_372459 := by decide
  rcases family_descends (prefixWord ++ tailWord_372459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372476 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_372476 : Nat := 118140960795 + 372476 * 2 ^ 59
def prefixEnd_372476 : Nat := 4983230072969 + 3 ^ 40 * 372476 * 2
def baseEnd_372476 : Nat := 170008195790391039677351

theorem tailTrace_372476 : CollatzResearch.WordTrace tailWord_372476 prefixEnd_372476 170008195790391039677351 := by
  unfold tailWord_372476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792657899295270340676641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9056877199060360454235521 6792657899295270340676641)
  ·
    refine ⟨5094493424471452755507481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6792657899295270340676641 5094493424471452755507481)
    ·
      refine ⟨3820870068353589566630611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5094493424471452755507481 3820870068353589566630611)
      ·
        refine ⟨5731305102530384349945917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820870068353589566630611 5731305102530384349945917)
        ·
          refine ⟨2149239413448894131229719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5731305102530384349945917 2149239413448894131229719)
          ·
            refine ⟨3223859120173341196844579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149239413448894131229719 3223859120173341196844579)
            ·
              refine ⟨4835788680260011795266869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3223859120173341196844579 4835788680260011795266869)
              ·
                refine ⟨453355188774376105806269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4835788680260011795266869 453355188774376105806269)
                ·
                  refine ⟨170008195790391039677351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453355188774376105806269 170008195790391039677351)
                  ·
                    rfl

theorem cell20_372476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_372476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372476 prefixEnd_372476 := by exact prefixLift 372476
  have htrace : WordTrace (prefixWord ++ tailWord_372476) baseStart_372476 baseEnd_372476 := by
    simpa [prefixWord, tailWord_372476, baseEnd_372476] using wordTrace_append hprefix tailTrace_372476
  have hstable : (prefixWord ++ tailWord_372476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372476).length < 2 ^ (prefixWord ++ tailWord_372476).sum := by decide
  have hdescent : baseEnd_372476 < baseStart_372476 := by decide
  rcases family_descends (prefixWord ++ tailWord_372476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372497 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_372497 : Nat := 118140960795 + 372497 * 2 ^ 59
def prefixEnd_372497 : Nat := 4983230072969 + 3 ^ 40 * 372497 * 2
def baseEnd_372497 : Nat := 170017780762608299977265

theorem tailTrace_372497 : CollatzResearch.WordTrace tailWord_372497 prefixEnd_372497 170017780762608299977265 := by
  unfold tailWord_372497
  simp only [CollatzResearch.WordTrace]
  refine ⟨13586081731514461267867745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9057387821009640845245163 13586081731514461267867745)
  ·
    refine ⟨10189561298635845950900809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13586081731514461267867745 10189561298635845950900809)
    ·
      refine ⟨7642170973976884463175607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10189561298635845950900809 7642170973976884463175607)
      ·
        refine ⟨11463256460965326694763411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7642170973976884463175607 11463256460965326694763411)
        ·
          refine ⟨17194884691447990042145117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11463256460965326694763411 17194884691447990042145117)
          ·
            refine ⟨6448081759292996265804419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17194884691447990042145117 6448081759292996265804419)
            ·
              refine ⟨9672122638939494398706629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448081759292996265804419 9672122638939494398706629)
              ·
                refine ⟨1813522994801155199757493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9672122638939494398706629 1813522994801155199757493)
                ·
                  refine ⟨170017780762608299977265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813522994801155199757493 170017780762608299977265)
                  ·
                    rfl

theorem cell20_372497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_372497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372497 prefixEnd_372497 := by exact prefixLift 372497
  have htrace : WordTrace (prefixWord ++ tailWord_372497) baseStart_372497 baseEnd_372497 := by
    simpa [prefixWord, tailWord_372497, baseEnd_372497] using wordTrace_append hprefix tailTrace_372497
  have hstable : (prefixWord ++ tailWord_372497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372497).length < 2 ^ (prefixWord ++ tailWord_372497).sum := by decide
  have hdescent : baseEnd_372497 < baseStart_372497 := by decide
  rcases family_descends (prefixWord ++ tailWord_372497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372514 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_372514 : Nat := 118140960795 + 372514 * 2 ^ 59
def prefixEnd_372514 : Nat := 4983230072969 + 3 ^ 40 * 372514 * 2
def baseEnd_372514 : Nat := 170025540025831796410529

theorem tailTrace_372514 : CollatzResearch.WordTrace tailWord_372514 prefixEnd_372514 170025540025831796410529 := by
  unfold tailWord_372514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396675443113218292809149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9057801181635248780824397 3396675443113218292809149)
  ·
    refine ⟨1273753291167456859803431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3396675443113218292809149 1273753291167456859803431)
    ·
      refine ⟨1910629936751185289705147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273753291167456859803431 1910629936751185289705147)
      ·
        refine ⟨2865944905126777934557721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910629936751185289705147 2865944905126777934557721)
        ·
          refine ⟨2149458678845083450918291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2865944905126777934557721 2149458678845083450918291)
          ·
            refine ⟨3224188018267625176377437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149458678845083450918291 3224188018267625176377437)
            ·
              refine ⟨1209070506850359441141539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3224188018267625176377437 1209070506850359441141539)
              ·
                refine ⟨1813605760275539161712309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209070506850359441141539 1813605760275539161712309)
                ·
                  refine ⟨170025540025831796410529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813605760275539161712309 170025540025831796410529)
                  ·
                    rfl

theorem cell20_372514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_372514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372514 prefixEnd_372514 := by exact prefixLift 372514
  have htrace : WordTrace (prefixWord ++ tailWord_372514) baseStart_372514 baseEnd_372514 := by
    simpa [prefixWord, tailWord_372514, baseEnd_372514] using wordTrace_append hprefix tailTrace_372514
  have hstable : (prefixWord ++ tailWord_372514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372514).length < 2 ^ (prefixWord ++ tailWord_372514).sum := by decide
  have hdescent : baseEnd_372514 < baseStart_372514 := by decide
  rcases family_descends (prefixWord ++ tailWord_372514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372572 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 4]
def baseStart_372572 : Nat := 118140960795 + 372572 * 2 ^ 59
def prefixEnd_372572 : Nat := 4983230072969 + 3 ^ 40 * 372572 * 2
def baseEnd_372572 : Nat := 170052012806241372476959

theorem tailTrace_372572 : CollatzResearch.WordTrace tailWord_372572 prefixEnd_372572 170052012806241372476959 := by
  unfold tailWord_372572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794408603121374538423985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9059211470828499384565313 6794408603121374538423985)
  ·
    refine ⟨5095806452341030903817989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6794408603121374538423985 5095806452341030903817989)
    ·
      refine ⟨955463709813943294465873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5095806452341030903817989 955463709813943294465873)
      ·
        refine ⟨716597782360457470849405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955463709813943294465873 716597782360457470849405)
        ·
          refine ⟨268724168385171551568527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716597782360457470849405 268724168385171551568527)
          ·
            refine ⟨403086252577757327352791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268724168385171551568527 403086252577757327352791)
            ·
              refine ⟨604629378866635991029187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403086252577757327352791 604629378866635991029187)
              ·
                refine ⟨906944068299953986543781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604629378866635991029187 906944068299953986543781)
                ·
                  refine ⟨170052012806241372476959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906944068299953986543781 170052012806241372476959)
                  ·
                    rfl

theorem cell20_372572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_372572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372572 prefixEnd_372572 := by exact prefixLift 372572
  have htrace : WordTrace (prefixWord ++ tailWord_372572) baseStart_372572 baseEnd_372572 := by
    simpa [prefixWord, tailWord_372572, baseEnd_372572] using wordTrace_append hprefix tailTrace_372572
  have hstable : (prefixWord ++ tailWord_372572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372572).length < 2 ^ (prefixWord ++ tailWord_372572).sum := by decide
  have hdescent : baseEnd_372572 < baseStart_372572 := by decide
  rcases family_descends (prefixWord ++ tailWord_372572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372576 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_372576 : Nat := 118140960795 + 372576 * 2 ^ 59
def prefixEnd_372576 : Nat := 4983230072969 + 3 ^ 40 * 372576 * 2
def baseEnd_372576 : Nat := 170053838515235136343609

theorem tailTrace_372576 : CollatzResearch.WordTrace tailWord_372576 prefixEnd_372576 170053838515235136343609 := by
  unfold tailWord_372576
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794481549114128879996791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9059308732152171839995721 6794481549114128879996791)
  ·
    refine ⟨10191722323671193319995187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6794481549114128879996791 10191722323671193319995187)
    ·
      refine ⟨15287583485506789979992781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10191722323671193319995187 15287583485506789979992781)
      ·
        refine ⟨5732843807065046242497293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15287583485506789979992781 5732843807065046242497293)
        ·
          refine ⟨2149816427649392340936485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5732843807065046242497293 2149816427649392340936485)
          ·
            refine ⟨403090580184261063925591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2149816427649392340936485 403090580184261063925591)
            ·
              refine ⟨604635870276391595888387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403090580184261063925591 604635870276391595888387)
              ·
                refine ⟨906953805414587393832581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604635870276391595888387 906953805414587393832581)
                ·
                  refine ⟨170053838515235136343609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906953805414587393832581 170053838515235136343609)
                  ·
                    rfl

theorem cell20_372576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_372576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372576 prefixEnd_372576 := by exact prefixLift 372576
  have htrace : WordTrace (prefixWord ++ tailWord_372576) baseStart_372576 baseEnd_372576 := by
    simpa [prefixWord, tailWord_372576, baseEnd_372576] using wordTrace_append hprefix tailTrace_372576
  have hstable : (prefixWord ++ tailWord_372576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372576).length < 2 ^ (prefixWord ++ tailWord_372576).sum := by decide
  have hdescent : baseEnd_372576 < baseStart_372576 := by decide
  rcases family_descends (prefixWord ++ tailWord_372576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372586 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_372586 : Nat := 118140960795 + 372586 * 2 ^ 59
def prefixEnd_372586 : Nat := 4983230072969 + 3 ^ 40 * 372586 * 2
def baseEnd_372586 : Nat := 170058402787719546010235

theorem tailTrace_372586 : CollatzResearch.WordTrace tailWord_372586 prefixEnd_372586 170058402787719546010235 := by
  unfold tailWord_372586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397331957048007366964403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9059551885461352978571741 3397331957048007366964403)
  ·
    refine ⟨5095997935572011050446605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3397331957048007366964403 5095997935572011050446605)
    ·
      refine ⟨1910999225839504143917477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5095997935572011050446605 1910999225839504143917477)
      ·
        refine ⟨358312354844907026984527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1910999225839504143917477 358312354844907026984527)
        ·
          refine ⟨537468532267360540476791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358312354844907026984527 537468532267360540476791)
          ·
            refine ⟨806202798401040810715187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537468532267360540476791 806202798401040810715187)
            ·
              refine ⟨1209304197601561216072781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806202798401040810715187 1209304197601561216072781)
              ·
                refine ⟨453489074100585456027293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209304197601561216072781 453489074100585456027293)
                ·
                  refine ⟨170058402787719546010235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453489074100585456027293 170058402787719546010235)
                  ·
                    rfl

theorem cell20_372586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_372586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372586 prefixEnd_372586 := by exact prefixLift 372586
  have htrace : WordTrace (prefixWord ++ tailWord_372586) baseStart_372586 baseEnd_372586 := by
    simpa [prefixWord, tailWord_372586, baseEnd_372586] using wordTrace_append hprefix tailTrace_372586
  have hstable : (prefixWord ++ tailWord_372586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372586).length < 2 ^ (prefixWord ++ tailWord_372586).sum := by decide
  have hdescent : baseEnd_372586 < baseStart_372586 := by decide
  rcases family_descends (prefixWord ++ tailWord_372586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372597 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_372597 : Nat := 118140960795 + 372597 * 2 ^ 59
def prefixEnd_372597 : Nat := 4983230072969 + 3 ^ 40 * 372597 * 2
def baseEnd_372597 : Nat := 170063423487452396643523

theorem tailTrace_372597 : CollatzResearch.WordTrace tailWord_372597 prefixEnd_372597 170063423487452396643523 := by
  unfold tailWord_372597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589729031152178346508045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9059819354101452231005363 13589729031152178346508045)
  ·
    refine ⟨5096148386682066879940517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13589729031152178346508045 5096148386682066879940517)
    ·
      refine ⟨955527822502887539988847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5096148386682066879940517 955527822502887539988847)
      ·
        refine ⟨1433291733754331309983271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955527822502887539988847 1433291733754331309983271)
        ·
          refine ⟨2149937600631496964974907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433291733754331309983271 2149937600631496964974907)
          ·
            refine ⟨3224906400947245447462361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149937600631496964974907 3224906400947245447462361)
            ·
              refine ⟨2418679800710434085596771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3224906400947245447462361 2418679800710434085596771)
              ·
                refine ⟨3628019701065651128395157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418679800710434085596771 3628019701065651128395157)
                ·
                  refine ⟨170063423487452396643523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3628019701065651128395157 170063423487452396643523)
                  ·
                    rfl

theorem cell20_372597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_372597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372597 prefixEnd_372597 := by exact prefixLift 372597
  have htrace : WordTrace (prefixWord ++ tailWord_372597) baseStart_372597 baseEnd_372597 := by
    simpa [prefixWord, tailWord_372597, baseEnd_372597] using wordTrace_append hprefix tailTrace_372597
  have hstable : (prefixWord ++ tailWord_372597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372597).length < 2 ^ (prefixWord ++ tailWord_372597).sum := by decide
  have hdescent : baseEnd_372597 < baseStart_372597 := by decide
  rcases family_descends (prefixWord ++ tailWord_372597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372631 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 2]
def baseStart_372631 : Nat := 118140960795 + 372631 * 2 ^ 59
def prefixEnd_372631 : Nat := 4983230072969 + 3 ^ 40 * 372631 * 2
def baseEnd_372631 : Nat := 170078942013899389510051

theorem tailTrace_372631 : CollatzResearch.WordTrace tailWord_372631 prefixEnd_372631 170078942013899389510051 := by
  unfold tailWord_372631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13590969113029002153245747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9060646075352668102163831 13590969113029002153245747)
  ·
    refine ⟨20386453669543503229868621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13590969113029002153245747 20386453669543503229868621)
    ·
      refine ⟨7644920126078813711200733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20386453669543503229868621 7644920126078813711200733)
      ·
        refine ⟨2866845047279555141700275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7644920126078813711200733 2866845047279555141700275)
        ·
          refine ⟨4300267570919332712550413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866845047279555141700275 4300267570919332712550413)
          ·
            refine ⟨1612600339094749767206405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4300267570919332712550413 1612600339094749767206405)
            ·
              refine ⟨302362563580265581351201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1612600339094749767206405 302362563580265581351201)
              ·
                refine ⟨226771922685199186013401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302362563580265581351201 226771922685199186013401)
                ·
                  refine ⟨170078942013899389510051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226771922685199186013401 170078942013899389510051)
                  ·
                    rfl

theorem cell20_372631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 2].length) (baseStart_372631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372631 prefixEnd_372631 := by exact prefixLift 372631
  have htrace : WordTrace (prefixWord ++ tailWord_372631) baseStart_372631 baseEnd_372631 := by
    simpa [prefixWord, tailWord_372631, baseEnd_372631] using wordTrace_append hprefix tailTrace_372631
  have hstable : (prefixWord ++ tailWord_372631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372631).length < 2 ^ (prefixWord ++ tailWord_372631).sum := by decide
  have hdescent : baseEnd_372631 < baseStart_372631 := by decide
  rcases family_descends (prefixWord ++ tailWord_372631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372669 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 2]
def baseStart_372669 : Nat := 118140960795 + 372669 * 2 ^ 59
def prefixEnd_372669 : Nat := 4983230072969 + 3 ^ 40 * 372669 * 2
def baseEnd_372669 : Nat := 170096286249340146243229

theorem tailTrace_372669 : CollatzResearch.WordTrace tailWord_372669 prefixEnd_372669 170096286249340146243229 := by
  unfold tailWord_372669
  simp only [CollatzResearch.WordTrace]
  refine ⟨13592355086891334643129061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9061570057927556428752707 13592355086891334643129061)
  ·
    refine ⟨2548566578792125245586699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13592355086891334643129061 2548566578792125245586699)
    ·
      refine ⟨3822849868188187868380049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548566578792125245586699 3822849868188187868380049)
      ·
        refine ⟨2867137401141140901285037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3822849868188187868380049 2867137401141140901285037)
        ·
          refine ⟨1075176525427927837981889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2867137401141140901285037 1075176525427927837981889)
          ·
            refine ⟨806382394070945878486417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075176525427927837981889 806382394070945878486417)
            ·
              refine ⟨604786795553209408864813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806382394070945878486417 604786795553209408864813)
              ·
                refine ⟨226795048332453528324305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604786795553209408864813 226795048332453528324305)
                ·
                  refine ⟨170096286249340146243229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226795048332453528324305 170096286249340146243229)
                  ·
                    rfl

theorem cell20_372669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_372669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372669 prefixEnd_372669 := by exact prefixLift 372669
  have htrace : WordTrace (prefixWord ++ tailWord_372669) baseStart_372669 baseEnd_372669 := by
    simpa [prefixWord, tailWord_372669, baseEnd_372669] using wordTrace_append hprefix tailTrace_372669
  have hstable : (prefixWord ++ tailWord_372669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372669).length < 2 ^ (prefixWord ++ tailWord_372669).sum := by decide
  have hdescent : baseEnd_372669 < baseStart_372669 := by decide
  rcases family_descends (prefixWord ++ tailWord_372669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372680 : List Nat := [2, 1, 3, 1, 4, 2, 7]
def baseStart_372680 : Nat := 118140960795 + 372680 * 2 ^ 59
def prefixEnd_372680 : Nat := 4983230072969 + 3 ^ 40 * 372680 * 2
def baseEnd_372680 : Nat := 18900145216563666319613

theorem tailTrace_372680 : CollatzResearch.WordTrace tailWord_372680 prefixEnd_372680 18900145216563666319613 := by
  unfold tailWord_372680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796378144925741760889747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9061837526567655681186329 6796378144925741760889747)
  ·
    refine ⟨10194567217388612641334621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6796378144925741760889747 10194567217388612641334621)
    ·
      refine ⟨3822962706520729740500483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10194567217388612641334621 3822962706520729740500483)
      ·
        refine ⟨5734444059781094610750725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822962706520729740500483 5734444059781094610750725)
        ·
          refine ⟨1075208261208955239515761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5734444059781094610750725 1075208261208955239515761)
          ·
            refine ⟨806406195906716429636821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075208261208955239515761 806406195906716429636821)
            ·
              refine ⟨18900145216563666319613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 806406195906716429636821 18900145216563666319613)
              ·
                rfl

theorem cell20_372680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_372680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372680 prefixEnd_372680 := by exact prefixLift 372680
  have htrace : WordTrace (prefixWord ++ tailWord_372680) baseStart_372680 baseEnd_372680 := by
    simpa [prefixWord, tailWord_372680, baseEnd_372680] using wordTrace_append hprefix tailTrace_372680
  have hstable : (prefixWord ++ tailWord_372680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372680).length < 2 ^ (prefixWord ++ tailWord_372680).sum := by decide
  have hdescent : baseEnd_372680 < baseStart_372680 := by decide
  rcases family_descends (prefixWord ++ tailWord_372680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372687 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_372687 : Nat := 118140960795 + 372687 * 2 ^ 59
def prefixEnd_372687 : Nat := 4983230072969 + 3 ^ 40 * 372687 * 2
def baseEnd_372687 : Nat := 170104501939812083643155

theorem tailTrace_372687 : CollatzResearch.WordTrace tailWord_372687 prefixEnd_372687 170104501939812083643155 := by
  unfold tailWord_372687
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593011600826123717284315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9062007733884082478189543 13593011600826123717284315)
  ·
    refine ⟨20389517401239185575926473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13593011600826123717284315 20389517401239185575926473)
    ·
      refine ⟨15292138050929389181944855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20389517401239185575926473 15292138050929389181944855)
      ·
        refine ⟨22938207076394083772917283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15292138050929389181944855 22938207076394083772917283)
        ·
          refine ⟨34407310614591125659375925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22938207076394083772917283 34407310614591125659375925)
          ·
            refine ⟨3225685370117918030566493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34407310614591125659375925 3225685370117918030566493)
            ·
              refine ⟨1209632013794219261462435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3225685370117918030566493 1209632013794219261462435)
              ·
                refine ⟨1814448020691328892193653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209632013794219261462435 1814448020691328892193653)
                ·
                  refine ⟨170104501939812083643155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1814448020691328892193653 170104501939812083643155)
                  ·
                    rfl

theorem cell20_372687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_372687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372687 prefixEnd_372687 := by exact prefixLift 372687
  have htrace : WordTrace (prefixWord ++ tailWord_372687) baseStart_372687 baseEnd_372687 := by
    simpa [prefixWord, tailWord_372687, baseEnd_372687] using wordTrace_append hprefix tailTrace_372687
  have hstable : (prefixWord ++ tailWord_372687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372687).length < 2 ^ (prefixWord ++ tailWord_372687).sum := by decide
  have hdescent : baseEnd_372687 < baseStart_372687 := by decide
  rcases family_descends (prefixWord ++ tailWord_372687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372728 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 2]
def baseStart_372728 : Nat := 118140960795 + 372728 * 2 ^ 59
def prefixEnd_372728 : Nat := 4983230072969 + 3 ^ 40 * 372728 * 2
def baseEnd_372728 : Nat := 170123215456998163276321

theorem tailTrace_372728 : CollatzResearch.WordTrace tailWord_372728 prefixEnd_372728 170123215456998163276321 := by
  unfold tailWord_372728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797253496838793859763419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9063004662451725146351225 6797253496838793859763419)
  ·
    refine ⟨10195880245258190789645129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6797253496838793859763419 10195880245258190789645129)
    ·
      refine ⟨7646910183943643092233847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10195880245258190789645129 7646910183943643092233847)
      ·
        refine ⟨11470365275915464638350771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646910183943643092233847 11470365275915464638350771)
        ·
          refine ⟨17205547913873196957526157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11470365275915464638350771 17205547913873196957526157)
          ·
            refine ⟨6452080467702448859072309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17205547913873196957526157 6452080467702448859072309)
            ·
              refine ⟨604882543847104580538029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6452080467702448859072309 604882543847104580538029)
              ·
                refine ⟨226830953942664217701761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604882543847104580538029 226830953942664217701761)
                ·
                  refine ⟨170123215456998163276321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226830953942664217701761 170123215456998163276321)
                  ·
                    rfl

theorem cell20_372728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_372728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372728 prefixEnd_372728 := by exact prefixLift 372728
  have htrace : WordTrace (prefixWord ++ tailWord_372728) baseStart_372728 baseEnd_372728 := by
    simpa [prefixWord, tailWord_372728, baseEnd_372728] using wordTrace_append hprefix tailTrace_372728
  have hstable : (prefixWord ++ tailWord_372728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372728).length < 2 ^ (prefixWord ++ tailWord_372728).sum := by decide
  have hdescent : baseEnd_372728 < baseStart_372728 := by decide
  rcases family_descends (prefixWord ++ tailWord_372728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372759 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_372759 : Nat := 118140960795 + 372759 * 2 ^ 59
def prefixEnd_372759 : Nat := 4983230072969 + 3 ^ 40 * 372759 * 2
def baseEnd_372759 : Nat := 170137364701699833242861

theorem tailTrace_372759 : CollatzResearch.WordTrace tailWord_372759 prefixEnd_372759 170137364701699833242861 := by
  unfold tailWord_372759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595637656565280013905331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9063758437710186675936887 13595637656565280013905331)
  ·
    refine ⟨20393456484847920020857997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13595637656565280013905331 20393456484847920020857997)
    ·
      refine ⟨7647546181817970007821749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20393456484847920020857997 7647546181817970007821749)
      ·
        refine ⟨716957454545434688233289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7647546181817970007821749 716957454545434688233289)
        ·
          refine ⟨537718090909076016174967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716957454545434688233289 537718090909076016174967)
          ·
            refine ⟨806577136363614024262451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537718090909076016174967 806577136363614024262451)
            ·
              refine ⟨1209865704545421036393677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806577136363614024262451 1209865704545421036393677)
              ·
                refine ⟨453699639204532888647629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209865704545421036393677 453699639204532888647629)
                ·
                  refine ⟨170137364701699833242861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453699639204532888647629 170137364701699833242861)
                  ·
                    rfl

theorem cell20_372759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_372759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372759 prefixEnd_372759 := by exact prefixLift 372759
  have htrace : WordTrace (prefixWord ++ tailWord_372759) baseStart_372759 baseEnd_372759 := by
    simpa [prefixWord, tailWord_372759, baseEnd_372759] using wordTrace_append hprefix tailTrace_372759
  have hstable : (prefixWord ++ tailWord_372759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372759).length < 2 ^ (prefixWord ++ tailWord_372759).sum := by decide
  have hdescent : baseEnd_372759 < baseStart_372759 := by decide
  rcases family_descends (prefixWord ++ tailWord_372759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372839 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_372839 : Nat := 118140960795 + 372839 * 2 ^ 59
def prefixEnd_372839 : Nat := 4983230072969 + 3 ^ 40 * 372839 * 2
def baseEnd_372839 : Nat := 170173878881575110575867

theorem tailTrace_372839 : CollatzResearch.WordTrace tailWord_372839 prefixEnd_372839 170173878881575110575867 := by
  unfold tailWord_372839
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598555496275453676817571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9065703664183635784545047 13598555496275453676817571)
  ·
    refine ⟨20397833244413180515226357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13598555496275453676817571 20397833244413180515226357)
    ·
      refine ⟨1912296866663735673302471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20397833244413180515226357 1912296866663735673302471)
      ·
        refine ⟨2868445299995603509953707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912296866663735673302471 2868445299995603509953707)
        ·
          refine ⟨4302667949993405264930561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868445299995603509953707 4302667949993405264930561)
          ·
            refine ⟨3227000962495053948697921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4302667949993405264930561 3227000962495053948697921)
            ·
              refine ⟨2420250721871290461523441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227000962495053948697921 2420250721871290461523441)
              ·
                refine ⟨1815188041403467846142581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420250721871290461523441 1815188041403467846142581)
                ·
                  refine ⟨170173878881575110575867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1815188041403467846142581 170173878881575110575867)
                  ·
                    rfl

theorem cell20_372839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_372839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372839 prefixEnd_372839 := by exact prefixLift 372839
  have htrace : WordTrace (prefixWord ++ tailWord_372839) baseStart_372839 baseEnd_372839 := by
    simpa [prefixWord, tailWord_372839, baseEnd_372839] using wordTrace_append hprefix tailTrace_372839
  have hstable : (prefixWord ++ tailWord_372839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372839).length < 2 ^ (prefixWord ++ tailWord_372839).sum := by decide
  have hdescent : baseEnd_372839 < baseStart_372839 := by decide
  rcases family_descends (prefixWord ++ tailWord_372839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372897 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 2]
def baseStart_372897 : Nat := 118140960795 + 372897 * 2 ^ 59
def prefixEnd_372897 : Nat := 4983230072969 + 3 ^ 40 * 372897 * 2
def baseEnd_372897 : Nat := 170200351661984686642297

theorem tailTrace_372897 : CollatzResearch.WordTrace tailWord_372897 prefixEnd_372897 170200351661984686642297 := by
  unfold tailWord_372897
  simp only [CollatzResearch.WordTrace]
  refine ⟨13600670930065329582428945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9067113953376886388285963 13600670930065329582428945)
  ·
    refine ⟨10200503197548997186821709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13600670930065329582428945 10200503197548997186821709)
    ·
      refine ⟨3825188699080873945058141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10200503197548997186821709 3825188699080873945058141)
      ·
        refine ⟨1434445762155327729396803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3825188699080873945058141 1434445762155327729396803)
        ·
          refine ⟨2151668643232991594095205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434445762155327729396803 2151668643232991594095205)
          ·
            refine ⟨403437870606185923892851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2151668643232991594095205 403437870606185923892851)
            ·
              refine ⟨605156805909278885839277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403437870606185923892851 605156805909278885839277)
              ·
                refine ⟨226933802215979582189729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 605156805909278885839277 226933802215979582189729)
                ·
                  refine ⟨170200351661984686642297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226933802215979582189729 170200351661984686642297)
                  ·
                    rfl

theorem cell20_372897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_372897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372897 prefixEnd_372897 := by exact prefixLift 372897
  have htrace : WordTrace (prefixWord ++ tailWord_372897) baseStart_372897 baseEnd_372897 := by
    simpa [prefixWord, tailWord_372897, baseEnd_372897] using wordTrace_append hprefix tailTrace_372897
  have hstable : (prefixWord ++ tailWord_372897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372897).length < 2 ^ (prefixWord ++ tailWord_372897).sum := by decide
  have hdescent : baseEnd_372897 < baseStart_372897 := by decide
  rcases family_descends (prefixWord ++ tailWord_372897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372915 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_372915 : Nat := 118140960795 + 372915 * 2 ^ 59
def prefixEnd_372915 : Nat := 4983230072969 + 3 ^ 40 * 372915 * 2
def baseEnd_372915 : Nat := 170208567352456624042223

theorem tailTrace_372915 : CollatzResearch.WordTrace tailWord_372915 prefixEnd_372915 170208567352456624042223 := by
  unfold tailWord_372915
  simp only [CollatzResearch.WordTrace]
  refine ⟨13601327444000118656584199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9067551629333412437722799 13601327444000118656584199)
  ·
    refine ⟨20401991166000177984876299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13601327444000118656584199 20401991166000177984876299)
    ·
      refine ⟨30602986749000266977314449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20401991166000177984876299 30602986749000266977314449)
      ·
        refine ⟨22952240061750200232985837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30602986749000266977314449 22952240061750200232985837)
        ·
          refine ⟨8607090023156325087369689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22952240061750200232985837 8607090023156325087369689)
          ·
            refine ⟨6455317517367243815527267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8607090023156325087369689 6455317517367243815527267)
            ·
              refine ⟨9682976276050865723290901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455317517367243815527267 9682976276050865723290901)
              ·
                refine ⟨453889512939884330779261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9682976276050865723290901 453889512939884330779261)
                ·
                  refine ⟨170208567352456624042223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453889512939884330779261 170208567352456624042223)
                  ·
                    rfl

theorem cell20_372915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_372915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372915 prefixEnd_372915 := by exact prefixLift 372915
  have htrace : WordTrace (prefixWord ++ tailWord_372915) baseStart_372915 baseEnd_372915 := by
    simpa [prefixWord, tailWord_372915, baseEnd_372915] using wordTrace_append hprefix tailTrace_372915
  have hstable : (prefixWord ++ tailWord_372915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372915).length < 2 ^ (prefixWord ++ tailWord_372915).sum := by decide
  have hdescent : baseEnd_372915 < baseStart_372915 := by decide
  rcases family_descends (prefixWord ++ tailWord_372915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372946 : List Nat := [3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_372946 : Nat := 118140960795 + 372946 * 2 ^ 59
def prefixEnd_372946 : Nat := 4983230072969 + 3 ^ 40 * 372946 * 2
def baseEnd_372946 : Nat := 56740905532386098002921

theorem tailTrace_372946 : CollatzResearch.WordTrace tailWord_372946 prefixEnd_372946 56740905532386098002921 := by
  unfold tailWord_372946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400614526721952737740673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9068305404591873967308461 3400614526721952737740673)
  ·
    refine ⟨2550460895041464553305505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3400614526721952737740673 2550460895041464553305505)
    ·
      refine ⟨1912845671281098414979129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550460895041464553305505 1912845671281098414979129)
      ·
        refine ⟨1434634253460823811234347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912845671281098414979129 1434634253460823811234347)
        ·
          refine ⟨2151951380191235716851521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434634253460823811234347 2151951380191235716851521)
          ·
            refine ⟨1613963535143426787638641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151951380191235716851521 1613963535143426787638641)
            ·
              refine ⟨1210472651357570090728981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613963535143426787638641 1210472651357570090728981)
              ·
                refine ⟨56740905532386098002921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1210472651357570090728981 56740905532386098002921)
                ·
                  rfl

theorem cell20_372946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_372946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372946 prefixEnd_372946 := by exact prefixLift 372946
  have htrace : WordTrace (prefixWord ++ tailWord_372946) baseStart_372946 baseEnd_372946 := by
    simpa [prefixWord, tailWord_372946, baseEnd_372946] using wordTrace_append hprefix tailTrace_372946
  have hstable : (prefixWord ++ tailWord_372946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372946).length < 2 ^ (prefixWord ++ tailWord_372946).sum := by decide
  have hdescent : baseEnd_372946 < baseStart_372946 := by decide
  rcases family_descends (prefixWord ++ tailWord_372946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372963 : List Nat := [1, 1, 1, 8, 2, 7]
def baseStart_372963 : Nat := 118140960795 + 372963 * 2 ^ 59
def prefixEnd_372963 : Nat := 4983230072969 + 3 ^ 40 * 372963 * 2
def baseEnd_372963 : Nat := 6304832439273399646001

theorem tailTrace_372963 : CollatzResearch.WordTrace tailWord_372963 prefixEnd_372963 6304832439273399646001 := by
  unfold tailWord_372963
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603078147826222854331543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9068718765217481902887695 13603078147826222854331543)
  ·
    refine ⟨20404617221739334281497315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13603078147826222854331543 20404617221739334281497315)
    ·
      refine ⟨30606925832609001422245973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20404617221739334281497315 30606925832609001422245973)
      ·
        refine ⟨358674912100886735416945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 30606925832609001422245973 358674912100886735416945)
        ·
          refine ⟨269006184075665051562709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358674912100886735416945 269006184075665051562709)
          ·
            refine ⟨6304832439273399646001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 269006184075665051562709 6304832439273399646001)
            ·
              rfl

theorem cell20_372963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 7].length) (baseStart_372963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372963 prefixEnd_372963 := by exact prefixLift 372963
  have htrace : WordTrace (prefixWord ++ tailWord_372963) baseStart_372963 baseEnd_372963 := by
    simpa [prefixWord, tailWord_372963, baseEnd_372963] using wordTrace_append hprefix tailTrace_372963
  have hstable : (prefixWord ++ tailWord_372963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372963).length < 2 ^ (prefixWord ++ tailWord_372963).sum := by decide
  have hdescent : baseEnd_372963 < baseStart_372963 := by decide
  rcases family_descends (prefixWord ++ tailWord_372963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372970 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_372970 : Nat := 118140960795 + 372970 * 2 ^ 59
def prefixEnd_372970 : Nat := 4983230072969 + 3 ^ 40 * 372970 * 2
def baseEnd_372970 : Nat := 170233670851120877208665

theorem tailTrace_372970 : CollatzResearch.WordTrace tailWord_372970 prefixEnd_372970 170233670851120877208665 := by
  unfold tailWord_372970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400833364700215762459091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9068888972533908699890909 3400833364700215762459091)
  ·
    refine ⟨5101250047050323643688637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3400833364700215762459091 5101250047050323643688637)
    ·
      refine ⟨1912968767643871366383239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5101250047050323643688637 1912968767643871366383239)
      ·
        refine ⟨2869453151465807049574859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912968767643871366383239 2869453151465807049574859)
        ·
          refine ⟨4304179727198710574362289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869453151465807049574859 4304179727198710574362289)
          ·
            refine ⟨3228134795399032930771717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4304179727198710574362289 3228134795399032930771717)
            ·
              refine ⟨605275274137318674519697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3228134795399032930771717 605275274137318674519697)
              ·
                refine ⟨453956455602989005889773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605275274137318674519697 453956455602989005889773)
                ·
                  refine ⟨170233670851120877208665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453956455602989005889773 170233670851120877208665)
                  ·
                    rfl

theorem cell20_372970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_372970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372970 prefixEnd_372970 := by exact prefixLift 372970
  have htrace : WordTrace (prefixWord ++ tailWord_372970) baseStart_372970 baseEnd_372970 := by
    simpa [prefixWord, tailWord_372970, baseEnd_372970] using wordTrace_append hprefix tailTrace_372970
  have hstable : (prefixWord ++ tailWord_372970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372970).length < 2 ^ (prefixWord ++ tailWord_372970).sum := by decide
  have hdescent : baseEnd_372970 < baseStart_372970 := by decide
  rcases family_descends (prefixWord ++ tailWord_372970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372973 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 2]
def baseStart_372973 : Nat := 118140960795 + 372973 * 2 ^ 59
def prefixEnd_372973 : Nat := 4983230072969 + 3 ^ 40 * 372973 * 2
def baseEnd_372973 : Nat := 170235040132866200108653

theorem tailTrace_372973 : CollatzResearch.WordTrace tailWord_372973 prefixEnd_372973 170235040132866200108653 := by
  unfold tailWord_372973
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603442877789994562195573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9068961918526663041463715 13603442877789994562195573)
  ·
    refine ⟨1275322769792811990205835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13603442877789994562195573 1275322769792811990205835)
    ·
      refine ⟨1912984154689217985308753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275322769792811990205835 1912984154689217985308753)
      ·
        refine ⟨1434738116016913488981565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912984154689217985308753 1434738116016913488981565)
        ·
          refine ⟨538026793506342558368087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1434738116016913488981565 538026793506342558368087)
          ·
            refine ⟨807040190259513837552131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538026793506342558368087 807040190259513837552131)
            ·
              refine ⟨1210560285389270756328197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807040190259513837552131 1210560285389270756328197)
              ·
                refine ⟨226980053510488266811537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1210560285389270756328197 226980053510488266811537)
                ·
                  refine ⟨170235040132866200108653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226980053510488266811537 170235040132866200108653)
                  ·
                    rfl

theorem cell20_372973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_372973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372973 prefixEnd_372973 := by exact prefixLift 372973
  have htrace : WordTrace (prefixWord ++ tailWord_372973) baseStart_372973 baseEnd_372973 := by
    simpa [prefixWord, tailWord_372973, baseEnd_372973] using wordTrace_append hprefix tailTrace_372973
  have hstable : (prefixWord ++ tailWord_372973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372973).length < 2 ^ (prefixWord ++ tailWord_372973).sum := by decide
  have hdescent : baseEnd_372973 < baseStart_372973 := by decide
  rcases family_descends (prefixWord ++ tailWord_372973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372991 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_372991 : Nat := 118140960795 + 372991 * 2 ^ 59
def prefixEnd_372991 : Nat := 4983230072969 + 3 ^ 40 * 372991 * 2
def baseEnd_372991 : Nat := 170243255823338137508579

theorem tailTrace_372991 : CollatzResearch.WordTrace tailWord_372991 prefixEnd_372991 170243255823338137508579 := by
  unfold tailWord_372991
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604099391724783636350827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9069399594483189090900551 13604099391724783636350827)
  ·
    refine ⟨20406149087587175454526241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13604099391724783636350827 20406149087587175454526241)
    ·
      refine ⟨15304611815690381590894681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20406149087587175454526241 15304611815690381590894681)
      ·
        refine ⟨11478458861767786193171011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15304611815690381590894681 11478458861767786193171011)
        ·
          refine ⟨17217688292651679289756517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11478458861767786193171011 17217688292651679289756517)
          ·
            refine ⟨3228316554872189866829347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17217688292651679289756517 3228316554872189866829347)
            ·
              refine ⟨4842474832308284800244021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228316554872189866829347 4842474832308284800244021)
              ·
                refine ⟨453982015528901700022877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4842474832308284800244021 453982015528901700022877)
                ·
                  refine ⟨170243255823338137508579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453982015528901700022877 170243255823338137508579)
                  ·
                    rfl

theorem cell20_372991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_372991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372991 prefixEnd_372991 := by exact prefixLift 372991
  have htrace : WordTrace (prefixWord ++ tailWord_372991) baseStart_372991 baseEnd_372991 := by
    simpa [prefixWord, tailWord_372991, baseEnd_372991] using wordTrace_append hprefix tailTrace_372991
  have hstable : (prefixWord ++ tailWord_372991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372991).length < 2 ^ (prefixWord ++ tailWord_372991).sum := by decide
  have hdescent : baseEnd_372991 < baseStart_372991 := by decide
  rcases family_descends (prefixWord ++ tailWord_372991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372994 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_372994 : Nat := 118140960795 + 372994 * 2 ^ 59
def prefixEnd_372994 : Nat := 4983230072969 + 3 ^ 40 * 372994 * 2
def baseEnd_372994 : Nat := 170244625105083460408567

theorem tailTrace_372994 : CollatzResearch.WordTrace tailWord_372994 prefixEnd_372994 170244625105083460408567 := by
  unfold tailWord_372994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401052202678478787177509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9069472540475943432473357 3401052202678478787177509)
  ·
    refine ⟨637697288002214772595783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3401052202678478787177509 637697288002214772595783)
    ·
      refine ⟨956545932003322158893675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637697288002214772595783 956545932003322158893675)
      ·
        refine ⟨1434818898004983238340513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956545932003322158893675 1434818898004983238340513)
        ·
          refine ⟨1076114173503737428755385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434818898004983238340513 1076114173503737428755385)
          ·
            refine ⟨807085630127803071566539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076114173503737428755385 807085630127803071566539)
            ·
              refine ⟨1210628445191704607349809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807085630127803071566539 1210628445191704607349809)
              ·
                refine ⟨907971333893778455512357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210628445191704607349809 907971333893778455512357)
                ·
                  refine ⟨170244625105083460408567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 907971333893778455512357 170244625105083460408567)
                  ·
                    rfl

theorem cell20_372994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_372994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_372994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_372994 prefixEnd_372994 := by exact prefixLift 372994
  have htrace : WordTrace (prefixWord ++ tailWord_372994) baseStart_372994 baseEnd_372994 := by
    simpa [prefixWord, tailWord_372994, baseEnd_372994] using wordTrace_append hprefix tailTrace_372994
  have hstable : (prefixWord ++ tailWord_372994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372994).length < 2 ^ (prefixWord ++ tailWord_372994).sum := by decide
  have hdescent : baseEnd_372994 < baseStart_372994 := by decide
  rcases family_descends (prefixWord ++ tailWord_372994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373032 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_373032 : Nat := 118140960795 + 373032 * 2 ^ 59
def prefixEnd_373032 : Nat := 4983230072969 + 3 ^ 40 * 373032 * 2
def baseEnd_373032 : Nat := 170261969340524217141745

theorem tailTrace_373032 : CollatzResearch.WordTrace tailWord_373032 prefixEnd_373032 170261969340524217141745 := by
  unfold tailWord_373032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802797392288123819296675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9070396523050831759062233 6802797392288123819296675)
  ·
    refine ⟨10204196088432185728945013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6802797392288123819296675 10204196088432185728945013)
    ·
      refine ⟨956643383290517412088595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10204196088432185728945013 956643383290517412088595)
      ·
        refine ⟨1434965074935776118132893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956643383290517412088595 1434965074935776118132893)
        ·
          refine ⟨538111903100916044299835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1434965074935776118132893 538111903100916044299835)
          ·
            refine ⟨807167854651374066449753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538111903100916044299835 807167854651374066449753)
            ·
              refine ⟨605375890988530549837315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807167854651374066449753 605375890988530549837315)
              ·
                refine ⟨908063836482795824755973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605375890988530549837315 908063836482795824755973)
                ·
                  refine ⟨170261969340524217141745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908063836482795824755973 170261969340524217141745)
                  ·
                    rfl

theorem cell20_373032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_373032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373032 prefixEnd_373032 := by exact prefixLift 373032
  have htrace : WordTrace (prefixWord ++ tailWord_373032) baseStart_373032 baseEnd_373032 := by
    simpa [prefixWord, tailWord_373032, baseEnd_373032] using wordTrace_append hprefix tailTrace_373032
  have hstable : (prefixWord ++ tailWord_373032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373032).length < 2 ^ (prefixWord ++ tailWord_373032).sum := by decide
  have hdescent : baseEnd_373032 < baseStart_373032 := by decide
  rcases family_descends (prefixWord ++ tailWord_373032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373036 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_373036 : Nat := 118140960795 + 373036 * 2 ^ 59
def prefixEnd_373036 : Nat := 4983230072969 + 3 ^ 40 * 373036 * 2
def baseEnd_373036 : Nat := 170263795049517981008395

theorem tailTrace_373036 : CollatzResearch.WordTrace tailWord_373036 prefixEnd_373036 170263795049517981008395 := by
  unfold tailWord_373036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802870338280878160869481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9070493784374504214492641 6802870338280878160869481)
  ·
    refine ⟨5102152753710658620652111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6802870338280878160869481 5102152753710658620652111)
    ·
      refine ⟨7653229130565987930978167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5102152753710658620652111 7653229130565987930978167)
      ·
        refine ⟨11479843695848981896467251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7653229130565987930978167 11479843695848981896467251)
        ·
          refine ⟨17219765543773472844700877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11479843695848981896467251 17219765543773472844700877)
          ·
            refine ⟨6457412078915052316762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17219765543773472844700877 6457412078915052316762829)
            ·
              refine ⟨2421529529593144618786061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6457412078915052316762829 2421529529593144618786061)
              ·
                refine ⟨908073573597429232044773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2421529529593144618786061 908073573597429232044773)
                ·
                  refine ⟨170263795049517981008395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908073573597429232044773 170263795049517981008395)
                  ·
                    rfl

theorem cell20_373036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_373036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373036 prefixEnd_373036 := by exact prefixLift 373036
  have htrace : WordTrace (prefixWord ++ tailWord_373036) baseStart_373036 baseEnd_373036 := by
    simpa [prefixWord, tailWord_373036, baseEnd_373036] using wordTrace_append hprefix tailTrace_373036
  have hstable : (prefixWord ++ tailWord_373036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373036).length < 2 ^ (prefixWord ++ tailWord_373036).sum := by decide
  have hdescent : baseEnd_373036 < baseStart_373036 := by decide
  rcases family_descends (prefixWord ++ tailWord_373036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373043 : List Nat := [1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_373043 : Nat := 118140960795 + 373043 * 2 ^ 59
def prefixEnd_373043 : Nat := 4983230072969 + 3 ^ 40 * 373043 * 2
def baseEnd_373043 : Nat := 56755663346752355925011

theorem tailTrace_373043 : CollatzResearch.WordTrace tailWord_373043 prefixEnd_373043 56755663346752355925011 := by
  unfold tailWord_373043
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605995987536396517243783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9070663991690931011495855 13605995987536396517243783)
  ·
    refine ⟨20408993981304594775865675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13605995987536396517243783 20408993981304594775865675)
    ·
      refine ⟨30613490971956892163798513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20408993981304594775865675 30613490971956892163798513)
      ·
        refine ⟨22960118228967669122848885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30613490971956892163798513 22960118228967669122848885)
        ·
          refine ⟨2152511083965718980267083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22960118228967669122848885 2152511083965718980267083)
          ·
            refine ⟨3228766625948578470400625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152511083965718980267083 3228766625948578470400625)
            ·
              refine ⟨2421574969461433852800469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228766625948578470400625 2421574969461433852800469)
              ·
                refine ⟨56755663346752355925011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2421574969461433852800469 56755663346752355925011)
                ·
                  rfl

theorem cell20_373043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_373043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373043 prefixEnd_373043 := by exact prefixLift 373043
  have htrace : WordTrace (prefixWord ++ tailWord_373043) baseStart_373043 baseEnd_373043 := by
    simpa [prefixWord, tailWord_373043, baseEnd_373043] using wordTrace_append hprefix tailTrace_373043
  have hstable : (prefixWord ++ tailWord_373043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373043).length < 2 ^ (prefixWord ++ tailWord_373043).sum := by decide
  have hdescent : baseEnd_373043 < baseStart_373043 := by decide
  rcases family_descends (prefixWord ++ tailWord_373043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373074 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_373074 : Nat := 118140960795 + 373074 * 2 ^ 59
def prefixEnd_373074 : Nat := 4983230072969 + 3 ^ 40 * 373074 * 2
def baseEnd_373074 : Nat := 170281139284958737741573

theorem tailTrace_373074 : CollatzResearch.WordTrace tailWord_373074 prefixEnd_373074 170281139284958737741573 := by
  unfold tailWord_373074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401781662606022202905569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9071417766949392541081517 3401781662606022202905569)
  ·
    refine ⟨2551336246954516652179177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3401781662606022202905569 2551336246954516652179177)
    ·
      refine ⟨1913502185215887489134383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2551336246954516652179177 1913502185215887489134383)
      ·
        refine ⟨2870253277823831233701575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913502185215887489134383 2870253277823831233701575)
        ·
          refine ⟨4305379916735746850552363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870253277823831233701575 4305379916735746850552363)
          ·
            refine ⟨6458069875103620275828545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305379916735746850552363 6458069875103620275828545)
            ·
              refine ⟨4843552406327715206871409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6458069875103620275828545 4843552406327715206871409)
              ·
                refine ⟨3632664304745786405153557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4843552406327715206871409 3632664304745786405153557)
                ·
                  refine ⟨170281139284958737741573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3632664304745786405153557 170281139284958737741573)
                  ·
                    rfl

theorem cell20_373074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_373074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373074 prefixEnd_373074 := by exact prefixLift 373074
  have htrace : WordTrace (prefixWord ++ tailWord_373074) baseStart_373074 baseEnd_373074 := by
    simpa [prefixWord, tailWord_373074, baseEnd_373074] using wordTrace_append hprefix tailTrace_373074
  have hstable : (prefixWord ++ tailWord_373074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373074).length < 2 ^ (prefixWord ++ tailWord_373074).sum := by decide
  have hdescent : baseEnd_373074 < baseStart_373074 := by decide
  rcases family_descends (prefixWord ++ tailWord_373074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373077 : List Nat := [1, 3, 2, 2, 5, 1, 6]
def baseStart_373077 : Nat := 118140960795 + 373077 * 2 ^ 59
def prefixEnd_373077 : Nat := 4983230072969 + 3 ^ 40 * 373077 * 2
def baseEnd_373077 : Nat := 18920278729633784515729

theorem tailTrace_373077 : CollatzResearch.WordTrace tailWord_373077 prefixEnd_373077 18920278729633784515729 := by
  unfold tailWord_373077
  simp only [CollatzResearch.WordTrace]
  refine ⟨13607236069413220323981485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9071490712942146882654323 13607236069413220323981485)
  ·
    refine ⟨5102713526029957621493057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13607236069413220323981485 5102713526029957621493057)
    ·
      refine ⟨3827035144522468216119793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5102713526029957621493057 3827035144522468216119793)
      ·
        refine ⟨2870276358391851162089845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3827035144522468216119793 2870276358391851162089845)
        ·
          refine ⟨269088408599236046445923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2870276358391851162089845 269088408599236046445923)
          ·
            refine ⟨403632612898854069668885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269088408599236046445923 403632612898854069668885)
            ·
              refine ⟨18920278729633784515729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403632612898854069668885 18920278729633784515729)
              ·
                rfl

theorem cell20_373077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 6].length) (baseStart_373077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373077 prefixEnd_373077 := by exact prefixLift 373077
  have htrace : WordTrace (prefixWord ++ tailWord_373077) baseStart_373077 baseEnd_373077 := by
    simpa [prefixWord, tailWord_373077, baseEnd_373077] using wordTrace_append hprefix tailTrace_373077
  have hstable : (prefixWord ++ tailWord_373077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373077).length < 2 ^ (prefixWord ++ tailWord_373077).sum := by decide
  have hdescent : baseEnd_373077 < baseStart_373077 := by decide
  rcases family_descends (prefixWord ++ tailWord_373077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373098 : List Nat := [3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_373098 : Nat := 118140960795 + 373098 * 2 ^ 59
def prefixEnd_373098 : Nat := 4983230072969 + 3 ^ 40 * 373098 * 2
def baseEnd_373098 : Nat := 56764031179640440313825

theorem tailTrace_373098 : CollatzResearch.WordTrace tailWord_373098 prefixEnd_373098 56764031179640440313825 := by
  unfold tailWord_373098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402000500584285227623987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9072001334891427273663965 3402000500584285227623987)
  ·
    refine ⟨5103000750876427841435981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3402000500584285227623987 5103000750876427841435981)
    ·
      refine ⟨1913625281578660440538493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5103000750876427841435981 1913625281578660440538493)
      ·
        refine ⟨717609480591997665201935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1913625281578660440538493 717609480591997665201935)
        ·
          refine ⟨1076414220887996497802903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717609480591997665201935 1076414220887996497802903)
          ·
            refine ⟨1614621331331994746704355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076414220887996497802903 1614621331331994746704355)
            ·
              refine ⟨2421931996997992120056533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614621331331994746704355 2421931996997992120056533)
              ·
                refine ⟨56764031179640440313825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2421931996997992120056533 56764031179640440313825)
                ·
                  rfl

theorem cell20_373098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_373098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373098 prefixEnd_373098 := by exact prefixLift 373098
  have htrace : WordTrace (prefixWord ++ tailWord_373098) baseStart_373098 baseEnd_373098 := by
    simpa [prefixWord, tailWord_373098, baseEnd_373098] using wordTrace_append hprefix tailTrace_373098
  have hstable : (prefixWord ++ tailWord_373098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373098).length < 2 ^ (prefixWord ++ tailWord_373098).sum := by decide
  have hdescent : baseEnd_373098 < baseStart_373098 := by decide
  rcases family_descends (prefixWord ++ tailWord_373098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373143 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_373143 : Nat := 118140960795 + 373143 * 2 ^ 59
def prefixEnd_373143 : Nat := 4983230072969 + 3 ^ 40 * 373143 * 2
def baseEnd_373143 : Nat := 170312632765101164441291

theorem tailTrace_373143 : CollatzResearch.WordTrace tailWord_373143 prefixEnd_373143 170312632765101164441291 := by
  unfold tailWord_373143
  simp only [CollatzResearch.WordTrace]
  refine ⟨13609643287174113595884083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9073095524782742397256055 13609643287174113595884083)
  ·
    refine ⟨20414464930761170393826125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13609643287174113595884083 20414464930761170393826125)
    ·
      refine ⟨7655424349035438897684797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20414464930761170393826125 7655424349035438897684797)
      ·
        refine ⟨2870784130888289586631799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7655424349035438897684797 2870784130888289586631799)
        ·
          refine ⟨4306176196332434379947699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870784130888289586631799 4306176196332434379947699)
          ·
            refine ⟨6459264294498651569921549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306176196332434379947699 6459264294498651569921549)
            ·
              refine ⟨2422224110436994338720581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6459264294498651569921549 2422224110436994338720581)
              ·
                refine ⟨454167020706936438510109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2422224110436994338720581 454167020706936438510109)
                ·
                  refine ⟨170312632765101164441291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454167020706936438510109 170312632765101164441291)
                  ·
                    rfl

theorem cell20_373143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_373143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373143 prefixEnd_373143 := by exact prefixLift 373143
  have htrace : WordTrace (prefixWord ++ tailWord_373143) baseStart_373143 baseEnd_373143 := by
    simpa [prefixWord, tailWord_373143, baseEnd_373143] using wordTrace_append hprefix tailTrace_373143
  have hstable : (prefixWord ++ tailWord_373143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373143).length < 2 ^ (prefixWord ++ tailWord_373143).sum := by decide
  have hdescent : baseEnd_373143 < baseStart_373143 := by decide
  rcases family_descends (prefixWord ++ tailWord_373143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373146 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_373146 : Nat := 118140960795 + 373146 * 2 ^ 59
def prefixEnd_373146 : Nat := 4983230072969 + 3 ^ 40 * 373146 * 2
def baseEnd_373146 : Nat := 170314002046846487341279

theorem tailTrace_373146 : CollatzResearch.WordTrace tailWord_373146 prefixEnd_373146 170314002046846487341279 := by
  unfold tailWord_373146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402438176540811277060823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9073168470775496738828861 3402438176540811277060823)
  ·
    refine ⟨5103657264811216915591235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3402438176540811277060823 5103657264811216915591235)
    ·
      refine ⟨7655485897216825373386853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103657264811216915591235 7655485897216825373386853)
      ·
        refine ⟨1435403605728154757510035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7655485897216825373386853 1435403605728154757510035)
        ·
          refine ⟨2153105408592232136265053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435403605728154757510035 2153105408592232136265053)
          ·
            refine ⟨807414528222087051099395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2153105408592232136265053 807414528222087051099395)
            ·
              refine ⟨1211121792333130576649093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807414528222087051099395 1211121792333130576649093)
              ·
                refine ⟨227085336062461983121705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1211121792333130576649093 227085336062461983121705)
                ·
                  refine ⟨170314002046846487341279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227085336062461983121705 170314002046846487341279)
                  ·
                    rfl

theorem cell20_373146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_373146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373146 prefixEnd_373146 := by exact prefixLift 373146
  have htrace : WordTrace (prefixWord ++ tailWord_373146) baseStart_373146 baseEnd_373146 := by
    simpa [prefixWord, tailWord_373146, baseEnd_373146] using wordTrace_append hprefix tailTrace_373146
  have hstable : (prefixWord ++ tailWord_373146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373146).length < 2 ^ (prefixWord ++ tailWord_373146).sum := by decide
  have hdescent : baseEnd_373146 < baseStart_373146 := by decide
  rcases family_descends (prefixWord ++ tailWord_373146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373164 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_373164 : Nat := 118140960795 + 373164 * 2 ^ 59
def prefixEnd_373164 : Nat := 4983230072969 + 3 ^ 40 * 373164 * 2
def baseEnd_373164 : Nat := 170322217737318424741205

theorem tailTrace_373164 : CollatzResearch.WordTrace tailWord_373164 prefixEnd_373164 170322217737318424741205 := by
  unfold tailWord_373164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805204610049017091199273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9073606146732022788265697 6805204610049017091199273)
  ·
    refine ⟨5103903457536762818399455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6805204610049017091199273 5103903457536762818399455)
    ·
      refine ⟨7655855186305144227599183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103903457536762818399455 7655855186305144227599183)
      ·
        refine ⟨11483782779457716341398775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7655855186305144227599183 11483782779457716341398775)
        ·
          refine ⟨17225674169186574512098163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11483782779457716341398775 17225674169186574512098163)
          ·
            refine ⟨25838511253779861768147245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17225674169186574512098163 25838511253779861768147245)
            ·
              refine ⟨9689441720167448163055217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25838511253779861768147245 9689441720167448163055217)
              ·
                refine ⟨7267081290125586122291413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9689441720167448163055217 7267081290125586122291413)
                ·
                  refine ⟨170322217737318424741205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7267081290125586122291413 170322217737318424741205)
                  ·
                    rfl

theorem cell20_373164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_373164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373164 prefixEnd_373164 := by exact prefixLift 373164
  have htrace : WordTrace (prefixWord ++ tailWord_373164) baseStart_373164 baseEnd_373164 := by
    simpa [prefixWord, tailWord_373164, baseEnd_373164] using wordTrace_append hprefix tailTrace_373164
  have hstable : (prefixWord ++ tailWord_373164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373164).length < 2 ^ (prefixWord ++ tailWord_373164).sum := by decide
  have hdescent : baseEnd_373164 < baseStart_373164 := by decide
  rcases family_descends (prefixWord ++ tailWord_373164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373205 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_373205 : Nat := 118140960795 + 373205 * 2 ^ 59
def prefixEnd_373205 : Nat := 4983230072969 + 3 ^ 40 * 373205 * 2
def baseEnd_373205 : Nat := 170340931254504504374371

theorem tailTrace_373205 : CollatzResearch.WordTrace tailWord_373205 prefixEnd_373205 170340931254504504374371 := by
  unfold tailWord_373205
  simp only [CollatzResearch.WordTrace]
  refine ⟨13611904612949498184641069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9074603075299665456427379 13611904612949498184641069)
  ·
    refine ⟨5104464229856061819240401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13611904612949498184641069 5104464229856061819240401)
    ·
      refine ⟨3828348172392046364430301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5104464229856061819240401 3828348172392046364430301)
      ·
        refine ⟨1435630564647017386661363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3828348172392046364430301 1435630564647017386661363)
        ·
          refine ⟨2153445846970526079992045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435630564647017386661363 2153445846970526079992045)
          ·
            refine ⟨807542192613947279997017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2153445846970526079992045 807542192613947279997017)
            ·
              refine ⟨605656644460460459997763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807542192613947279997017 605656644460460459997763)
              ·
                refine ⟨908484966690690689996645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605656644460460459997763 908484966690690689996645)
                ·
                  refine ⟨170340931254504504374371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908484966690690689996645 170340931254504504374371)
                  ·
                    rfl

theorem cell20_373205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_373205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373205 prefixEnd_373205 := by exact prefixLift 373205
  have htrace : WordTrace (prefixWord ++ tailWord_373205) baseStart_373205 baseEnd_373205 := by
    simpa [prefixWord, tailWord_373205, baseEnd_373205] using wordTrace_append hprefix tailTrace_373205
  have hstable : (prefixWord ++ tailWord_373205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373205).length < 2 ^ (prefixWord ++ tailWord_373205).sum := by decide
  have hdescent : baseEnd_373205 < baseStart_373205 := by decide
  rcases family_descends (prefixWord ++ tailWord_373205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373229 : List Nat := [1, 5, 1, 3, 1, 1, 4, 4]
def baseStart_373229 : Nat := 118140960795 + 373229 * 2 ^ 59
def prefixEnd_373229 : Nat := 4983230072969 + 3 ^ 40 * 373229 * 2
def baseEnd_373229 : Nat := 56783961836155695858091

theorem tailTrace_373229 : CollatzResearch.WordTrace tailWord_373229 prefixEnd_373229 56783961836155695858091 := by
  unfold tailWord_373229
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612779964862550283514741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9075186643241700189009827 13612779964862550283514741)
  ·
    refine ⟨1276198121705864089079507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13612779964862550283514741 1276198121705864089079507)
    ·
      refine ⟨1914297182558796133619261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276198121705864089079507 1914297182558796133619261)
      ·
        refine ⟨717861443459548550107223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1914297182558796133619261 717861443459548550107223)
        ·
          refine ⟨1076792165189322825160835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717861443459548550107223 1076792165189322825160835)
          ·
            refine ⟨1615188247783984237741253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076792165189322825160835 1615188247783984237741253)
            ·
              refine ⟨302847796459497044576485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1615188247783984237741253 302847796459497044576485)
              ·
                refine ⟨56783961836155695858091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302847796459497044576485 56783961836155695858091)
                ·
                  rfl

theorem cell20_373229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_373229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373229 prefixEnd_373229 := by exact prefixLift 373229
  have htrace : WordTrace (prefixWord ++ tailWord_373229) baseStart_373229 baseEnd_373229 := by
    simpa [prefixWord, tailWord_373229, baseEnd_373229] using wordTrace_append hprefix tailTrace_373229
  have hstable : (prefixWord ++ tailWord_373229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373229).length < 2 ^ (prefixWord ++ tailWord_373229).sum := by decide
  have hdescent : baseEnd_373229 < baseStart_373229 := by decide
  rcases family_descends (prefixWord ++ tailWord_373229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373233 : List Nat := [1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_373233 : Nat := 118140960795 + 373233 * 2 ^ 59
def prefixEnd_373233 : Nat := 4983230072969 + 3 ^ 40 * 373233 * 2
def baseEnd_373233 : Nat := 56784570405820283813641

theorem tailTrace_373233 : CollatzResearch.WordTrace tailWord_373233 prefixEnd_373233 56784570405820283813641 := by
  unfold tailWord_373233
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612925856848058966660353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9075283904565372644440235 13612925856848058966660353)
  ·
    refine ⟨10209694392636044224995265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13612925856848058966660353 10209694392636044224995265)
    ·
      refine ⟨7657270794477033168746449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10209694392636044224995265 7657270794477033168746449)
      ·
        refine ⟨5742953095857774876559837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7657270794477033168746449 5742953095857774876559837)
        ·
          refine ⟨2153607410946665578709939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5742953095857774876559837 2153607410946665578709939)
          ·
            refine ⟨3230411116419998368064909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153607410946665578709939 3230411116419998368064909)
            ·
              refine ⟨1211404168657499388024341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3230411116419998368064909 1211404168657499388024341)
              ·
                refine ⟨56784570405820283813641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1211404168657499388024341 56784570405820283813641)
                ·
                  rfl

theorem cell20_373233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_373233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373233 prefixEnd_373233 := by exact prefixLift 373233
  have htrace : WordTrace (prefixWord ++ tailWord_373233) baseStart_373233 baseEnd_373233 := by
    simpa [prefixWord, tailWord_373233, baseEnd_373233] using wordTrace_append hprefix tailTrace_373233
  have hstable : (prefixWord ++ tailWord_373233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373233).length < 2 ^ (prefixWord ++ tailWord_373233).sum := by decide
  have hdescent : baseEnd_373233 < baseStart_373233 := by decide
  rcases family_descends (prefixWord ++ tailWord_373233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373240 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_373240 : Nat := 118140960795 + 373240 * 2 ^ 59
def prefixEnd_373240 : Nat := 4983230072969 + 3 ^ 40 * 373240 * 2
def baseEnd_373240 : Nat := 170356906208199938207561

theorem tailTrace_373240 : CollatzResearch.WordTrace tailWord_373240 prefixEnd_373240 170356906208199938207561 := by
  unfold tailWord_373240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806590583911349581082587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9075454111881799441443449 6806590583911349581082587)
  ·
    refine ⟨10209885875867024371623881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806590583911349581082587 10209885875867024371623881)
    ·
      refine ⟨7657414406900268278717911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10209885875867024371623881 7657414406900268278717911)
      ·
        refine ⟨11486121610350402418076867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657414406900268278717911 11486121610350402418076867)
        ·
          refine ⟨17229182415525603627115301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11486121610350402418076867 17229182415525603627115301)
          ·
            refine ⟨3230471702911050680084119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17229182415525603627115301 3230471702911050680084119)
            ·
              refine ⟨4845707554366576020126179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230471702911050680084119 4845707554366576020126179)
              ·
                refine ⟨7268561331549864030189269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845707554366576020126179 7268561331549864030189269)
                ·
                  refine ⟨170356906208199938207561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7268561331549864030189269 170356906208199938207561)
                  ·
                    rfl

theorem cell20_373240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_373240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373240 prefixEnd_373240 := by exact prefixLift 373240
  have htrace : WordTrace (prefixWord ++ tailWord_373240) baseStart_373240 baseEnd_373240 := by
    simpa [prefixWord, tailWord_373240, baseEnd_373240] using wordTrace_append hprefix tailTrace_373240
  have hstable : (prefixWord ++ tailWord_373240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373240).length < 2 ^ (prefixWord ++ tailWord_373240).sum := by decide
  have hdescent : baseEnd_373240 < baseStart_373240 := by decide
  rcases family_descends (prefixWord ++ tailWord_373240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373274 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_373274 : Nat := 118140960795 + 373274 * 2 ^ 59
def prefixEnd_373274 : Nat := 4983230072969 + 3 ^ 40 * 373274 * 2
def baseEnd_373274 : Nat := 170372424734646931074089

theorem tailTrace_373274 : CollatzResearch.WordTrace tailWord_373274 prefixEnd_373274 170372424734646931074089 := by
  unfold tailWord_373274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403605312424880742225719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9076280833133015312601917 3403605312424880742225719)
  ·
    refine ⟨5105407968637321113338579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3403605312424880742225719 5105407968637321113338579)
    ·
      refine ⟨7658111952955981670007869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105407968637321113338579 7658111952955981670007869)
      ·
        refine ⟨2871791982358493126252951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7658111952955981670007869 2871791982358493126252951)
        ·
          refine ⟨4307687973537739689379427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871791982358493126252951 4307687973537739689379427)
          ·
            refine ⟨6461531960306609534069141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307687973537739689379427 6461531960306609534069141)
            ·
              refine ⟨302884310639372321909491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6461531960306609534069141 302884310639372321909491)
              ·
                refine ⟨454326465959058482864237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302884310639372321909491 454326465959058482864237)
                ·
                  refine ⟨170372424734646931074089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454326465959058482864237 170372424734646931074089)
                  ·
                    rfl

theorem cell20_373274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_373274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373274 prefixEnd_373274 := by exact prefixLift 373274
  have htrace : WordTrace (prefixWord ++ tailWord_373274) baseStart_373274 baseEnd_373274 := by
    simpa [prefixWord, tailWord_373274, baseEnd_373274] using wordTrace_append hprefix tailTrace_373274
  have hstable : (prefixWord ++ tailWord_373274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373274).length < 2 ^ (prefixWord ++ tailWord_373274).sum := by decide
  have hdescent : baseEnd_373274 < baseStart_373274 := by decide
  rcases family_descends (prefixWord ++ tailWord_373274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373288 : List Nat := [2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_373288 : Nat := 118140960795 + 373288 * 2 ^ 59
def prefixEnd_373288 : Nat := 4983230072969 + 3 ^ 40 * 373288 * 2
def baseEnd_373288 : Nat := 56792938238708368202455

theorem tailTrace_373288 : CollatzResearch.WordTrace tailWord_373288 prefixEnd_373288 56792938238708368202455 := by
  unfold tailWord_373288
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807465935824401679956259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9076621247765868906608345 6807465935824401679956259)
  ·
    refine ⟨10211198903736602519934389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6807465935824401679956259 10211198903736602519934389)
    ·
      refine ⟨957299897225306486243849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10211198903736602519934389 957299897225306486243849)
      ·
        refine ⟨717974922918979864682887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 957299897225306486243849 717974922918979864682887)
        ·
          refine ⟨1076962384378469797024331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717974922918979864682887 1076962384378469797024331)
          ·
            refine ⟨1615443576567704695536497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076962384378469797024331 1615443576567704695536497)
            ·
              refine ⟨1211582682425778521652373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615443576567704695536497 1211582682425778521652373)
              ·
                refine ⟨56792938238708368202455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1211582682425778521652373 56792938238708368202455)
                ·
                  rfl

theorem cell20_373288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_373288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373288 prefixEnd_373288 := by exact prefixLift 373288
  have htrace : WordTrace (prefixWord ++ tailWord_373288) baseStart_373288 baseEnd_373288 := by
    simpa [prefixWord, tailWord_373288, baseEnd_373288] using wordTrace_append hprefix tailTrace_373288
  have hstable : (prefixWord ++ tailWord_373288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373288).length < 2 ^ (prefixWord ++ tailWord_373288).sum := by decide
  have hdescent : baseEnd_373288 < baseStart_373288 := by decide
  rcases family_descends (prefixWord ++ tailWord_373288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373309 : List Nat := [1, 4, 1, 3, 2, 9]
def baseStart_373309 : Nat := 118140960795 + 373309 * 2 ^ 59
def prefixEnd_373309 : Nat := 4983230072969 + 3 ^ 40 * 373309 * 2
def baseEnd_373309 : Nat := 6310681469938606107677

theorem tailTrace_373309 : CollatzResearch.WordTrace tailWord_373309 prefixEnd_373309 6310681469938606107677 := by
  unfold tailWord_373309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13615697804572723946426981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9077131869715149297617987 13615697804572723946426981)
  ·
    refine ⟨2552943338357385739955059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13615697804572723946426981 2552943338357385739955059)
    ·
      refine ⟨3829415007536078609932589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2552943338357385739955059 3829415007536078609932589)
      ·
        refine ⟨1436030627826029478724721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3829415007536078609932589 1436030627826029478724721)
        ·
          refine ⟨1077022970869522109043541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436030627826029478724721 1077022970869522109043541)
          ·
            refine ⟨6310681469938606107677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1077022970869522109043541 6310681469938606107677)
            ·
              rfl

theorem cell20_373309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 9].length) (baseStart_373309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373309 prefixEnd_373309 := by exact prefixLift 373309
  have htrace : WordTrace (prefixWord ++ tailWord_373309) baseStart_373309 baseEnd_373309 := by
    simpa [prefixWord, tailWord_373309, baseEnd_373309] using wordTrace_append hprefix tailTrace_373309
  have hstable : (prefixWord ++ tailWord_373309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373309).length < 2 ^ (prefixWord ++ tailWord_373309).sum := by decide
  have hdescent : baseEnd_373309 < baseStart_373309 := by decide
  rcases family_descends (prefixWord ++ tailWord_373309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373333 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_373333 : Nat := 118140960795 + 373333 * 2 ^ 59
def prefixEnd_373333 : Nat := 4983230072969 + 3 ^ 40 * 373333 * 2
def baseEnd_373333 : Nat := 170399353942304948107181

theorem tailTrace_373333 : CollatzResearch.WordTrace tailWord_373333 prefixEnd_373333 170399353942304948107181 := by
  unfold tailWord_373333
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616573156485776045300653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9077715437657184030200435 13616573156485776045300653)
  ·
    refine ⟨5106214933682166016987745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13616573156485776045300653 5106214933682166016987745)
    ·
      refine ⟨3829661200261624512740809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5106214933682166016987745 3829661200261624512740809)
      ·
        refine ⟨2872245900196218384555607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3829661200261624512740809 2872245900196218384555607)
        ·
          refine ⟨4308368850294327576833411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872245900196218384555607 4308368850294327576833411)
          ·
            refine ⟨6462553275441491365250117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308368850294327576833411 6462553275441491365250117)
            ·
              refine ⟨1211728739145279630984397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6462553275441491365250117 1211728739145279630984397)
              ·
                refine ⟨454398277179479861619149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1211728739145279630984397 454398277179479861619149)
                ·
                  refine ⟨170399353942304948107181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454398277179479861619149 170399353942304948107181)
                  ·
                    rfl

theorem cell20_373333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_373333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373333 prefixEnd_373333 := by exact prefixLift 373333
  have htrace : WordTrace (prefixWord ++ tailWord_373333) baseStart_373333 baseEnd_373333 := by
    simpa [prefixWord, tailWord_373333, baseEnd_373333] using wordTrace_append hprefix tailTrace_373333
  have hstable : (prefixWord ++ tailWord_373333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373333).length < 2 ^ (prefixWord ++ tailWord_373333).sum := by decide
  have hdescent : baseEnd_373333 < baseStart_373333 := by decide
  rcases family_descends (prefixWord ++ tailWord_373333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373423 : List Nat := [1, 1, 2, 1, 2, 7, 6]
def baseStart_373423 : Nat := 118140960795 + 373423 * 2 ^ 59
def prefixEnd_373423 : Nat := 4983230072969 + 3 ^ 40 * 373423 * 2
def baseEnd_373423 : Nat := 18937825821629403900757

theorem tailTrace_373423 : CollatzResearch.WordTrace tailWord_373423 prefixEnd_373423 18937825821629403900757 := by
  unfold tailWord_373423
  simp only [CollatzResearch.WordTrace]
  refine ⟨13619855726159721416076923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9079903817439814277384615 13619855726159721416076923)
  ·
    refine ⟨20429783589239582124115385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13619855726159721416076923 20429783589239582124115385)
    ·
      refine ⟨15322337691929686593086539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20429783589239582124115385 15322337691929686593086539)
      ·
        refine ⟨22983506537894529889629809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15322337691929686593086539 22983506537894529889629809)
        ·
          refine ⟨17237629903420897417222357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22983506537894529889629809 17237629903420897417222357)
          ·
            refine ⟨404006950861427283216149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17237629903420897417222357 404006950861427283216149)
            ·
              refine ⟨18937825821629403900757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 404006950861427283216149 18937825821629403900757)
              ·
                rfl

theorem cell20_373423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_373423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373423 prefixEnd_373423 := by exact prefixLift 373423
  have htrace : WordTrace (prefixWord ++ tailWord_373423) baseStart_373423 baseEnd_373423 := by
    simpa [prefixWord, tailWord_373423, baseEnd_373423] using wordTrace_append hprefix tailTrace_373423
  have hstable : (prefixWord ++ tailWord_373423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373423).length < 2 ^ (prefixWord ++ tailWord_373423).sum := by decide
  have hdescent : baseEnd_373423 < baseStart_373423 := by decide
  rcases family_descends (prefixWord ++ tailWord_373423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373429 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 2]
def baseStart_373429 : Nat := 118140960795 + 373429 * 2 ^ 59
def prefixEnd_373429 : Nat := 4983230072969 + 3 ^ 40 * 373429 * 2
def baseEnd_373429 : Nat := 170443170958155280906789

theorem tailTrace_373429 : CollatzResearch.WordTrace tailWord_373429 prefixEnd_373429 170443170958155280906789 := by
  unfold tailWord_373429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13620074564137984440795341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9080049709425322960530227 13620074564137984440795341)
  ·
    refine ⟨5107527961551744165298253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13620074564137984440795341 5107527961551744165298253)
    ·
      refine ⟨1915322985581904061986845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5107527961551744165298253 1915322985581904061986845)
      ·
        refine ⟨718246119593214023245067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1915322985581904061986845 718246119593214023245067)
        ·
          refine ⟨1077369179389821034867601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718246119593214023245067 1077369179389821034867601)
          ·
            refine ⟨808026884542365776150701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077369179389821034867601 808026884542365776150701)
            ·
              refine ⟨303010081703387166056513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 808026884542365776150701 303010081703387166056513)
              ·
                refine ⟨227257561277540374542385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303010081703387166056513 227257561277540374542385)
                ·
                  refine ⟨170443170958155280906789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227257561277540374542385 170443170958155280906789)
                  ·
                    rfl

theorem cell20_373429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_373429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373429 prefixEnd_373429 := by exact prefixLift 373429
  have htrace : WordTrace (prefixWord ++ tailWord_373429) baseStart_373429 baseEnd_373429 := by
    simpa [prefixWord, tailWord_373429, baseEnd_373429] using wordTrace_append hprefix tailTrace_373429
  have hstable : (prefixWord ++ tailWord_373429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373429).length < 2 ^ (prefixWord ++ tailWord_373429).sum := by decide
  have hdescent : baseEnd_373429 < baseStart_373429 := by decide
  rcases family_descends (prefixWord ++ tailWord_373429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373502 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_373502 : Nat := 118140960795 + 373502 * 2 ^ 59
def prefixEnd_373502 : Nat := 4983230072969 + 3 ^ 40 * 373502 * 2
def baseEnd_373502 : Nat := 170476490147291471473157

theorem tailTrace_373502 : CollatzResearch.WordTrace tailWord_373502 prefixEnd_373502 170476490147291471473157 := by
  unfold tailWord_373502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702842136609189738525345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9081824728582345272135173 1702842136609189738525345)
  ·
    refine ⟨1277131602456892303894009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1702842136609189738525345 1277131602456892303894009)
    ·
      refine ⟨957848701842669227920507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1277131602456892303894009 957848701842669227920507)
      ·
        refine ⟨1436773052764003841880761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957848701842669227920507 1436773052764003841880761)
        ·
          refine ⟨1077579789573002881410571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436773052764003841880761 1077579789573002881410571)
          ·
            refine ⟨1616369684359504322115857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077579789573002881410571 1616369684359504322115857)
            ·
              refine ⟨1212277263269628241586893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616369684359504322115857 1212277263269628241586893)
              ·
                refine ⟨454603973726110590595085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1212277263269628241586893 454603973726110590595085)
                ·
                  refine ⟨170476490147291471473157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454603973726110590595085 170476490147291471473157)
                  ·
                    rfl

theorem cell20_373502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_373502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373502 prefixEnd_373502 := by exact prefixLift 373502
  have htrace : WordTrace (prefixWord ++ tailWord_373502) baseStart_373502 baseEnd_373502 := by
    simpa [prefixWord, tailWord_373502, baseEnd_373502] using wordTrace_append hprefix tailTrace_373502
  have hstable : (prefixWord ++ tailWord_373502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373502).length < 2 ^ (prefixWord ++ tailWord_373502).sum := by decide
  have hdescent : baseEnd_373502 < baseStart_373502 := by decide
  rcases family_descends (prefixWord ++ tailWord_373502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373513 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_373513 : Nat := 118140960795 + 373513 * 2 ^ 59
def prefixEnd_373513 : Nat := 4983230072969 + 3 ^ 40 * 373513 * 2
def baseEnd_373513 : Nat := 170481510847024322106445

theorem tailTrace_373513 : CollatzResearch.WordTrace tailWord_373513 prefixEnd_373513 170481510847024322106445 := by
  unfold tailWord_373513
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623138295833666786853193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9082092197222444524568795 13623138295833666786853193)
  ·
    refine ⟨10217353721875250090139895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13623138295833666786853193 10217353721875250090139895)
    ·
      refine ⟨15326030582812875135209843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10217353721875250090139895 15326030582812875135209843)
      ·
        refine ⟨22989045874219312702814765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15326030582812875135209843 22989045874219312702814765)
        ·
          refine ⟨8620892202832242263555537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22989045874219312702814765 8620892202832242263555537)
          ·
            refine ⟨6465669152124181697666653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8620892202832242263555537 6465669152124181697666653)
            ·
              refine ⟨2424625932046568136624995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6465669152124181697666653 2424625932046568136624995)
              ·
                refine ⟨3636938898069852204937493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424625932046568136624995 3636938898069852204937493)
                ·
                  refine ⟨170481510847024322106445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3636938898069852204937493 170481510847024322106445)
                  ·
                    rfl

theorem cell20_373513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_373513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373513 prefixEnd_373513 := by exact prefixLift 373513
  have htrace : WordTrace (prefixWord ++ tailWord_373513) baseStart_373513 baseEnd_373513 := by
    simpa [prefixWord, tailWord_373513, baseEnd_373513] using wordTrace_append hprefix tailTrace_373513
  have hstable : (prefixWord ++ tailWord_373513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373513).length < 2 ^ (prefixWord ++ tailWord_373513).sum := by decide
  have hdescent : baseEnd_373513 < baseStart_373513 := by decide
  rcases family_descends (prefixWord ++ tailWord_373513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373602 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_373602 : Nat := 118140960795 + 373602 * 2 ^ 59
def prefixEnd_373602 : Nat := 4983230072969 + 3 ^ 40 * 373602 * 2
def baseEnd_373602 : Nat := 170522132872135568139415

theorem tailTrace_373602 : CollatzResearch.WordTrace tailWord_373602 prefixEnd_373602 170522132872135568139415 := by
  unfold tailWord_373602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406596098127808746710765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9084256261674156657895373 3406596098127808746710765)
  ·
    refine ⟨1277473536797928280016537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3406596098127808746710765 1277473536797928280016537)
    ·
      refine ⟨958105152598446210012403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1277473536797928280016537 958105152598446210012403)
      ·
        refine ⟨1437157728897669315018605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958105152598446210012403 1437157728897669315018605)
        ·
          refine ⟨538934148336625993131977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1437157728897669315018605 538934148336625993131977)
          ·
            refine ⟨404200611252469494848983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538934148336625993131977 404200611252469494848983)
            ·
              refine ⟨606300916878704242273475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404200611252469494848983 606300916878704242273475)
              ·
                refine ⟨909451375318056363410213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606300916878704242273475 909451375318056363410213)
                ·
                  refine ⟨170522132872135568139415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909451375318056363410213 170522132872135568139415)
                  ·
                    rfl

theorem cell20_373602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_373602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373602 prefixEnd_373602 := by exact prefixLift 373602
  have htrace : WordTrace (prefixWord ++ tailWord_373602) baseStart_373602 baseEnd_373602 := by
    simpa [prefixWord, tailWord_373602, baseEnd_373602] using wordTrace_append hprefix tailTrace_373602
  have hstable : (prefixWord ++ tailWord_373602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373602).length < 2 ^ (prefixWord ++ tailWord_373602).sum := by decide
  have hdescent : baseEnd_373602 < baseStart_373602 := by decide
  rcases family_descends (prefixWord ++ tailWord_373602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373627 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_373627 : Nat := 118140960795 + 373627 * 2 ^ 59
def prefixEnd_373627 : Nat := 4983230072969 + 3 ^ 40 * 373627 * 2
def baseEnd_373627 : Nat := 170533543553346592305979

theorem tailTrace_373627 : CollatzResearch.WordTrace tailWord_373627 prefixEnd_373627 170533543553346592305979 := by
  unfold tailWord_373627
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627296217420664256503135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9084864144947109504335423 13627296217420664256503135)
  ·
    refine ⟨20440944326130996384754703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13627296217420664256503135 20440944326130996384754703)
    ·
      refine ⟨30661416489196494577132055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20440944326130996384754703 30661416489196494577132055)
      ·
        refine ⟨45992124733794741865698083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30661416489196494577132055 45992124733794741865698083)
        ·
          refine ⟨68988187100692112798547125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45992124733794741865698083 68988187100692112798547125)
          ·
            refine ⟨6467642540689885574863793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68988187100692112798547125 6467642540689885574863793)
            ·
              refine ⟨4850731905517414181147845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6467642540689885574863793 4850731905517414181147845)
              ·
                refine ⟨909512232284515158965221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4850731905517414181147845 909512232284515158965221)
                ·
                  refine ⟨170533543553346592305979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909512232284515158965221 170533543553346592305979)
                  ·
                    rfl

theorem cell20_373627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_373627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373627 prefixEnd_373627 := by exact prefixLift 373627
  have htrace : WordTrace (prefixWord ++ tailWord_373627) baseStart_373627 baseEnd_373627 := by
    simpa [prefixWord, tailWord_373627, baseEnd_373627] using wordTrace_append hprefix tailTrace_373627
  have hstable : (prefixWord ++ tailWord_373627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373627).length < 2 ^ (prefixWord ++ tailWord_373627).sum := by decide
  have hdescent : baseEnd_373627 < baseStart_373627 := by decide
  rcases family_descends (prefixWord ++ tailWord_373627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373661 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 2]
def baseStart_373661 : Nat := 118140960795 + 373661 * 2 ^ 59
def prefixEnd_373661 : Nat := 4983230072969 + 3 ^ 40 * 373661 * 2
def baseEnd_373661 : Nat := 170549062079793585172507

theorem tailTrace_373661 : CollatzResearch.WordTrace tailWord_373661 prefixEnd_373661 170549062079793585172507 := by
  unfold tailWord_373661
  simp only [CollatzResearch.WordTrace]
  refine ⟨13628536299297488063240837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9085690866198325375493891 13628536299297488063240837)
  ·
    refine ⟨2555350556118279011857657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13628536299297488063240837 2555350556118279011857657)
    ·
      refine ⟨1916512917088709258893243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2555350556118279011857657 1916512917088709258893243)
      ·
        refine ⟨2874769375633063888339865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916512917088709258893243 2874769375633063888339865)
        ·
          refine ⟨2156077031724797916254899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2874769375633063888339865 2156077031724797916254899)
          ·
            refine ⟨3234115547587196874382349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156077031724797916254899 3234115547587196874382349)
            ·
              refine ⟨1212793330345198827893381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3234115547587196874382349 1212793330345198827893381)
              ·
                refine ⟨227398749439724780230009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1212793330345198827893381 227398749439724780230009)
                ·
                  refine ⟨170549062079793585172507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227398749439724780230009 170549062079793585172507)
                  ·
                    rfl

theorem cell20_373661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_373661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373661 prefixEnd_373661 := by exact prefixLift 373661
  have htrace : WordTrace (prefixWord ++ tailWord_373661) baseStart_373661 baseEnd_373661 := by
    simpa [prefixWord, tailWord_373661, baseEnd_373661] using wordTrace_append hprefix tailTrace_373661
  have hstable : (prefixWord ++ tailWord_373661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373661).length < 2 ^ (prefixWord ++ tailWord_373661).sum := by decide
  have hdescent : baseEnd_373661 < baseStart_373661 := by decide
  rcases family_descends (prefixWord ++ tailWord_373661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373720 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_373720 : Nat := 118140960795 + 373720 * 2 ^ 59
def prefixEnd_373720 : Nat := 4983230072969 + 3 ^ 40 * 373720 * 2
def baseEnd_373720 : Nat := 170575991287451602205599

theorem tailTrace_373720 : CollatzResearch.WordTrace tailWord_373720 prefixEnd_373720 170575991287451602205599 := by
  unfold tailWord_373720
  simp only [CollatzResearch.WordTrace]
  refine ⟨6815344103041870569819307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9087125470722494093092409 6815344103041870569819307)
  ·
    refine ⟨10223016154562805854728961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6815344103041870569819307 10223016154562805854728961)
    ·
      refine ⟨7667262115922104391046721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10223016154562805854728961 7667262115922104391046721)
      ·
        refine ⟨5750446586941578293285041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7667262115922104391046721 5750446586941578293285041)
        ·
          refine ⟨4312834940206183719963781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750446586941578293285041 4312834940206183719963781)
          ·
            refine ⟨808656551288659447493209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4312834940206183719963781 808656551288659447493209)
            ·
              refine ⟨606492413466494585619907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808656551288659447493209 606492413466494585619907)
              ·
                refine ⟨909738620199741878429861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606492413466494585619907 909738620199741878429861)
                ·
                  refine ⟨170575991287451602205599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909738620199741878429861 170575991287451602205599)
                  ·
                    rfl

theorem cell20_373720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_373720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373720 prefixEnd_373720 := by exact prefixLift 373720
  have htrace : WordTrace (prefixWord ++ tailWord_373720) baseStart_373720 baseEnd_373720 := by
    simpa [prefixWord, tailWord_373720, baseEnd_373720] using wordTrace_append hprefix tailTrace_373720
  have hstable : (prefixWord ++ tailWord_373720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373720).length < 2 ^ (prefixWord ++ tailWord_373720).sum := by decide
  have hdescent : baseEnd_373720 < baseStart_373720 := by decide
  rcases family_descends (prefixWord ++ tailWord_373720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373772 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_373772 : Nat := 118140960795 + 373772 * 2 ^ 59
def prefixEnd_373772 : Nat := 4983230072969 + 3 ^ 40 * 373772 * 2
def baseEnd_373772 : Nat := 170599725504370532472053

theorem tailTrace_373772 : CollatzResearch.WordTrace tailWord_373772 prefixEnd_373772 170599725504370532472053 := by
  unfold tailWord_373772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816292400947677010265785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9088389867930236013687713 6816292400947677010265785)
  ·
    refine ⟨5112219300710757757699339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6816292400947677010265785 5112219300710757757699339)
    ·
      refine ⟨7668328951066136636549009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5112219300710757757699339 7668328951066136636549009)
      ·
        refine ⟨5751246713299602477411757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7668328951066136636549009 5751246713299602477411757)
        ·
          refine ⟨2156717517487350929029409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5751246713299602477411757 2156717517487350929029409)
          ·
            refine ⟨1617538138115513196772057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156717517487350929029409 1617538138115513196772057)
            ·
              refine ⟨1213153603586634897579043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617538138115513196772057 1213153603586634897579043)
              ·
                refine ⟨1819730405379952346368565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213153603586634897579043 1819730405379952346368565)
                ·
                  refine ⟨170599725504370532472053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1819730405379952346368565 170599725504370532472053)
                  ·
                    rfl

theorem cell20_373772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_373772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373772 prefixEnd_373772 := by exact prefixLift 373772
  have htrace : WordTrace (prefixWord ++ tailWord_373772) baseStart_373772 baseEnd_373772 := by
    simpa [prefixWord, tailWord_373772, baseEnd_373772] using wordTrace_append hprefix tailTrace_373772
  have hstable : (prefixWord ++ tailWord_373772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373772).length < 2 ^ (prefixWord ++ tailWord_373772).sum := by decide
  have hdescent : baseEnd_373772 < baseStart_373772 := by decide
  rcases family_descends (prefixWord ++ tailWord_373772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373778 : List Nat := [3, 2, 5, 1, 1, 1, 2, 5]
def baseStart_373778 : Nat := 118140960795 + 373778 * 2 ^ 59
def prefixEnd_373778 : Nat := 4983230072969 + 3 ^ 40 * 373778 * 2
def baseEnd_373778 : Nat := 56867488022620392757343

theorem tailTrace_373778 : CollatzResearch.WordTrace tailWord_373778 prefixEnd_373778 56867488022620392757343 := by
  unfold tailWord_373778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3408200909968404261312497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9088535759915744696833325 3408200909968404261312497)
  ·
    refine ⟨2556150682476303195984373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3408200909968404261312497 2556150682476303195984373)
    ·
      refine ⟨239639126482153424623535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2556150682476303195984373 239639126482153424623535)
      ·
        refine ⟨359458689723230136935303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239639126482153424623535 359458689723230136935303)
        ·
          refine ⟨539188034584845205402955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359458689723230136935303 539188034584845205402955)
          ·
            refine ⟨808782051877267808104433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539188034584845205402955 808782051877267808104433)
            ·
              refine ⟨606586538907950856078325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808782051877267808104433 606586538907950856078325)
              ·
                refine ⟨56867488022620392757343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 606586538907950856078325 56867488022620392757343)
                ·
                  rfl

theorem cell20_373778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_373778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373778 prefixEnd_373778 := by exact prefixLift 373778
  have htrace : WordTrace (prefixWord ++ tailWord_373778) baseStart_373778 baseEnd_373778 := by
    simpa [prefixWord, tailWord_373778, baseEnd_373778] using wordTrace_append hprefix tailTrace_373778
  have hstable : (prefixWord ++ tailWord_373778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373778).length < 2 ^ (prefixWord ++ tailWord_373778).sum := by decide
  have hdescent : baseEnd_373778 < baseStart_373778 := by decide
  rcases family_descends (prefixWord ++ tailWord_373778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373848 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_373848 : Nat := 118140960795 + 373848 * 2 ^ 59
def prefixEnd_373848 : Nat := 4983230072969 + 3 ^ 40 * 373848 * 2
def baseEnd_373848 : Nat := 170634413975252045938409

theorem tailTrace_373848 : CollatzResearch.WordTrace tailWord_373848 prefixEnd_373848 170634413975252045938409 := by
  unfold tailWord_373848
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817678374810009500149099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9090237833080012666865465 6817678374810009500149099)
  ·
    refine ⟨10226517562215014250223649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6817678374810009500149099 10226517562215014250223649)
    ·
      refine ⟨7669888171661260687667737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10226517562215014250223649 7669888171661260687667737)
      ·
        refine ⟨5752416128745945515750803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7669888171661260687667737 5752416128745945515750803)
        ·
          refine ⟨8628624193118918273626205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752416128745945515750803 8628624193118918273626205)
          ·
            refine ⟨3235734072419594352609827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8628624193118918273626205 3235734072419594352609827)
            ·
              refine ⟨4853601108629391528914741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235734072419594352609827 4853601108629391528914741)
              ·
                refine ⟨455025103934005455835757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4853601108629391528914741 455025103934005455835757)
                ·
                  refine ⟨170634413975252045938409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455025103934005455835757 170634413975252045938409)
                  ·
                    rfl

theorem cell20_373848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_373848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373848 prefixEnd_373848 := by exact prefixLift 373848
  have htrace : WordTrace (prefixWord ++ tailWord_373848) baseStart_373848 baseEnd_373848 := by
    simpa [prefixWord, tailWord_373848, baseEnd_373848] using wordTrace_append hprefix tailTrace_373848
  have hstable : (prefixWord ++ tailWord_373848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373848).length < 2 ^ (prefixWord ++ tailWord_373848).sum := by decide
  have hdescent : baseEnd_373848 < baseStart_373848 := by decide
  rcases family_descends (prefixWord ++ tailWord_373848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373854 : List Nat := [4, 4, 1, 1, 1, 2, 3, 4]
def baseStart_373854 : Nat := 118140960795 + 373854 * 2 ^ 59
def prefixEnd_373854 : Nat := 4983230072969 + 3 ^ 40 * 373854 * 2
def baseEnd_373854 : Nat := 56879050846247563912795

theorem tailTrace_373854 : CollatzResearch.WordTrace tailWord_373854 prefixEnd_373854 56879050846247563912795 := by
  unfold tailWord_373854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704446948449785253127077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9090383725065521350011077 1704446948449785253127077)
  ·
    refine ⟨319583802834334734961327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1704446948449785253127077 319583802834334734961327)
    ·
      refine ⟨479375704251502102441991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319583802834334734961327 479375704251502102441991)
      ·
        refine ⟨719063556377253153662987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479375704251502102441991 719063556377253153662987)
        ·
          refine ⟨1078595334565879730494481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719063556377253153662987 1078595334565879730494481)
          ·
            refine ⟨808946500924409797870861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078595334565879730494481 808946500924409797870861)
            ·
              refine ⟨303354937846653674201573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 808946500924409797870861 303354937846653674201573)
              ·
                refine ⟨56879050846247563912795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303354937846653674201573 56879050846247563912795)
                ·
                  rfl

theorem cell20_373854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_373854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373854 prefixEnd_373854 := by exact prefixLift 373854
  have htrace : WordTrace (prefixWord ++ tailWord_373854) baseStart_373854 baseEnd_373854 := by
    simpa [prefixWord, tailWord_373854, baseEnd_373854] using wordTrace_append hprefix tailTrace_373854
  have hstable : (prefixWord ++ tailWord_373854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373854).length < 2 ^ (prefixWord ++ tailWord_373854).sum := by decide
  have hdescent : baseEnd_373854 < baseStart_373854 := by decide
  rcases family_descends (prefixWord ++ tailWord_373854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373855 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_373855 : Nat := 118140960795 + 373855 * 2 ^ 59
def prefixEnd_373855 : Nat := 4983230072969 + 3 ^ 40 * 373855 * 2
def baseEnd_373855 : Nat := 170637608965991132705047

theorem tailTrace_373855 : CollatzResearch.WordTrace tailWord_373855 prefixEnd_373855 170637608965991132705047 := by
  unfold tailWord_373855
  simp only [CollatzResearch.WordTrace]
  refine ⟨13635612060594659195803019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9090408040396439463868679 13635612060594659195803019)
  ·
    refine ⟨20453418090891988793704529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13635612060594659195803019 20453418090891988793704529)
    ·
      refine ⟨15340063568168991595278397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20453418090891988793704529 15340063568168991595278397)
      ·
        refine ⟨5752523838063371848229399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15340063568168991595278397 5752523838063371848229399)
        ·
          refine ⟨8628785757095057772344099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752523838063371848229399 8628785757095057772344099)
          ·
            refine ⟨12943178635642586658516149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8628785757095057772344099 12943178635642586658516149)
            ·
              refine ⟨1213422997091492499235889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12943178635642586658516149 1213422997091492499235889)
              ·
                refine ⟨910067247818619374426917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213422997091492499235889 910067247818619374426917)
                ·
                  refine ⟨170637608965991132705047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910067247818619374426917 170637608965991132705047)
                  ·
                    rfl

theorem cell20_373855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_373855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373855 prefixEnd_373855 := by exact prefixLift 373855
  have htrace : WordTrace (prefixWord ++ tailWord_373855) baseStart_373855 baseEnd_373855 := by
    simpa [prefixWord, tailWord_373855, baseEnd_373855] using wordTrace_append hprefix tailTrace_373855
  have hstable : (prefixWord ++ tailWord_373855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373855).length < 2 ^ (prefixWord ++ tailWord_373855).sum := by decide
  have hdescent : baseEnd_373855 < baseStart_373855 := by decide
  rcases family_descends (prefixWord ++ tailWord_373855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373889 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 2]
def baseStart_373889 : Nat := 118140960795 + 373889 * 2 ^ 59
def prefixEnd_373889 : Nat := 4983230072969 + 3 ^ 40 * 373889 * 2
def baseEnd_373889 : Nat := 170653127492438125571575

theorem tailTrace_373889 : CollatzResearch.WordTrace tailWord_373889 prefixEnd_373889 170653127492438125571575 := by
  unfold tailWord_373889
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636852142471483002540721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9091234761647655335027147 13636852142471483002540721)
  ·
    refine ⟨10227639106853612251905541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13636852142471483002540721 10227639106853612251905541)
    ·
      refine ⟨1917682332535052297232289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10227639106853612251905541 1917682332535052297232289)
      ·
        refine ⟨1438261749401289222924217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1917682332535052297232289 1438261749401289222924217)
        ·
          refine ⟨1078696312050966917193163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1438261749401289222924217 1078696312050966917193163)
          ·
            refine ⟨1618044468076450375789745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078696312050966917193163 1618044468076450375789745)
            ·
              refine ⟨1213533351057337781842309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618044468076450375789745 1213533351057337781842309)
              ·
                refine ⟨227537503323250834095433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1213533351057337781842309 227537503323250834095433)
                ·
                  refine ⟨170653127492438125571575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227537503323250834095433 170653127492438125571575)
                  ·
                    rfl

theorem cell20_373889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_373889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373889 prefixEnd_373889 := by exact prefixLift 373889
  have htrace : WordTrace (prefixWord ++ tailWord_373889) baseStart_373889 baseEnd_373889 := by
    simpa [prefixWord, tailWord_373889, baseEnd_373889] using wordTrace_append hprefix tailTrace_373889
  have hstable : (prefixWord ++ tailWord_373889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373889).length < 2 ^ (prefixWord ++ tailWord_373889).sum := by decide
  have hdescent : baseEnd_373889 < baseStart_373889 := by decide
  rcases family_descends (prefixWord ++ tailWord_373889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373924 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_373924 : Nat := 118140960795 + 373924 * 2 ^ 59
def prefixEnd_373924 : Nat := 4983230072969 + 3 ^ 40 * 373924 * 2
def baseEnd_373924 : Nat := 170669102446133559404765

theorem tailTrace_373924 : CollatzResearch.WordTrace tailWord_373924 prefixEnd_373924 170669102446133559404765 := by
  unfold tailWord_373924
  simp only [CollatzResearch.WordTrace]
  refine ⟨6819064348672341990032413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9092085798229789320043217 6819064348672341990032413)
  ·
    refine ⟨2557149130752128246262155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6819064348672341990032413 2557149130752128246262155)
    ·
      refine ⟨3835723696128192369393233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557149130752128246262155 3835723696128192369393233)
      ·
        refine ⟨2876792772096144277044925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3835723696128192369393233 2876792772096144277044925)
        ·
          refine ⟨1078797289536054103891847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2876792772096144277044925 1078797289536054103891847)
          ·
            refine ⟨1618195934304081155837771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078797289536054103891847 1618195934304081155837771)
            ·
              refine ⟨2427293901456121733756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618195934304081155837771 2427293901456121733756657)
              ·
                refine ⟨1820470426092091300317493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427293901456121733756657 1820470426092091300317493)
                ·
                  refine ⟨170669102446133559404765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1820470426092091300317493 170669102446133559404765)
                  ·
                    rfl

theorem cell20_373924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_373924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373924 prefixEnd_373924 := by exact prefixLift 373924
  have htrace : WordTrace (prefixWord ++ tailWord_373924) baseStart_373924 baseEnd_373924 := by
    simpa [prefixWord, tailWord_373924, baseEnd_373924] using wordTrace_append hprefix tailTrace_373924
  have hstable : (prefixWord ++ tailWord_373924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373924).length < 2 ^ (prefixWord ++ tailWord_373924).sum := by decide
  have hdescent : baseEnd_373924 < baseStart_373924 := by decide
  rcases family_descends (prefixWord ++ tailWord_373924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373938 : List Nat := [3, 2, 1, 1, 1, 4, 8]
def baseStart_373938 : Nat := 118140960795 + 373938 * 2 ^ 59
def prefixEnd_373938 : Nat := 4983230072969 + 3 ^ 40 * 373938 * 2
def baseEnd_373938 : Nat := 18963943603067970326449

theorem tailTrace_373938 : CollatzResearch.WordTrace tailWord_373938 prefixEnd_373938 18963943603067970326449 := by
  unfold tailWord_373938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3409659829823491092768617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9092426212862642914049645 3409659829823491092768617)
  ·
    refine ⟨2557244872367618319576463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3409659829823491092768617 2557244872367618319576463)
    ·
      refine ⟨3835867308551427479364695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557244872367618319576463 3835867308551427479364695)
      ·
        refine ⟨5753800962827141219047043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835867308551427479364695 5753800962827141219047043)
        ·
          refine ⟨8630701444240711828570565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5753800962827141219047043 8630701444240711828570565)
          ·
            refine ⟨1618256520795133467856981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8630701444240711828570565 1618256520795133467856981)
            ·
              refine ⟨18963943603067970326449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1618256520795133467856981 18963943603067970326449)
              ·
                rfl

theorem cell20_373938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_373938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373938 prefixEnd_373938 := by exact prefixLift 373938
  have htrace : WordTrace (prefixWord ++ tailWord_373938) baseStart_373938 baseEnd_373938 := by
    simpa [prefixWord, tailWord_373938, baseEnd_373938] using wordTrace_append hprefix tailTrace_373938
  have hstable : (prefixWord ++ tailWord_373938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373938).length < 2 ^ (prefixWord ++ tailWord_373938).sum := by decide
  have hdescent : baseEnd_373938 < baseStart_373938 := by decide
  rcases family_descends (prefixWord ++ tailWord_373938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373948 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_373948 : Nat := 118140960795 + 373948 * 2 ^ 59
def prefixEnd_373948 : Nat := 4983230072969 + 3 ^ 40 * 373948 * 2
def baseEnd_373948 : Nat := 170680056700096142604667

theorem tailTrace_373948 : CollatzResearch.WordTrace tailWord_373948 prefixEnd_373948 170680056700096142604667 := by
  unfold tailWord_373948
  simp only [CollatzResearch.WordTrace]
  refine ⟨6819502024628868039469249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9092669366171824052625665 6819502024628868039469249)
  ·
    refine ⟨5114626518471651029601937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6819502024628868039469249 5114626518471651029601937)
    ·
      refine ⟨3835969888853738272201453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5114626518471651029601937 3835969888853738272201453)
      ·
        refine ⟨1438488708320151852075545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3835969888853738272201453 1438488708320151852075545)
        ·
          refine ⟨1078866531240113889056659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1438488708320151852075545 1078866531240113889056659)
          ·
            refine ⟨1618299796860170833584989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078866531240113889056659 1618299796860170833584989)
            ·
              refine ⟨606862423822564062594371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1618299796860170833584989 606862423822564062594371)
              ·
                refine ⟨910293635733846093891557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606862423822564062594371 910293635733846093891557)
                ·
                  refine ⟨170680056700096142604667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910293635733846093891557 170680056700096142604667)
                  ·
                    rfl

theorem cell20_373948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_373948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373948 prefixEnd_373948 := by exact prefixLift 373948
  have htrace : WordTrace (prefixWord ++ tailWord_373948) baseStart_373948 baseEnd_373948 := by
    simpa [prefixWord, tailWord_373948, baseEnd_373948] using wordTrace_append hprefix tailTrace_373948
  have hstable : (prefixWord ++ tailWord_373948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373948).length < 2 ^ (prefixWord ++ tailWord_373948).sum := by decide
  have hdescent : baseEnd_373948 < baseStart_373948 := by decide
  rcases family_descends (prefixWord ++ tailWord_373948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373983 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_373983 : Nat := 118140960795 + 373983 * 2 ^ 59
def prefixEnd_373983 : Nat := 4983230072969 + 3 ^ 40 * 373983 * 2
def baseEnd_373983 : Nat := 170696031653791576437857

theorem tailTrace_373983 : CollatzResearch.WordTrace tailWord_373983 prefixEnd_373983 170696031653791576437857 := by
  unfold tailWord_373983
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640280604130937056462603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9093520402753958037641735 13640280604130937056462603)
  ·
    refine ⟨20460420906196405584693905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13640280604130937056462603 20460420906196405584693905)
    ·
      refine ⟨15345315679647304188520429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20460420906196405584693905 15345315679647304188520429)
      ·
        refine ⟨5754493379867739070695161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15345315679647304188520429 5754493379867739070695161)
        ·
          refine ⟨4315870034900804303021371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5754493379867739070695161 4315870034900804303021371)
          ·
            refine ⟨6473805052351206454532057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4315870034900804303021371 6473805052351206454532057)
            ·
              refine ⟨4855353789263404840899043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6473805052351206454532057 4855353789263404840899043)
              ·
                refine ⟨7283030683895107261348565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4855353789263404840899043 7283030683895107261348565)
                ·
                  refine ⟨170696031653791576437857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7283030683895107261348565 170696031653791576437857)
                  ·
                    rfl

theorem cell20_373983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_373983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373983 prefixEnd_373983 := by exact prefixLift 373983
  have htrace : WordTrace (prefixWord ++ tailWord_373983) baseStart_373983 baseEnd_373983 := by
    simpa [prefixWord, tailWord_373983, baseEnd_373983] using wordTrace_append hprefix tailTrace_373983
  have hstable : (prefixWord ++ tailWord_373983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373983).length < 2 ^ (prefixWord ++ tailWord_373983).sum := by decide
  have hdescent : baseEnd_373983 < baseStart_373983 := by decide
  rcases family_descends (prefixWord ++ tailWord_373983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373999 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 2]
def baseStart_373999 : Nat := 118140960795 + 373999 * 2 ^ 59
def prefixEnd_373999 : Nat := 4983230072969 + 3 ^ 40 * 373999 * 2
def baseEnd_373999 : Nat := 170703334489766631904459

theorem tailTrace_373999 : CollatzResearch.WordTrace tailWord_373999 prefixEnd_373999 170703334489766631904459 := by
  unfold tailWord_373999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640864172072971789045051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9093909448048647859363367 13640864172072971789045051)
  ·
    refine ⟨20461296258109457683567577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13640864172072971789045051 20461296258109457683567577)
    ·
      refine ⟨15345972193582093262675683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20461296258109457683567577 15345972193582093262675683)
      ·
        refine ⟨23018958290373139894013525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15345972193582093262675683 23018958290373139894013525)
        ·
          refine ⟨269753417465310233132971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 23018958290373139894013525 269753417465310233132971)
          ·
            refine ⟨404630126197965349699457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269753417465310233132971 404630126197965349699457)
            ·
              refine ⟨303472594648474012274593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404630126197965349699457 303472594648474012274593)
              ·
                refine ⟨227604445986355509205945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303472594648474012274593 227604445986355509205945)
                ·
                  refine ⟨170703334489766631904459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227604445986355509205945 170703334489766631904459)
                  ·
                    rfl

theorem cell20_373999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 2].length) (baseStart_373999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_373999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_373999 prefixEnd_373999 := by exact prefixLift 373999
  have htrace : WordTrace (prefixWord ++ tailWord_373999) baseStart_373999 baseEnd_373999 := by
    simpa [prefixWord, tailWord_373999, baseEnd_373999] using wordTrace_append hprefix tailTrace_373999
  have hstable : (prefixWord ++ tailWord_373999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373999).length < 2 ^ (prefixWord ++ tailWord_373999).sum := by decide
  have hdescent : baseEnd_373999 < baseStart_373999 := by decide
  rcases family_descends (prefixWord ++ tailWord_373999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374003 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 2]
def baseStart_374003 : Nat := 118140960795 + 374003 * 2 ^ 59
def prefixEnd_374003 : Nat := 4983230072969 + 3 ^ 40 * 374003 * 2
def baseEnd_374003 : Nat := 170705160198760395771109

theorem tailTrace_374003 : CollatzResearch.WordTrace tailWord_374003 prefixEnd_374003 170705160198760395771109 := by
  unfold tailWord_374003
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641010064058480472190663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9094006709372320314793775 13641010064058480472190663)
  ·
    refine ⟨20461515096087720708285995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13641010064058480472190663 20461515096087720708285995)
    ·
      refine ⟨30692272644131581062428993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20461515096087720708285995 30692272644131581062428993)
      ·
        refine ⟨23019204483098685796821745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30692272644131581062428993 23019204483098685796821745)
        ·
          refine ⟨17264403362324014347616309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23019204483098685796821745 17264403362324014347616309)
          ·
            refine ⟨1618537815217876345089029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17264403362324014347616309 1618537815217876345089029)
            ·
              refine ⟨303475840353351814704193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1618537815217876345089029 303475840353351814704193)
              ·
                refine ⟨227606880265013861028145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303475840353351814704193 227606880265013861028145)
                ·
                  refine ⟨170705160198760395771109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227606880265013861028145 170705160198760395771109)
                  ·
                    rfl

theorem cell20_374003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 2].length) (baseStart_374003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374003 prefixEnd_374003 := by exact prefixLift 374003
  have htrace : WordTrace (prefixWord ++ tailWord_374003) baseStart_374003 baseEnd_374003 := by
    simpa [prefixWord, tailWord_374003, baseEnd_374003] using wordTrace_append hprefix tailTrace_374003
  have hstable : (prefixWord ++ tailWord_374003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374003).length < 2 ^ (prefixWord ++ tailWord_374003).sum := by decide
  have hdescent : baseEnd_374003 < baseStart_374003 := by decide
  rcases family_descends (prefixWord ++ tailWord_374003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374024 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_374024 : Nat := 118140960795 + 374024 * 2 ^ 59
def prefixEnd_374024 : Nat := 4983230072969 + 3 ^ 40 * 374024 * 2
def baseEnd_374024 : Nat := 170714745170977656071023

theorem tailTrace_374024 : CollatzResearch.WordTrace tailWord_374024 prefixEnd_374024 170714745170977656071023 := by
  unfold tailWord_374024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820887998491200529352563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9094517331321600705803417 6820887998491200529352563)
  ·
    refine ⟨10231331997736800794028845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6820887998491200529352563 10231331997736800794028845)
    ·
      refine ⟨3836749499151300297760817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10231331997736800794028845 3836749499151300297760817)
      ·
        refine ⟨2877562124363475223320613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3836749499151300297760817 2877562124363475223320613)
        ·
          refine ⟨539542898318151604372615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2877562124363475223320613 539542898318151604372615)
          ·
            refine ⟨809314347477227406558923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539542898318151604372615 809314347477227406558923)
            ·
              refine ⟨1213971521215841109838385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809314347477227406558923 1213971521215841109838385)
              ·
                refine ⟨910478640911880832378789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213971521215841109838385 910478640911880832378789)
                ·
                  refine ⟨170714745170977656071023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910478640911880832378789 170714745170977656071023)
                  ·
                    rfl

theorem cell20_374024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_374024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374024 prefixEnd_374024 := by exact prefixLift 374024
  have htrace : WordTrace (prefixWord ++ tailWord_374024) baseStart_374024 baseEnd_374024 := by
    simpa [prefixWord, tailWord_374024, baseEnd_374024] using wordTrace_append hprefix tailTrace_374024
  have hstable : (prefixWord ++ tailWord_374024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374024).length < 2 ^ (prefixWord ++ tailWord_374024).sum := by decide
  have hdescent : baseEnd_374024 < baseStart_374024 := by decide
  rcases family_descends (prefixWord ++ tailWord_374024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374052 : List Nat := [2, 3, 1, 3, 1, 1, 9]
def baseStart_374052 : Nat := 118140960795 + 374052 * 2 ^ 59
def prefixEnd_374052 : Nat := 4983230072969 + 3 ^ 40 * 374052 * 2
def baseEnd_374052 : Nat := 18969725014881555904175

theorem tailTrace_374052 : CollatzResearch.WordTrace tailWord_374052 prefixEnd_374052 18969725014881555904175 := by
  unfold tailWord_374052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821398620440480920362205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9095198160587307893816273 6821398620440480920362205)
  ·
    refine ⟨2558024482665180345135827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6821398620440480920362205 2558024482665180345135827)
    ·
      refine ⟨3837036723997770517703741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558024482665180345135827 3837036723997770517703741)
      ·
        refine ⟨1438888771499163944138903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3837036723997770517703741 1438888771499163944138903)
        ·
          refine ⟨2158333157248745916208355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438888771499163944138903 2158333157248745916208355)
          ·
            refine ⟨3237499735873118874312533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158333157248745916208355 3237499735873118874312533)
            ·
              refine ⟨18969725014881555904175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3237499735873118874312533 18969725014881555904175)
              ·
                rfl

theorem cell20_374052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_374052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374052 prefixEnd_374052 := by exact prefixLift 374052
  have htrace : WordTrace (prefixWord ++ tailWord_374052) baseStart_374052 baseEnd_374052 := by
    simpa [prefixWord, tailWord_374052, baseEnd_374052] using wordTrace_append hprefix tailTrace_374052
  have hstable : (prefixWord ++ tailWord_374052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374052).length < 2 ^ (prefixWord ++ tailWord_374052).sum := by decide
  have hdescent : baseEnd_374052 < baseStart_374052 := by decide
  rcases family_descends (prefixWord ++ tailWord_374052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374097 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_374097 : Nat := 118140960795 + 374097 * 2 ^ 59
def prefixEnd_374097 : Nat := 4983230072969 + 3 ^ 40 * 374097 * 2
def baseEnd_374097 : Nat := 170748064360113846637391

theorem tailTrace_374097 : CollatzResearch.WordTrace tailWord_374097 prefixEnd_374097 170748064360113846637391 := by
  unfold tailWord_374097
  simp only [CollatzResearch.WordTrace]
  refine ⟨13644438525717934526112545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9096292350478623017408363 13644438525717934526112545)
  ·
    refine ⟨10233328894288450894584409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13644438525717934526112545 10233328894288450894584409)
    ·
      refine ⟨7674996670716338170938307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10233328894288450894584409 7674996670716338170938307)
      ·
        refine ⟨11512495006074507256407461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674996670716338170938307 11512495006074507256407461)
        ·
          refine ⟨2158592813638970110576399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11512495006074507256407461 2158592813638970110576399)
          ·
            refine ⟨3237889220458455165864599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158592813638970110576399 3237889220458455165864599)
            ·
              refine ⟨4856833830687682748796899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237889220458455165864599 4856833830687682748796899)
              ·
                refine ⟨7285250746031524123195349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856833830687682748796899 7285250746031524123195349)
                ·
                  refine ⟨170748064360113846637391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7285250746031524123195349 170748064360113846637391)
                  ·
                    rfl

theorem cell20_374097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_374097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374097 prefixEnd_374097 := by exact prefixLift 374097
  have htrace : WordTrace (prefixWord ++ tailWord_374097) baseStart_374097 baseEnd_374097 := by
    simpa [prefixWord, tailWord_374097, baseEnd_374097] using wordTrace_append hprefix tailTrace_374097
  have hstable : (prefixWord ++ tailWord_374097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374097).length < 2 ^ (prefixWord ++ tailWord_374097).sum := by decide
  have hdescent : baseEnd_374097 < baseStart_374097 := by decide
  rcases family_descends (prefixWord ++ tailWord_374097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374114 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_374114 : Nat := 118140960795 + 374114 * 2 ^ 59
def prefixEnd_374114 : Nat := 4983230072969 + 3 ^ 40 * 374114 * 2
def baseEnd_374114 : Nat := 170755823623337343070655

theorem tailTrace_374114 : CollatzResearch.WordTrace tailWord_374114 prefixEnd_374114 170755823623337343070655 := by
  unfold tailWord_374114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411264641664086607370349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9096705711104230952987597 3411264641664086607370349)
  ·
    refine ⟨1279224240624032477763881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3411264641664086607370349 1279224240624032477763881)
    ·
      refine ⟨959418180468024358322911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1279224240624032477763881 959418180468024358322911)
      ·
        refine ⟨1439127270702036537484367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959418180468024358322911 1439127270702036537484367)
        ·
          refine ⟨2158690906053054806226551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439127270702036537484367 2158690906053054806226551)
          ·
            refine ⟨3238036359079582209339827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158690906053054806226551 3238036359079582209339827)
            ·
              refine ⟨4857054538619373314009741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238036359079582209339827 4857054538619373314009741)
              ·
                refine ⟨1821395451982264992753653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4857054538619373314009741 1821395451982264992753653)
                ·
                  refine ⟨170755823623337343070655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821395451982264992753653 170755823623337343070655)
                  ·
                    rfl

theorem cell20_374114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_374114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374114 prefixEnd_374114 := by exact prefixLift 374114
  have htrace : WordTrace (prefixWord ++ tailWord_374114) baseStart_374114 baseEnd_374114 := by
    simpa [prefixWord, tailWord_374114, baseEnd_374114] using wordTrace_append hprefix tailTrace_374114
  have hstable : (prefixWord ++ tailWord_374114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374114).length < 2 ^ (prefixWord ++ tailWord_374114).sum := by decide
  have hdescent : baseEnd_374114 < baseStart_374114 := by decide
  rcases family_descends (prefixWord ++ tailWord_374114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374117 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 2]
def baseStart_374117 : Nat := 118140960795 + 374117 * 2 ^ 59
def prefixEnd_374117 : Nat := 4983230072969 + 3 ^ 40 * 374117 * 2
def baseEnd_374117 : Nat := 170757192905082665970643

theorem tailTrace_374117 : CollatzResearch.WordTrace tailWord_374117 prefixEnd_374117 170757192905082665970643 := by
  unfold tailWord_374117
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645167985645477941840605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9096778657096985294560403 13645167985645477941840605)
  ·
    refine ⟨5116937994617054228190227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13645167985645477941840605 5116937994617054228190227)
    ·
      refine ⟨7675406991925581342285341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5116937994617054228190227 7675406991925581342285341)
      ·
        refine ⟨2878277621972093003357003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7675406991925581342285341 2878277621972093003357003)
        ·
          refine ⟨4317416432958139505035505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878277621972093003357003 4317416432958139505035505)
          ·
            refine ⟨3238062324718604628776629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4317416432958139505035505 3238062324718604628776629)
            ·
              refine ⟨303568342942369183947809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3238062324718604628776629 303568342942369183947809)
              ·
                refine ⟨227676257206776887960857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303568342942369183947809 227676257206776887960857)
                ·
                  refine ⟨170757192905082665970643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227676257206776887960857 170757192905082665970643)
                  ·
                    rfl

theorem cell20_374117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_374117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374117 prefixEnd_374117 := by exact prefixLift 374117
  have htrace : WordTrace (prefixWord ++ tailWord_374117) baseStart_374117 baseEnd_374117 := by
    simpa [prefixWord, tailWord_374117, baseEnd_374117] using wordTrace_append hprefix tailTrace_374117
  have hstable : (prefixWord ++ tailWord_374117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374117).length < 2 ^ (prefixWord ++ tailWord_374117).sum := by decide
  have hdescent : baseEnd_374117 < baseStart_374117 := by decide
  rcases family_descends (prefixWord ++ tailWord_374117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374128 : List Nat := [2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_374128 : Nat := 118140960795 + 374128 * 2 ^ 59
def prefixEnd_374128 : Nat := 4983230072969 + 3 ^ 40 * 374128 * 2
def baseEnd_374128 : Nat := 56920737868271838867977

theorem tailTrace_374128 : CollatzResearch.WordTrace tailWord_374128 prefixEnd_374128 56920737868271838867977 := by
  unfold tailWord_374128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822784594302813410245519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9097046125737084546994025 6822784594302813410245519)
  ·
    refine ⟨10234176891454220115368279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6822784594302813410245519 10234176891454220115368279)
    ·
      refine ⟨15351265337181330173052419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10234176891454220115368279 15351265337181330173052419)
      ·
        refine ⟨23026898005771995259578629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15351265337181330173052419 23026898005771995259578629)
        ·
          refine ⟨4317543376082249111170993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23026898005771995259578629 4317543376082249111170993)
          ·
            refine ⟨3238157532061686833378245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4317543376082249111170993 3238157532061686833378245)
            ·
              refine ⟨607154537261566281258421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3238157532061686833378245 607154537261566281258421)
              ·
                refine ⟨56920737868271838867977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 607154537261566281258421 56920737868271838867977)
                ·
                  rfl

theorem cell20_374128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_374128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374128 prefixEnd_374128 := by exact prefixLift 374128
  have htrace : WordTrace (prefixWord ++ tailWord_374128) baseStart_374128 baseEnd_374128 := by
    simpa [prefixWord, tailWord_374128, baseEnd_374128] using wordTrace_append hprefix tailTrace_374128
  have hstable : (prefixWord ++ tailWord_374128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374128).length < 2 ^ (prefixWord ++ tailWord_374128).sum := by decide
  have hdescent : baseEnd_374128 < baseStart_374128 := by decide
  rcases family_descends (prefixWord ++ tailWord_374128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374162 : List Nat := [3, 2, 3, 3, 2, 7]
def baseStart_374162 : Nat := 118140960795 + 374162 * 2 ^ 59
def prefixEnd_374162 : Nat := 4983230072969 + 3 ^ 40 * 374162 * 2
def baseEnd_374162 : Nat := 6325101190046759610017

theorem tailTrace_374162 : CollatzResearch.WordTrace tailWord_374162 prefixEnd_374162 6325101190046759610017 := by
  unfold tailWord_374162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411702317620612656807185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9097872846988300418152493 3411702317620612656807185)
  ·
    refine ⟨2558776738215459492605389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3411702317620612656807185 2558776738215459492605389)
    ·
      refine ⟨959541276830797309727021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2558776738215459492605389 959541276830797309727021)
      ·
        refine ⟨359827978811548991147633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 959541276830797309727021 359827978811548991147633)
        ·
          refine ⟨269870984108661743360725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359827978811548991147633 269870984108661743360725)
          ·
            refine ⟨6325101190046759610017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 269870984108661743360725 6325101190046759610017)
            ·
              rfl

theorem cell20_374162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 7].length) (baseStart_374162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374162 prefixEnd_374162 := by exact prefixLift 374162
  have htrace : WordTrace (prefixWord ++ tailWord_374162) baseStart_374162 baseEnd_374162 := by
    simpa [prefixWord, tailWord_374162, baseEnd_374162] using wordTrace_append hprefix tailTrace_374162
  have hstable : (prefixWord ++ tailWord_374162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374162).length < 2 ^ (prefixWord ++ tailWord_374162).sum := by decide
  have hdescent : baseEnd_374162 < baseStart_374162 := by decide
  rcases family_descends (prefixWord ++ tailWord_374162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374172 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 2]
def baseStart_374172 : Nat := 118140960795 + 374172 * 2 ^ 59
def prefixEnd_374172 : Nat := 4983230072969 + 3 ^ 40 * 374172 * 2
def baseEnd_374172 : Nat := 170782296403746919137085

theorem tailTrace_374172 : CollatzResearch.WordTrace tailWord_374172 prefixEnd_374172 170782296403746919137085 := by
  unfold tailWord_374172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823587000223111167546385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9098116000297481556728513 6823587000223111167546385)
  ·
    refine ⟨5117690250167333375659789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6823587000223111167546385 5117690250167333375659789)
    ·
      refine ⟨1919133843812750015872421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5117690250167333375659789 1919133843812750015872421)
      ·
        refine ⟨359837595714890627976079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1919133843812750015872421 359837595714890627976079)
        ·
          refine ⟨539756393572335941964119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359837595714890627976079 539756393572335941964119)
          ·
            refine ⟨809634590358503912946179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539756393572335941964119 809634590358503912946179)
            ·
              refine ⟨1214451885537755869419269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809634590358503912946179 1214451885537755869419269)
              ·
                refine ⟨227709728538329225516113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1214451885537755869419269 227709728538329225516113)
                ·
                  refine ⟨170782296403746919137085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227709728538329225516113 170782296403746919137085)
                  ·
                    rfl

theorem cell20_374172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_374172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374172 prefixEnd_374172 := by exact prefixLift 374172
  have htrace : WordTrace (prefixWord ++ tailWord_374172) baseStart_374172 baseEnd_374172 := by
    simpa [prefixWord, tailWord_374172, baseEnd_374172] using wordTrace_append hprefix tailTrace_374172
  have hstable : (prefixWord ++ tailWord_374172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374172).length < 2 ^ (prefixWord ++ tailWord_374172).sum := by decide
  have hdescent : baseEnd_374172 < baseStart_374172 := by decide
  rcases family_descends (prefixWord ++ tailWord_374172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374176 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 2]
def baseStart_374176 : Nat := 118140960795 + 374176 * 2 ^ 59
def prefixEnd_374176 : Nat := 4983230072969 + 3 ^ 40 * 374176 * 2
def baseEnd_374176 : Nat := 170784122112740683003735

theorem tailTrace_374176 : CollatzResearch.WordTrace tailWord_374176 prefixEnd_374176 170784122112740683003735 := by
  unfold tailWord_374176
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823659946215865509119191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9098213261621154012158921 6823659946215865509119191)
  ·
    refine ⟨10235489919323798263678787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6823659946215865509119191 10235489919323798263678787)
    ·
      refine ⟨15353234878985697395518181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10235489919323798263678787 15353234878985697395518181)
      ·
        refine ⟨2878731539809818261659659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15353234878985697395518181 2878731539809818261659659)
        ·
          refine ⟨4318097309714727392489489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878731539809818261659659 4318097309714727392489489)
          ·
            refine ⟨3238572982286045544367117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318097309714727392489489 3238572982286045544367117)
            ·
              refine ⟨1214464868357267079137669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3238572982286045544367117 1214464868357267079137669)
              ·
                refine ⟨227712162816987577338313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1214464868357267079137669 227712162816987577338313)
                ·
                  refine ⟨170784122112740683003735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227712162816987577338313 170784122112740683003735)
                  ·
                    rfl

theorem cell20_374176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_374176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374176 prefixEnd_374176 := by exact prefixLift 374176
  have htrace : WordTrace (prefixWord ++ tailWord_374176) baseStart_374176 baseEnd_374176 := by
    simpa [prefixWord, tailWord_374176, baseEnd_374176] using wordTrace_append hprefix tailTrace_374176
  have hstable : (prefixWord ++ tailWord_374176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374176).length < 2 ^ (prefixWord ++ tailWord_374176).sum := by decide
  have hdescent : baseEnd_374176 < baseStart_374176 := by decide
  rcases family_descends (prefixWord ++ tailWord_374176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374197 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_374197 : Nat := 118140960795 + 374197 * 2 ^ 59
def prefixEnd_374197 : Nat := 4983230072969 + 3 ^ 40 * 374197 * 2
def baseEnd_374197 : Nat := 170793707084957943303649

theorem tailTrace_374197 : CollatzResearch.WordTrace tailWord_374197 prefixEnd_374197 170793707084957943303649 := by
  unfold tailWord_374197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13648085825355651604752845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9098723883570434403168563 13648085825355651604752845)
  ·
    refine ⟨5118032184508369351782317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13648085825355651604752845 5118032184508369351782317)
    ·
      refine ⟨1919262069190638506918369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5118032184508369351782317 1919262069190638506918369)
      ·
        refine ⟨1439446551892978880188777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919262069190638506918369 1439446551892978880188777)
        ·
          refine ⟨1079584913919734160141583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439446551892978880188777 1079584913919734160141583)
          ·
            refine ⟨1619377370879601240212375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079584913919734160141583 1619377370879601240212375)
            ·
              refine ⟨2429066056319401860318563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619377370879601240212375 2429066056319401860318563)
              ·
                refine ⟨3643599084479102790477845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429066056319401860318563 3643599084479102790477845)
                ·
                  refine ⟨170793707084957943303649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3643599084479102790477845 170793707084957943303649)
                  ·
                    rfl

theorem cell20_374197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_374197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374197 prefixEnd_374197 := by exact prefixLift 374197
  have htrace : WordTrace (prefixWord ++ tailWord_374197) baseStart_374197 baseEnd_374197 := by
    simpa [prefixWord, tailWord_374197, baseEnd_374197] using wordTrace_append hprefix tailTrace_374197
  have hstable : (prefixWord ++ tailWord_374197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374197).length < 2 ^ (prefixWord ++ tailWord_374197).sum := by decide
  have hdescent : baseEnd_374197 < baseStart_374197 := by decide
  rcases family_descends (prefixWord ++ tailWord_374197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374269 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 2]
def baseStart_374269 : Nat := 118140960795 + 374269 * 2 ^ 59
def prefixEnd_374269 : Nat := 4983230072969 + 3 ^ 40 * 374269 * 2
def baseEnd_374269 : Nat := 170826569846845692903355

theorem tailTrace_374269 : CollatzResearch.WordTrace tailWord_374269 prefixEnd_374269 170826569846845692903355 := by
  unfold tailWord_374269
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650711881094807901373861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9100474587396538600915907 13650711881094807901373861)
  ·
    refine ⟨2559508477705276481507599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13650711881094807901373861 2559508477705276481507599)
    ·
      refine ⟨3839262716557914722261399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559508477705276481507599 3839262716557914722261399)
      ·
        refine ⟨5758894074836872083392099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839262716557914722261399 5758894074836872083392099)
        ·
          refine ⟨8638341112255308125088149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5758894074836872083392099 8638341112255308125088149)
          ·
            refine ⟨404922239636967568363507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8638341112255308125088149 404922239636967568363507)
            ·
              refine ⟨607383359455451352545261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404922239636967568363507 607383359455451352545261)
              ·
                refine ⟨227768759795794257204473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607383359455451352545261 227768759795794257204473)
                ·
                  refine ⟨170826569846845692903355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227768759795794257204473 170826569846845692903355)
                  ·
                    rfl

theorem cell20_374269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_374269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374269 prefixEnd_374269 := by exact prefixLift 374269
  have htrace : WordTrace (prefixWord ++ tailWord_374269) baseStart_374269 baseEnd_374269 := by
    simpa [prefixWord, tailWord_374269, baseEnd_374269] using wordTrace_append hprefix tailTrace_374269
  have hstable : (prefixWord ++ tailWord_374269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374269).length < 2 ^ (prefixWord ++ tailWord_374269).sum := by decide
  have hdescent : baseEnd_374269 < baseStart_374269 := by decide
  rcases family_descends (prefixWord ++ tailWord_374269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374276 : List Nat := [2, 3, 2, 3, 3, 1, 6]
def baseStart_374276 : Nat := 118140960795 + 374276 * 2 ^ 59
def prefixEnd_374276 : Nat := 4983230072969 + 3 ^ 40 * 374276 * 2
def baseEnd_374276 : Nat := 18981084981953864407777

theorem tailTrace_374276 : CollatzResearch.WordTrace tailWord_374276 prefixEnd_374276 18981084981953864407777 := by
  unfold tailWord_374276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825483596034724048439341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9100644794712965397919121 6825483596034724048439341)
  ·
    refine ⟨2559556348513021518164753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6825483596034724048439341 2559556348513021518164753)
    ·
      refine ⟨1919667261384766138623565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2559556348513021518164753 1919667261384766138623565)
      ·
        refine ⟨719875223019287301983837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1919667261384766138623565 719875223019287301983837)
        ·
          refine ⟨269953208632232738243939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 719875223019287301983837 269953208632232738243939)
          ·
            refine ⟨404929812948349107365909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269953208632232738243939 404929812948349107365909)
            ·
              refine ⟨18981084981953864407777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 404929812948349107365909 18981084981953864407777)
              ·
                rfl

theorem cell20_374276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 6].length) (baseStart_374276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374276 prefixEnd_374276 := by exact prefixLift 374276
  have htrace : WordTrace (prefixWord ++ tailWord_374276) baseStart_374276 baseEnd_374276 := by
    simpa [prefixWord, tailWord_374276, baseEnd_374276] using wordTrace_append hprefix tailTrace_374276
  have hstable : (prefixWord ++ tailWord_374276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374276).length < 2 ^ (prefixWord ++ tailWord_374276).sum := by decide
  have hdescent : baseEnd_374276 < baseStart_374276 := by decide
  rcases family_descends (prefixWord ++ tailWord_374276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374286 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_374286 : Nat := 118140960795 + 374286 * 2 ^ 59
def prefixEnd_374286 : Nat := 4983230072969 + 3 ^ 40 * 374286 * 2
def baseEnd_374286 : Nat := 170834329110069189336619

theorem tailTrace_374286 : CollatzResearch.WordTrace tailWord_374286 prefixEnd_374286 170834329110069189336619 := by
  unfold tailWord_374286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706416490254152475592839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9100887948022146536495141 1706416490254152475592839)
  ·
    refine ⟨2559624735381228713389259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706416490254152475592839 2559624735381228713389259)
    ·
      refine ⟨3839437103071843070083889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559624735381228713389259 3839437103071843070083889)
      ·
        refine ⟨2879577827303882302562917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3839437103071843070083889 2879577827303882302562917)
        ·
          refine ⟨539920842619477931730547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2879577827303882302562917 539920842619477931730547)
          ·
            refine ⟨809881263929216897595821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539920842619477931730547 809881263929216897595821)
            ·
              refine ⟨303705473973456336598433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 809881263929216897595821 303705473973456336598433)
              ·
                refine ⟨227779105480092252448825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303705473973456336598433 227779105480092252448825)
                ·
                  refine ⟨170834329110069189336619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227779105480092252448825 170834329110069189336619)
                  ·
                    rfl

theorem cell20_374286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_374286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374286 prefixEnd_374286 := by exact prefixLift 374286
  have htrace : WordTrace (prefixWord ++ tailWord_374286) baseStart_374286 baseEnd_374286 := by
    simpa [prefixWord, tailWord_374286, baseEnd_374286] using wordTrace_append hprefix tailTrace_374286
  have hstable : (prefixWord ++ tailWord_374286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374286).length < 2 ^ (prefixWord ++ tailWord_374286).sum := by decide
  have hdescent : baseEnd_374286 < baseStart_374286 := by decide
  rcases family_descends (prefixWord ++ tailWord_374286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374373 : List Nat := [1, 3, 1, 3, 3, 2, 3, 4]
def baseStart_374373 : Nat := 118140960795 + 374373 * 2 ^ 59
def prefixEnd_374373 : Nat := 4983230072969 + 3 ^ 40 * 374373 * 2
def baseEnd_374373 : Nat := 56958012760227851145421

theorem tailTrace_374373 : CollatzResearch.WordTrace tailWord_374373 prefixEnd_374373 56958012760227851145421 := by
  unfold tailWord_374373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654505072718033663159773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9103003381812022442106515 13654505072718033663159773)
  ·
    refine ⟨5120439402269262623684915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13654505072718033663159773 5120439402269262623684915)
    ·
      refine ⟨7680659103403893935527373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5120439402269262623684915 7680659103403893935527373)
      ·
        refine ⟨2880247163776460225822765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7680659103403893935527373 2880247163776460225822765)
        ·
          refine ⟨1080092686416172584683537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2880247163776460225822765 1080092686416172584683537)
          ·
            refine ⟨810069514812129438512653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080092686416172584683537 810069514812129438512653)
            ·
              refine ⟨303776068054548539442245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810069514812129438512653 303776068054548539442245)
              ·
                refine ⟨56958012760227851145421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303776068054548539442245 56958012760227851145421)
                ·
                  rfl

theorem cell20_374373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_374373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374373 prefixEnd_374373 := by exact prefixLift 374373
  have htrace : WordTrace (prefixWord ++ tailWord_374373) baseStart_374373 baseEnd_374373 := by
    simpa [prefixWord, tailWord_374373, baseEnd_374373] using wordTrace_append hprefix tailTrace_374373
  have hstable : (prefixWord ++ tailWord_374373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374373).length < 2 ^ (prefixWord ++ tailWord_374373).sum := by decide
  have hdescent : baseEnd_374373 < baseStart_374373 := by decide
  rcases family_descends (prefixWord ++ tailWord_374373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374377 : List Nat := [1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_374377 : Nat := 118140960795 + 374377 * 2 ^ 59
def prefixEnd_374377 : Nat := 4983230072969 + 3 ^ 40 * 374377 * 2
def baseEnd_374377 : Nat := 56958621329892439100971

theorem tailTrace_374377 : CollatzResearch.WordTrace tailWord_374377 prefixEnd_374377 56958621329892439100971 := by
  unfold tailWord_374377
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654650964703542346305385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9103100643135694897536923 13654650964703542346305385)
  ·
    refine ⟨10240988223527656759729039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13654650964703542346305385 10240988223527656759729039)
    ·
      refine ⟨15361482335291485139593559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10240988223527656759729039 15361482335291485139593559)
      ·
        refine ⟨23042223502937227709390339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15361482335291485139593559 23042223502937227709390339)
        ·
          refine ⟨34563335254405841564085509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23042223502937227709390339 34563335254405841564085509)
          ·
            refine ⟨6480625360201095293266033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34563335254405841564085509 6480625360201095293266033)
            ·
              refine ⟨4860469020150821469949525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6480625360201095293266033 4860469020150821469949525)
              ·
                refine ⟨56958621329892439100971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4860469020150821469949525 56958621329892439100971)
                ·
                  rfl

theorem cell20_374377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_374377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374377 prefixEnd_374377 := by exact prefixLift 374377
  have htrace : WordTrace (prefixWord ++ tailWord_374377) baseStart_374377 baseEnd_374377 := by
    simpa [prefixWord, tailWord_374377, baseEnd_374377] using wordTrace_append hprefix tailTrace_374377
  have hstable : (prefixWord ++ tailWord_374377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374377).length < 2 ^ (prefixWord ++ tailWord_374377).sum := by decide
  have hdescent : baseEnd_374377 < baseStart_374377 := by decide
  rcases family_descends (prefixWord ++ tailWord_374377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374397 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 3]
def baseStart_374397 : Nat := 118140960795 + 374397 * 2 ^ 59
def prefixEnd_374397 : Nat := 4983230072969 + 3 ^ 40 * 374397 * 2
def baseEnd_374397 : Nat := 170884992534646136636165

theorem tailTrace_374397 : CollatzResearch.WordTrace tailWord_374397 prefixEnd_374397 170884992534646136636165 := by
  unfold tailWord_374397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13655380424631085762033445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9103586949754057174688963 13655380424631085762033445)
  ·
    refine ⟨2560383829618328580381271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13655380424631085762033445 2560383829618328580381271)
    ·
      refine ⟨3840575744427492870571907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560383829618328580381271 3840575744427492870571907)
      ·
        refine ⟨5760863616641239305857861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840575744427492870571907 5760863616641239305857861)
        ·
          refine ⟨1080161928120232369848349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5760863616641239305857861 1080161928120232369848349)
          ·
            refine ⟨405060723045087138693131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1080161928120232369848349 405060723045087138693131)
            ·
              refine ⟨607591084567630708039697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405060723045087138693131 607591084567630708039697)
              ·
                refine ⟨455693313425723031029773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607591084567630708039697 455693313425723031029773)
                ·
                  refine ⟨170884992534646136636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455693313425723031029773 170884992534646136636165)
                  ·
                    rfl

theorem cell20_374397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_374397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374397 prefixEnd_374397 := by exact prefixLift 374397
  have htrace : WordTrace (prefixWord ++ tailWord_374397) baseStart_374397 baseEnd_374397 := by
    simpa [prefixWord, tailWord_374397, baseEnd_374397] using wordTrace_append hprefix tailTrace_374397
  have hstable : (prefixWord ++ tailWord_374397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374397).length < 2 ^ (prefixWord ++ tailWord_374397).sum := by decide
  have hdescent : baseEnd_374397 < baseStart_374397 := by decide
  rcases family_descends (prefixWord ++ tailWord_374397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374404 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_374404 : Nat := 118140960795 + 374404 * 2 ^ 59
def prefixEnd_374404 : Nat := 4983230072969 + 3 ^ 40 * 374404 * 2
def baseEnd_374404 : Nat := 170888187525385223402803

theorem tailTrace_374404 : CollatzResearch.WordTrace tailWord_374404 prefixEnd_374404 170888187525385223402803 := by
  unfold tailWord_374404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6827817867802862978769133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9103757157070483971692177 6827817867802862978769133)
  ·
    refine ⟨2560431700426073617038425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6827817867802862978769133 2560431700426073617038425)
    ·
      refine ⟨1920323775319555212778819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2560431700426073617038425 1920323775319555212778819)
      ·
        refine ⟨2880485662979332819168229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920323775319555212778819 2880485662979332819168229)
        ·
          refine ⟨540091061808624903594043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2880485662979332819168229 540091061808624903594043)
          ·
            refine ⟨810136592712937355391065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540091061808624903594043 810136592712937355391065)
            ·
              refine ⟨607602444534703016543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810136592712937355391065 607602444534703016543299)
              ·
                refine ⟨911403666802054524814949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607602444534703016543299 911403666802054524814949)
                ·
                  refine ⟨170888187525385223402803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911403666802054524814949 170888187525385223402803)
                  ·
                    rfl

theorem cell20_374404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_374404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374404 prefixEnd_374404 := by exact prefixLift 374404
  have htrace : WordTrace (prefixWord ++ tailWord_374404) baseStart_374404 baseEnd_374404 := by
    simpa [prefixWord, tailWord_374404, baseEnd_374404] using wordTrace_append hprefix tailTrace_374404
  have hstable : (prefixWord ++ tailWord_374404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374404).length < 2 ^ (prefixWord ++ tailWord_374404).sum := by decide
  have hdescent : baseEnd_374404 < baseStart_374404 := by decide
  rcases family_descends (prefixWord ++ tailWord_374404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374428 : List Nat := [2, 2, 3, 2, 3, 2, 2, 4]
def baseStart_374428 : Nat := 118140960795 + 374428 * 2 ^ 59
def prefixEnd_374428 : Nat := 4983230072969 + 3 ^ 40 * 374428 * 2
def baseEnd_374428 : Nat := 56966380593115935534235

theorem tailTrace_374428 : CollatzResearch.WordTrace tailWord_374428 prefixEnd_374428 56966380593115935534235 := by
  unfold tailWord_374428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828255543759389028205969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9104340725012518704274625 6828255543759389028205969)
  ·
    refine ⟨5121191657819541771154477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6828255543759389028205969 5121191657819541771154477)
    ·
      refine ⟨1920446871682328164182929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5121191657819541771154477 1920446871682328164182929)
      ·
        refine ⟨1440335153761746123137197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920446871682328164182929 1440335153761746123137197)
        ·
          refine ⟨540125682660654796176449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1440335153761746123137197 540125682660654796176449)
          ·
            refine ⟨405094261995491097132337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540125682660654796176449 405094261995491097132337)
            ·
              refine ⟨303820696496618322849253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405094261995491097132337 303820696496618322849253)
              ·
                refine ⟨56966380593115935534235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303820696496618322849253 56966380593115935534235)
                ·
                  rfl

theorem cell20_374428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_374428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374428 prefixEnd_374428 := by exact prefixLift 374428
  have htrace : WordTrace (prefixWord ++ tailWord_374428) baseStart_374428 baseEnd_374428 := by
    simpa [prefixWord, tailWord_374428, baseEnd_374428] using wordTrace_append hprefix tailTrace_374428
  have hstable : (prefixWord ++ tailWord_374428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374428).length < 2 ^ (prefixWord ++ tailWord_374428).sum := by decide
  have hdescent : baseEnd_374428 < baseStart_374428 := by decide
  rcases family_descends (prefixWord ++ tailWord_374428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374432 : List Nat := [2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_374432 : Nat := 118140960795 + 374432 * 2 ^ 59
def prefixEnd_374432 : Nat := 4983230072969 + 3 ^ 40 * 374432 * 2
def baseEnd_374432 : Nat := 56966989162780523489785

theorem tailTrace_374432 : CollatzResearch.WordTrace tailWord_374432 prefixEnd_374432 56966989162780523489785 := by
  unfold tailWord_374432
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828328489752143369778775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9104437986336191159705033 6828328489752143369778775)
  ·
    refine ⟨10242492734628215054668163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6828328489752143369778775 10242492734628215054668163)
    ·
      refine ⟨15363739101942322582002245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242492734628215054668163 15363739101942322582002245)
      ·
        refine ⟨2880701081614185484125421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15363739101942322582002245 2880701081614185484125421)
        ·
          refine ⟨1080262905605319556547033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2880701081614185484125421 1080262905605319556547033)
          ·
            refine ⟨810197179203989667410275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080262905605319556547033 810197179203989667410275)
            ·
              refine ⟨1215295768805984501115413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810197179203989667410275 1215295768805984501115413)
              ·
                refine ⟨56966989162780523489785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1215295768805984501115413 56966989162780523489785)
                ·
                  rfl

theorem cell20_374432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_374432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374432 prefixEnd_374432 := by exact prefixLift 374432
  have htrace : WordTrace (prefixWord ++ tailWord_374432) baseStart_374432 baseEnd_374432 := by
    simpa [prefixWord, tailWord_374432, baseEnd_374432] using wordTrace_append hprefix tailTrace_374432
  have hstable : (prefixWord ++ tailWord_374432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374432).length < 2 ^ (prefixWord ++ tailWord_374432).sum := by decide
  have hdescent : baseEnd_374432 < baseStart_374432 := by decide
  rcases family_descends (prefixWord ++ tailWord_374432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374515 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_374515 : Nat := 118140960795 + 374515 * 2 ^ 59
def prefixEnd_374515 : Nat := 4983230072969 + 3 ^ 40 * 374515 * 2
def baseEnd_374515 : Nat := 170938850949962170702349

theorem tailTrace_374515 : CollatzResearch.WordTrace tailWord_374515 prefixEnd_374515 170938850949962170702349 := by
  unfold tailWord_374515
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659684238203591914828999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9106456158802394609885999 13659684238203591914828999)
  ·
    refine ⟨20489526357305387872243499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13659684238203591914828999 20489526357305387872243499)
    ·
      refine ⟨30734289535958081808365249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20489526357305387872243499 30734289535958081808365249)
      ·
        refine ⟨23050717151968561356273937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30734289535958081808365249 23050717151968561356273937)
        ·
          refine ⟨17288037863976421017205453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23050717151968561356273937 17288037863976421017205453)
          ·
            refine ⟨6483014198991157881452045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17288037863976421017205453 6483014198991157881452045)
            ·
              refine ⟨2431130324621684205544517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6483014198991157881452045 2431130324621684205544517)
              ·
                refine ⟨455836935866565788539597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2431130324621684205544517 455836935866565788539597)
                ·
                  refine ⟨170938850949962170702349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455836935866565788539597 170938850949962170702349)
                  ·
                    rfl

theorem cell20_374515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_374515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374515 prefixEnd_374515 := by exact prefixLift 374515
  have htrace : WordTrace (prefixWord ++ tailWord_374515) baseStart_374515 baseEnd_374515 := by
    simpa [prefixWord, tailWord_374515, baseEnd_374515] using wordTrace_append hprefix tailTrace_374515
  have hstable : (prefixWord ++ tailWord_374515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374515).length < 2 ^ (prefixWord ++ tailWord_374515).sum := by decide
  have hdescent : baseEnd_374515 < baseStart_374515 := by decide
  rcases family_descends (prefixWord ++ tailWord_374515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374522 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_374522 : Nat := 118140960795 + 374522 * 2 ^ 59
def prefixEnd_374522 : Nat := 4983230072969 + 3 ^ 40 * 374522 * 2
def baseEnd_374522 : Nat := 170942045940701257468987

theorem tailTrace_374522 : CollatzResearch.WordTrace tailWord_374522 prefixEnd_374522 170942045940701257468987 := by
  unfold tailWord_374522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414984887294558027583455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9106626366118821406889213 3414984887294558027583455)
  ·
    refine ⟨5122477330941837041375183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3414984887294558027583455 5122477330941837041375183)
    ·
      refine ⟨7683715996412755562062775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5122477330941837041375183 7683715996412755562062775)
      ·
        refine ⟨11525573994619133343094163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7683715996412755562062775 11525573994619133343094163)
        ·
          refine ⟨17288360991928700014641245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11525573994619133343094163 17288360991928700014641245)
          ·
            refine ⟨6483135371973262505490467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17288360991928700014641245 6483135371973262505490467)
            ·
              refine ⟨9724703057959893758235701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6483135371973262505490467 9724703057959893758235701)
              ·
                refine ⟨911690911683740039834597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9724703057959893758235701 911690911683740039834597)
                ·
                  refine ⟨170942045940701257468987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911690911683740039834597 170942045940701257468987)
                  ·
                    rfl

theorem cell20_374522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_374522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374522 prefixEnd_374522 := by exact prefixLift 374522
  have htrace : WordTrace (prefixWord ++ tailWord_374522) baseStart_374522 baseEnd_374522 := by
    simpa [prefixWord, tailWord_374522, baseEnd_374522] using wordTrace_append hprefix tailTrace_374522
  have hstable : (prefixWord ++ tailWord_374522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374522).length < 2 ^ (prefixWord ++ tailWord_374522).sum := by decide
  have hdescent : baseEnd_374522 < baseStart_374522 := by decide
  rcases family_descends (prefixWord ++ tailWord_374522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374532 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_374532 : Nat := 118140960795 + 374532 * 2 ^ 59
def prefixEnd_374532 : Nat := 4983230072969 + 3 ^ 40 * 374532 * 2
def baseEnd_374532 : Nat := 170946610213185667135613

theorem tailTrace_374532 : CollatzResearch.WordTrace tailWord_374532 prefixEnd_374532 170946610213185667135613 := by
  unfold tailWord_374532
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830152139571001909098925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9106869519428002545465233 6830152139571001909098925)
  ·
    refine ⟨2561307052339125715912097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6830152139571001909098925 2561307052339125715912097)
    ·
      refine ⟨1920980289254344286934073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2561307052339125715912097 1920980289254344286934073)
      ·
        refine ⟨1440735216940758215200555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920980289254344286934073 1440735216940758215200555)
        ·
          refine ⟨2161102825411137322800833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440735216940758215200555 2161102825411137322800833)
          ·
            refine ⟨1620827119058352992100625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161102825411137322800833 1620827119058352992100625)
            ·
              refine ⟨1215620339293764744075469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620827119058352992100625 1215620339293764744075469)
              ·
                refine ⟨455857627235161779028301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1215620339293764744075469 455857627235161779028301)
                ·
                  refine ⟨170946610213185667135613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455857627235161779028301 170946610213185667135613)
                  ·
                    rfl

theorem cell20_374532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_374532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374532 prefixEnd_374532 := by exact prefixLift 374532
  have htrace : WordTrace (prefixWord ++ tailWord_374532) baseStart_374532 baseEnd_374532 := by
    simpa [prefixWord, tailWord_374532, baseEnd_374532] using wordTrace_append hprefix tailTrace_374532
  have hstable : (prefixWord ++ tailWord_374532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374532).length < 2 ^ (prefixWord ++ tailWord_374532).sum := by decide
  have hdescent : baseEnd_374532 < baseStart_374532 := by decide
  rcases family_descends (prefixWord ++ tailWord_374532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374556 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 2]
def baseStart_374556 : Nat := 118140960795 + 374556 * 2 ^ 59
def prefixEnd_374556 : Nat := 4983230072969 + 3 ^ 40 * 374556 * 2
def baseEnd_374556 : Nat := 170957564467148250335515

theorem tailTrace_374556 : CollatzResearch.WordTrace tailWord_374556 prefixEnd_374556 170957564467148250335515 := by
  unfold tailWord_374556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830589815527527958535761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9107453087370037278047681 6830589815527527958535761)
  ·
    refine ⟨5122942361645645968901821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6830589815527527958535761 5122942361645645968901821)
    ·
      refine ⟨1921103385617117238338183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5122942361645645968901821 1921103385617117238338183)
      ·
        refine ⟨2881655078425675857507275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921103385617117238338183 2881655078425675857507275)
        ·
          refine ⟨4322482617638513786260913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881655078425675857507275 4322482617638513786260913)
          ·
            refine ⟨3241861963228885339695685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322482617638513786260913 3241861963228885339695685)
            ·
              refine ⟨607849118105416001192941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3241861963228885339695685 607849118105416001192941)
              ·
                refine ⟨227943419289531000447353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607849118105416001192941 227943419289531000447353)
                ·
                  refine ⟨170957564467148250335515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227943419289531000447353 170957564467148250335515)
                  ·
                    rfl

theorem cell20_374556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_374556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374556 prefixEnd_374556 := by exact prefixLift 374556
  have htrace : WordTrace (prefixWord ++ tailWord_374556) baseStart_374556 baseEnd_374556 := by
    simpa [prefixWord, tailWord_374556, baseEnd_374556] using wordTrace_append hprefix tailTrace_374556
  have hstable : (prefixWord ++ tailWord_374556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374556).length < 2 ^ (prefixWord ++ tailWord_374556).sum := by decide
  have hdescent : baseEnd_374556 < baseStart_374556 := by decide
  rcases family_descends (prefixWord ++ tailWord_374556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374560 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_374560 : Nat := 118140960795 + 374560 * 2 ^ 59
def prefixEnd_374560 : Nat := 4983230072969 + 3 ^ 40 * 374560 * 2
def baseEnd_374560 : Nat := 170959390176142014202165

theorem tailTrace_374560 : CollatzResearch.WordTrace tailWord_374560 prefixEnd_374560 170959390176142014202165 := by
  unfold tailWord_374560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830662761520282300108567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9107550348693709733478089 6830662761520282300108567)
  ·
    refine ⟨10245994142280423450162851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6830662761520282300108567 10245994142280423450162851)
    ·
      refine ⟨15368991213420635175244277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10245994142280423450162851 15368991213420635175244277)
      ·
        refine ⟨1440842926258184547679151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15368991213420635175244277 1440842926258184547679151)
        ·
          refine ⟨2161264389387276821518727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440842926258184547679151 2161264389387276821518727)
          ·
            refine ⟨3241896584080915232278091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161264389387276821518727 3241896584080915232278091)
            ·
              refine ⟨4862844876121372848417137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241896584080915232278091 4862844876121372848417137)
              ·
                refine ⟨3647133657091029636312853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4862844876121372848417137 3647133657091029636312853)
                ·
                  refine ⟨170959390176142014202165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3647133657091029636312853 170959390176142014202165)
                  ·
                    rfl

theorem cell20_374560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_374560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374560 prefixEnd_374560 := by exact prefixLift 374560
  have htrace : WordTrace (prefixWord ++ tailWord_374560) baseStart_374560 baseEnd_374560 := by
    simpa [prefixWord, tailWord_374560, baseEnd_374560] using wordTrace_append hprefix tailTrace_374560
  have hstable : (prefixWord ++ tailWord_374560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374560).length < 2 ^ (prefixWord ++ tailWord_374560).sum := by decide
  have hdescent : baseEnd_374560 < baseStart_374560 := by decide
  rcases family_descends (prefixWord ++ tailWord_374560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374577 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_374577 : Nat := 118140960795 + 374577 * 2 ^ 59
def prefixEnd_374577 : Nat := 4983230072969 + 3 ^ 40 * 374577 * 2
def baseEnd_374577 : Nat := 170967149439365510635429

theorem tailTrace_374577 : CollatzResearch.WordTrace tailWord_374577 prefixEnd_374577 170967149439365510635429 := by
  unfold tailWord_374577
  simp only [CollatzResearch.WordTrace]
  refine ⟨13661945563978976503585985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9107963709319317669057323 13661945563978976503585985)
  ·
    refine ⟨10246459172984232377689489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13661945563978976503585985 10246459172984232377689489)
    ·
      refine ⟨7684844379738174283267117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10246459172984232377689489 7684844379738174283267117)
      ·
        refine ⟨2881816642401815356225169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7684844379738174283267117 2881816642401815356225169)
        ·
          refine ⟨2161362481801361517168877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2881816642401815356225169 2161362481801361517168877)
          ·
            refine ⟨810510930675510568938329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2161362481801361517168877 810510930675510568938329)
            ·
              refine ⟨607883198006632926703747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810510930675510568938329 607883198006632926703747)
              ·
                refine ⟨911824797009949390055621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607883198006632926703747 911824797009949390055621)
                ·
                  refine ⟨170967149439365510635429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911824797009949390055621 170967149439365510635429)
                  ·
                    rfl

theorem cell20_374577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_374577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374577 prefixEnd_374577 := by exact prefixLift 374577
  have htrace : WordTrace (prefixWord ++ tailWord_374577) baseStart_374577 baseEnd_374577 := by
    simpa [prefixWord, tailWord_374577, baseEnd_374577] using wordTrace_append hprefix tailTrace_374577
  have hstable : (prefixWord ++ tailWord_374577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374577).length < 2 ^ (prefixWord ++ tailWord_374577).sum := by decide
  have hdescent : baseEnd_374577 < baseStart_374577 := by decide
  rcases family_descends (prefixWord ++ tailWord_374577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374629 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_374629 : Nat := 118140960795 + 374629 * 2 ^ 59
def prefixEnd_374629 : Nat := 4983230072969 + 3 ^ 40 * 374629 * 2
def baseEnd_374629 : Nat := 170990883656284440901883

theorem tailTrace_374629 : CollatzResearch.WordTrace tailWord_374629 prefixEnd_374629 170990883656284440901883 := by
  unfold tailWord_374629
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663842159790589384478941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9109228106527059589652627 13663842159790589384478941)
  ·
    refine ⟨5123940809921471019179603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13663842159790589384478941 5123940809921471019179603)
    ·
      refine ⟨7685911214882206528769405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5123940809921471019179603 7685911214882206528769405)
      ·
        refine ⟨2882216705580827448288527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7685911214882206528769405 2882216705580827448288527)
        ·
          refine ⟨4323325058371241172432791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882216705580827448288527 4323325058371241172432791)
          ·
            refine ⟨6484987587556861758649187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323325058371241172432791 6484987587556861758649187)
            ·
              refine ⟨9727481381335292637973781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484987587556861758649187 9727481381335292637973781)
              ·
                refine ⟨455975689750091842405021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9727481381335292637973781 455975689750091842405021)
                ·
                  refine ⟨170990883656284440901883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455975689750091842405021 170990883656284440901883)
                  ·
                    rfl

theorem cell20_374629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_374629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374629 prefixEnd_374629 := by exact prefixLift 374629
  have htrace : WordTrace (prefixWord ++ tailWord_374629) baseStart_374629 baseEnd_374629 := by
    simpa [prefixWord, tailWord_374629, baseEnd_374629] using wordTrace_append hprefix tailTrace_374629
  have hstable : (prefixWord ++ tailWord_374629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374629).length < 2 ^ (prefixWord ++ tailWord_374629).sum := by decide
  have hdescent : baseEnd_374629 < baseStart_374629 := by decide
  rcases family_descends (prefixWord ++ tailWord_374629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374684 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_374684 : Nat := 118140960795 + 374684 * 2 ^ 59
def prefixEnd_374684 : Nat := 4983230072969 + 3 ^ 40 * 374684 * 2
def baseEnd_374684 : Nat := 171015987154948694068325

theorem tailTrace_374684 : CollatzResearch.WordTrace tailWord_374684 prefixEnd_374684 171015987154948694068325 := by
  unfold tailWord_374684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6832924087295666888865553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9110565449727555851820737 6832924087295666888865553)
  ·
    refine ⟨5124693065471750166649165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6832924087295666888865553 5124693065471750166649165)
    ·
      refine ⟨1921759899551906312493437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5124693065471750166649165 1921759899551906312493437)
      ·
        refine ⟨720659962331964867185039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1921759899551906312493437 720659962331964867185039)
        ·
          refine ⟨1080989943497947300777559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720659962331964867185039 1080989943497947300777559)
          ·
            refine ⟨1621484915246920951166339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080989943497947300777559 1621484915246920951166339)
            ·
              refine ⟨2432227372870381426749509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621484915246920951166339 2432227372870381426749509)
              ·
                refine ⟨456042632413196517515533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2432227372870381426749509 456042632413196517515533)
                ·
                  refine ⟨171015987154948694068325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456042632413196517515533 171015987154948694068325)
                  ·
                    rfl

theorem cell20_374684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_374684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374684 prefixEnd_374684 := by exact prefixLift 374684
  have htrace : WordTrace (prefixWord ++ tailWord_374684) baseStart_374684 baseEnd_374684 := by
    simpa [prefixWord, tailWord_374684, baseEnd_374684] using wordTrace_append hprefix tailTrace_374684
  have hstable : (prefixWord ++ tailWord_374684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374684).length < 2 ^ (prefixWord ++ tailWord_374684).sum := by decide
  have hdescent : baseEnd_374684 < baseStart_374684 := by decide
  rcases family_descends (prefixWord ++ tailWord_374684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374712 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_374712 : Nat := 118140960795 + 374712 * 2 ^ 59
def prefixEnd_374712 : Nat := 4983230072969 + 3 ^ 40 * 374712 * 2
def baseEnd_374712 : Nat := 171028767117905041134877

theorem tailTrace_374712 : CollatzResearch.WordTrace tailWord_374712 prefixEnd_374712 171028767117905041134877 := by
  unfold tailWord_374712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6833434709244947279875195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9111246278993263039833593 6833434709244947279875195)
  ·
    refine ⟨10250152063867420919812793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6833434709244947279875195 10250152063867420919812793)
    ·
      refine ⟨7687614047900565689859595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10250152063867420919812793 7687614047900565689859595)
      ·
        refine ⟨11531421071850848534789393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7687614047900565689859595 11531421071850848534789393)
        ·
          refine ⟨8648565803888136401092045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11531421071850848534789393 8648565803888136401092045)
          ·
            refine ⟨3243212176458051150409517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8648565803888136401092045 3243212176458051150409517)
            ·
              refine ⟨1216204566171769181403569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3243212176458051150409517 1216204566171769181403569)
              ·
                refine ⟨912153424628826886052677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216204566171769181403569 912153424628826886052677)
                ·
                  refine ⟨171028767117905041134877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912153424628826886052677 171028767117905041134877)
                  ·
                    rfl

theorem cell20_374712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_374712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374712 prefixEnd_374712 := by exact prefixLift 374712
  have htrace : WordTrace (prefixWord ++ tailWord_374712) baseStart_374712 baseEnd_374712 := by
    simpa [prefixWord, tailWord_374712, baseEnd_374712] using wordTrace_append hprefix tailTrace_374712
  have hstable : (prefixWord ++ tailWord_374712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374712).length < 2 ^ (prefixWord ++ tailWord_374712).sum := by decide
  have hdescent : baseEnd_374712 < baseStart_374712 := by decide
  rcases family_descends (prefixWord ++ tailWord_374712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374797 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 4]
def baseStart_374797 : Nat := 118140960795 + 374797 * 2 ^ 59
def prefixEnd_374797 : Nat := 4983230072969 + 3 ^ 40 * 374797 * 2
def baseEnd_374797 : Nat := 171067563434022523301197

theorem tailTrace_374797 : CollatzResearch.WordTrace tailWord_374797 prefixEnd_374797 171067563434022523301197 := by
  unfold tailWord_374797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669969623181954076594645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9113313082121302717729763 13669969623181954076594645)
  ·
    refine ⟨320389913043327048670187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13669969623181954076594645 320389913043327048670187)
    ·
      refine ⟨480584869564990573005281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320389913043327048670187 480584869564990573005281)
      ·
        refine ⟨360438652173742929753961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480584869564990573005281 360438652173742929753961)
        ·
          refine ⟨270328989130307197315471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360438652173742929753961 270328989130307197315471)
          ·
            refine ⟨405493483695460795973207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270328989130307197315471 405493483695460795973207)
            ·
              refine ⟨608240225543191193959811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405493483695460795973207 608240225543191193959811)
              ·
                refine ⟨912360338314786790939717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608240225543191193959811 912360338314786790939717)
                ·
                  refine ⟨171067563434022523301197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912360338314786790939717 171067563434022523301197)
                  ·
                    rfl

theorem cell20_374797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_374797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374797 prefixEnd_374797 := by exact prefixLift 374797
  have htrace : WordTrace (prefixWord ++ tailWord_374797) baseStart_374797 baseEnd_374797 := by
    simpa [prefixWord, tailWord_374797, baseEnd_374797] using wordTrace_append hprefix tailTrace_374797
  have hstable : (prefixWord ++ tailWord_374797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374797).length < 2 ^ (prefixWord ++ tailWord_374797).sum := by decide
  have hdescent : baseEnd_374797 < baseStart_374797 := by decide
  rcases family_descends (prefixWord ++ tailWord_374797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374812 : List Nat := [2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_374812 : Nat := 118140960795 + 374812 * 2 ^ 59
def prefixEnd_374812 : Nat := 4983230072969 + 3 ^ 40 * 374812 * 2
def baseEnd_374812 : Nat := 57024803280916379267045

theorem tailTrace_374812 : CollatzResearch.WordTrace tailWord_374812 prefixEnd_374812 57024803280916379267045 := by
  unfold tailWord_374812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835258359063805819195345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9113677812085074425593793 6835258359063805819195345)
  ·
    refine ⟨5126443769297854364396509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6835258359063805819195345 5126443769297854364396509)
    ·
      refine ⟨1922416413486695386648691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5126443769297854364396509 1922416413486695386648691)
      ·
        refine ⟨2883624620230043079973037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922416413486695386648691 2883624620230043079973037)
        ·
          refine ⟨1081359232586266154989889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2883624620230043079973037 1081359232586266154989889)
          ·
            refine ⟨811019424439699616242417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081359232586266154989889 811019424439699616242417)
            ·
              refine ⟨608264568329774712181813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811019424439699616242417 608264568329774712181813)
              ·
                refine ⟨57024803280916379267045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 608264568329774712181813 57024803280916379267045)
                ·
                  rfl

theorem cell20_374812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_374812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374812 prefixEnd_374812 := by exact prefixLift 374812
  have htrace : WordTrace (prefixWord ++ tailWord_374812) baseStart_374812 baseEnd_374812 := by
    simpa [prefixWord, tailWord_374812, baseEnd_374812] using wordTrace_append hprefix tailTrace_374812
  have hstable : (prefixWord ++ tailWord_374812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374812).length < 2 ^ (prefixWord ++ tailWord_374812).sum := by decide
  have hdescent : baseEnd_374812 < baseStart_374812 := by decide
  rcases family_descends (prefixWord ++ tailWord_374812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374819 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_374819 : Nat := 118140960795 + 374819 * 2 ^ 59
def prefixEnd_374819 : Nat := 4983230072969 + 3 ^ 40 * 374819 * 2
def baseEnd_374819 : Nat := 171077604833488224567773

theorem tailTrace_374819 : CollatzResearch.WordTrace tailWord_374819 prefixEnd_374819 171077604833488224567773 := by
  unfold tailWord_374819
  simp only [CollatzResearch.WordTrace]
  refine ⟨13670772029102251833895511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9113848019401501222597007 13670772029102251833895511)
  ·
    refine ⟨20506158043653377750843267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13670772029102251833895511 20506158043653377750843267)
    ·
      refine ⟨30759237065480066626264901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20506158043653377750843267 30759237065480066626264901)
      ·
        refine ⟨5767356949777512492424669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30759237065480066626264901 5767356949777512492424669)
        ·
          refine ⟨2162758856166567184659251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5767356949777512492424669 2162758856166567184659251)
          ·
            refine ⟨3244138284249850776988877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162758856166567184659251 3244138284249850776988877)
            ·
              refine ⟨1216551856593694041370829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3244138284249850776988877 1216551856593694041370829)
              ·
                refine ⟨456206946222635265514061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216551856593694041370829 456206946222635265514061)
                ·
                  refine ⟨171077604833488224567773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456206946222635265514061 171077604833488224567773)
                  ·
                    rfl

theorem cell20_374819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_374819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374819 prefixEnd_374819 := by exact prefixLift 374819
  have htrace : WordTrace (prefixWord ++ tailWord_374819) baseStart_374819 baseEnd_374819 := by
    simpa [prefixWord, tailWord_374819, baseEnd_374819] using wordTrace_append hprefix tailTrace_374819
  have hstable : (prefixWord ++ tailWord_374819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374819).length < 2 ^ (prefixWord ++ tailWord_374819).sum := by decide
  have hdescent : baseEnd_374819 < baseStart_374819 := by decide
  rcases family_descends (prefixWord ++ tailWord_374819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374833 : List Nat := [1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_374833 : Nat := 118140960795 + 374833 * 2 ^ 59
def prefixEnd_374833 : Nat := 4983230072969 + 3 ^ 40 * 374833 * 2
def baseEnd_374833 : Nat := 57027998271655466033683

theorem tailTrace_374833 : CollatzResearch.WordTrace tailWord_374833 prefixEnd_374833 57027998271655466033683 := by
  unfold tailWord_374833
  simp only [CollatzResearch.WordTrace]
  refine ⟨13671282651051532224905153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9114188434034354816603435 13671282651051532224905153)
  ·
    refine ⟨10253461988288649168678865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13671282651051532224905153 10253461988288649168678865)
    ·
      refine ⟨7690096491216486876509149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10253461988288649168678865 7690096491216486876509149)
      ·
        refine ⟨2883786184206182578690931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7690096491216486876509149 2883786184206182578690931)
        ·
          refine ⟨4325679276309273868036397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883786184206182578690931 4325679276309273868036397)
          ·
            refine ⟨1622129728615977700513649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4325679276309273868036397 1622129728615977700513649)
            ·
              refine ⟨1216597296461983275385237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622129728615977700513649 1216597296461983275385237)
              ·
                refine ⟨57027998271655466033683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1216597296461983275385237 57027998271655466033683)
                ·
                  rfl

theorem cell20_374833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_374833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374833 prefixEnd_374833 := by exact prefixLift 374833
  have htrace : WordTrace (prefixWord ++ tailWord_374833) baseStart_374833 baseEnd_374833 := by
    simpa [prefixWord, tailWord_374833, baseEnd_374833] using wordTrace_append hprefix tailTrace_374833
  have hstable : (prefixWord ++ tailWord_374833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374833).length < 2 ^ (prefixWord ++ tailWord_374833).sum := by decide
  have hdescent : baseEnd_374833 < baseStart_374833 := by decide
  rcases family_descends (prefixWord ++ tailWord_374833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374857 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_374857 : Nat := 118140960795 + 374857 * 2 ^ 59
def prefixEnd_374857 : Nat := 4983230072969 + 3 ^ 40 * 374857 * 2
def baseEnd_374857 : Nat := 171094949068928981300951

theorem tailTrace_374857 : CollatzResearch.WordTrace tailWord_374857 prefixEnd_374857 171094949068928981300951 := by
  unfold tailWord_374857
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672158002964584323778825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9114772001976389549185883 13672158002964584323778825)
  ·
    refine ⟨10254118502223438242834119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13672158002964584323778825 10254118502223438242834119)
    ·
      refine ⟨15381177753335157364251179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254118502223438242834119 15381177753335157364251179)
      ·
        refine ⟨23071766630002736046376769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15381177753335157364251179 23071766630002736046376769)
        ·
          refine ⟨17303824972502052034782577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23071766630002736046376769 17303824972502052034782577)
          ·
            refine ⟨12977868729376539026086933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17303824972502052034782577 12977868729376539026086933)
            ·
              refine ⟨608337596689525266847825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12977868729376539026086933 608337596689525266847825)
              ·
                refine ⟨456253197517143950135869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608337596689525266847825 456253197517143950135869)
                ·
                  refine ⟨171094949068928981300951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456253197517143950135869 171094949068928981300951)
                  ·
                    rfl

theorem cell20_374857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_374857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374857 prefixEnd_374857 := by exact prefixLift 374857
  have htrace : WordTrace (prefixWord ++ tailWord_374857) baseStart_374857 baseEnd_374857 := by
    simpa [prefixWord, tailWord_374857, baseEnd_374857] using wordTrace_append hprefix tailTrace_374857
  have hstable : (prefixWord ++ tailWord_374857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374857).length < 2 ^ (prefixWord ++ tailWord_374857).sum := by decide
  have hdescent : baseEnd_374857 < baseStart_374857 := by decide
  rcases family_descends (prefixWord ++ tailWord_374857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374860 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 2]
def baseStart_374860 : Nat := 118140960795 + 374860 * 2 ^ 59
def prefixEnd_374860 : Nat := 4983230072969 + 3 ^ 40 * 374860 * 2
def baseEnd_374860 : Nat := 171096318350674304200939

theorem tailTrace_374860 : CollatzResearch.WordTrace tailWord_374860 prefixEnd_374860 171096318350674304200939 := by
  unfold tailWord_374860
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836133710976857918069017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9114844947969143890758689 6836133710976857918069017)
  ·
    refine ⟨5127100283232643438551763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6836133710976857918069017 5127100283232643438551763)
    ·
      refine ⟨7690650424848965157827645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127100283232643438551763 7690650424848965157827645)
      ·
        refine ⟨2883993909318361934185367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7690650424848965157827645 2883993909318361934185367)
        ·
          refine ⟨4325990863977542901278051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883993909318361934185367 4325990863977542901278051)
          ·
            refine ⟨6488986295966314351917077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325990863977542901278051 6488986295966314351917077)
            ·
              refine ⟨304171232623420985246113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6488986295966314351917077 304171232623420985246113)
              ·
                refine ⟨228128424467565738934585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304171232623420985246113 228128424467565738934585)
                ·
                  refine ⟨171096318350674304200939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228128424467565738934585 171096318350674304200939)
                  ·
                    rfl

theorem cell20_374860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_374860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374860 prefixEnd_374860 := by exact prefixLift 374860
  have htrace : WordTrace (prefixWord ++ tailWord_374860) baseStart_374860 baseEnd_374860 := by
    simpa [prefixWord, tailWord_374860, baseEnd_374860] using wordTrace_append hprefix tailTrace_374860
  have hstable : (prefixWord ++ tailWord_374860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374860).length < 2 ^ (prefixWord ++ tailWord_374860).sum := by decide
  have hdescent : baseEnd_374860 < baseStart_374860 := by decide
  rcases family_descends (prefixWord ++ tailWord_374860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374871 : List Nat := [1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_374871 : Nat := 118140960795 + 374871 * 2 ^ 59
def prefixEnd_374871 : Nat := 4983230072969 + 3 ^ 40 * 374871 * 2
def baseEnd_374871 : Nat := 57033779683469051611409

theorem tailTrace_374871 : CollatzResearch.WordTrace tailWord_374871 prefixEnd_374871 57033779683469051611409 := by
  unfold tailWord_374871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672668624913864714788467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9115112416609243143192311 13672668624913864714788467)
  ·
    refine ⟨20509002937370797072182701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13672668624913864714788467 20509002937370797072182701)
    ·
      refine ⟨7690876101514048902068513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20509002937370797072182701 7690876101514048902068513)
      ·
        refine ⟨5768157076135536676551385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7690876101514048902068513 5768157076135536676551385)
        ·
          refine ⟨4326117807101652507413539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5768157076135536676551385 4326117807101652507413539)
          ·
            refine ⟨6489176710652478761120309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326117807101652507413539 6489176710652478761120309)
            ·
              refine ⟨608360316623669883855029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6489176710652478761120309 608360316623669883855029)
              ·
                refine ⟨57033779683469051611409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 608360316623669883855029 57033779683469051611409)
                ·
                  rfl

theorem cell20_374871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_374871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374871 prefixEnd_374871 := by exact prefixLift 374871
  have htrace : WordTrace (prefixWord ++ tailWord_374871) baseStart_374871 baseEnd_374871 := by
    simpa [prefixWord, tailWord_374871, baseEnd_374871] using wordTrace_append hprefix tailTrace_374871
  have hstable : (prefixWord ++ tailWord_374871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374871).length < 2 ^ (prefixWord ++ tailWord_374871).sum := by decide
  have hdescent : baseEnd_374871 < baseStart_374871 := by decide
  rcases family_descends (prefixWord ++ tailWord_374871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374898 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_374898 : Nat := 118140960795 + 374898 * 2 ^ 59
def prefixEnd_374898 : Nat := 4983230072969 + 3 ^ 40 * 374898 * 2
def baseEnd_374898 : Nat := 171113662586115060934117

theorem tailTrace_374898 : CollatzResearch.WordTrace tailWord_374898 prefixEnd_374898 171113662586115060934117 := by
  unfold tailWord_374898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418413348954012081505337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9115768930544032217347565 3418413348954012081505337)
  ·
    refine ⟨2563810011715509061129003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3418413348954012081505337 2563810011715509061129003)
    ·
      refine ⟨3845715017573263591693505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563810011715509061129003 3845715017573263591693505)
      ·
        refine ⟨2884286263179947693770129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845715017573263591693505 2884286263179947693770129)
        ·
          refine ⟨2163214697384960770327597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2884286263179947693770129 2163214697384960770327597)
          ·
            refine ⟨811205511519360288872849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2163214697384960770327597 811205511519360288872849)
            ·
              refine ⟨608404133639520216654637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811205511519360288872849 608404133639520216654637)
              ·
                refine ⟨228151550114820081245489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608404133639520216654637 228151550114820081245489)
                ·
                  refine ⟨171113662586115060934117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228151550114820081245489 171113662586115060934117)
                  ·
                    rfl

theorem cell20_374898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_374898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374898 prefixEnd_374898 := by exact prefixLift 374898
  have htrace : WordTrace (prefixWord ++ tailWord_374898) baseStart_374898 baseEnd_374898 := by
    simpa [prefixWord, tailWord_374898, baseEnd_374898] using wordTrace_append hprefix tailTrace_374898
  have hstable : (prefixWord ++ tailWord_374898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374898).length < 2 ^ (prefixWord ++ tailWord_374898).sum := by decide
  have hdescent : baseEnd_374898 < baseStart_374898 := by decide
  rcases family_descends (prefixWord ++ tailWord_374898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374909 : List Nat := [1, 4, 1, 1, 3, 3, 7]
def baseStart_374909 : Nat := 118140960795 + 374909 * 2 ^ 59
def prefixEnd_374909 : Nat := 4983230072969 + 3 ^ 40 * 374909 * 2
def baseEnd_374909 : Nat := 19013187031760879063045

theorem tailTrace_374909 : CollatzResearch.WordTrace tailWord_374909 prefixEnd_374909 19013187031760879063045 := by
  unfold tailWord_374909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674054598776197204671781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9116036399184131469781187 13674054598776197204671781)
  ·
    refine ⟨2563885237270536975875959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13674054598776197204671781 2563885237270536975875959)
    ·
      refine ⟨3845827855905805463813939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563885237270536975875959 3845827855905805463813939)
      ·
        refine ⟨5768741783858708195720909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845827855905805463813939 5768741783858708195720909)
        ·
          refine ⟨2163278168947015573395341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5768741783858708195720909 2163278168947015573395341)
          ·
            refine ⟨811229313355130840023253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2163278168947015573395341 811229313355130840023253)
            ·
              refine ⟨19013187031760879063045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 811229313355130840023253 19013187031760879063045)
              ·
                rfl

theorem cell20_374909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_374909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374909 prefixEnd_374909 := by exact prefixLift 374909
  have htrace : WordTrace (prefixWord ++ tailWord_374909) baseStart_374909 baseEnd_374909 := by
    simpa [prefixWord, tailWord_374909, baseEnd_374909] using wordTrace_append hprefix tailTrace_374909
  have hstable : (prefixWord ++ tailWord_374909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374909).length < 2 ^ (prefixWord ++ tailWord_374909).sum := by decide
  have hdescent : baseEnd_374909 < baseStart_374909 := by decide
  rcases family_descends (prefixWord ++ tailWord_374909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374919 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 2]
def baseStart_374919 : Nat := 118140960795 + 374919 * 2 ^ 59
def prefixEnd_374919 : Nat := 4983230072969 + 3 ^ 40 * 374919 * 2
def baseEnd_374919 : Nat := 171123247558332321234031

theorem tailTrace_374919 : CollatzResearch.WordTrace tailWord_374919 prefixEnd_374919 171123247558332321234031 := by
  unfold tailWord_374919
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674419328739968912535811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9116279552493312608357207 13674419328739968912535811)
  ·
    refine ⟨20511628993109953368803717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13674419328739968912535811 20511628993109953368803717)
    ·
      refine ⟨3845930436208116256650697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20511628993109953368803717 3845930436208116256650697)
      ·
        refine ⟨2884447827156087192488023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845930436208116256650697 2884447827156087192488023)
        ·
          refine ⟨4326671740734130788732035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884447827156087192488023 4326671740734130788732035)
          ·
            refine ⟨6490007611101196183098053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326671740734130788732035 6490007611101196183098053)
            ·
              refine ⟨1216876427081474284330885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6490007611101196183098053 1216876427081474284330885)
              ·
                refine ⟨228164330077776428312041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1216876427081474284330885 228164330077776428312041)
                ·
                  refine ⟨171123247558332321234031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228164330077776428312041 171123247558332321234031)
                  ·
                    rfl

theorem cell20_374919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 2].length) (baseStart_374919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374919 prefixEnd_374919 := by exact prefixLift 374919
  have htrace : WordTrace (prefixWord ++ tailWord_374919) baseStart_374919 baseEnd_374919 := by
    simpa [prefixWord, tailWord_374919, baseEnd_374919] using wordTrace_append hprefix tailTrace_374919
  have hstable : (prefixWord ++ tailWord_374919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374919).length < 2 ^ (prefixWord ++ tailWord_374919).sum := by decide
  have hdescent : baseEnd_374919 < baseStart_374919 := by decide
  rcases family_descends (prefixWord ++ tailWord_374919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374940 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_374940 : Nat := 118140960795 + 374940 * 2 ^ 59
def prefixEnd_374940 : Nat := 4983230072969 + 3 ^ 40 * 374940 * 2
def baseEnd_374940 : Nat := 171132832530549581533945

theorem tailTrace_374940 : CollatzResearch.WordTrace tailWord_374940 prefixEnd_374940 171132832530549581533945 := by
  unfold tailWord_374940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837592630831944749525137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9116790174442592999366849 6837592630831944749525137)
  ·
    refine ⟨5128194473123958562143853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6837592630831944749525137 5128194473123958562143853)
    ·
      refine ⟨1923072927421484460803945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5128194473123958562143853 1923072927421484460803945)
      ·
        refine ⟨1442304695566113345602959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1923072927421484460803945 1442304695566113345602959)
        ·
          refine ⟨2163457043349170018404439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442304695566113345602959 2163457043349170018404439)
          ·
            refine ⟨3245185565023755027606659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163457043349170018404439 3245185565023755027606659)
            ·
              refine ⟨4867778347535632541409989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245185565023755027606659 4867778347535632541409989)
              ·
                refine ⟨912708440162931101514373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4867778347535632541409989 912708440162931101514373)
                ·
                  refine ⟨171132832530549581533945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912708440162931101514373 171132832530549581533945)
                  ·
                    rfl

theorem cell20_374940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_374940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374940 prefixEnd_374940 := by exact prefixLift 374940
  have htrace : WordTrace (prefixWord ++ tailWord_374940) baseStart_374940 baseEnd_374940 := by
    simpa [prefixWord, tailWord_374940, baseEnd_374940] using wordTrace_append hprefix tailTrace_374940
  have hstable : (prefixWord ++ tailWord_374940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374940).length < 2 ^ (prefixWord ++ tailWord_374940).sum := by decide
  have hdescent : baseEnd_374940 < baseStart_374940 := by decide
  rcases family_descends (prefixWord ++ tailWord_374940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374943 : List Nat := [1, 1, 2, 6, 1, 3, 2, 4]
def baseStart_374943 : Nat := 118140960795 + 374943 * 2 ^ 59
def prefixEnd_374943 : Nat := 4983230072969 + 3 ^ 40 * 374943 * 2
def baseEnd_374943 : Nat := 57044733937431634811311

theorem tailTrace_374943 : CollatzResearch.WordTrace tailWord_374943 prefixEnd_374943 57044733937431634811311 := by
  unfold tailWord_374943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675294680653021011409483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9116863120435347340939655 13675294680653021011409483)
  ·
    refine ⟨20512942020979531517114225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13675294680653021011409483 20512942020979531517114225)
    ·
      refine ⟨15384706515734648637835669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20512942020979531517114225 15384706515734648637835669)
      ·
        refine ⟨721158117925061654898547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15384706515734648637835669 721158117925061654898547)
        ·
          refine ⟨1081737176887592482347821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721158117925061654898547 1081737176887592482347821)
          ·
            refine ⟨405651441332847180880433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1081737176887592482347821 405651441332847180880433)
            ·
              refine ⟨304238580999635385660325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405651441332847180880433 304238580999635385660325)
              ·
                refine ⟨57044733937431634811311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304238580999635385660325 57044733937431634811311)
                ·
                  rfl

theorem cell20_374943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_374943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374943 prefixEnd_374943 := by exact prefixLift 374943
  have htrace : WordTrace (prefixWord ++ tailWord_374943) baseStart_374943 baseEnd_374943 := by
    simpa [prefixWord, tailWord_374943, baseEnd_374943] using wordTrace_append hprefix tailTrace_374943
  have hstable : (prefixWord ++ tailWord_374943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374943).length < 2 ^ (prefixWord ++ tailWord_374943).sum := by decide
  have hdescent : baseEnd_374943 < baseStart_374943 := by decide
  rcases family_descends (prefixWord ++ tailWord_374943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374974 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_374974 : Nat := 118140960795 + 374974 * 2 ^ 59
def prefixEnd_374974 : Nat := 4983230072969 + 3 ^ 40 * 374974 * 2
def baseEnd_374974 : Nat := 171148351056996574400473

theorem tailTrace_374974 : CollatzResearch.WordTrace tailWord_374974 prefixEnd_374974 171148351056996574400473 := by
  unfold tailWord_374974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709553167942589163223497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9117616895693808870525317 1709553167942589163223497)
  ·
    refine ⟨1282164875956941872417623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1709553167942589163223497 1282164875956941872417623)
    ·
      refine ⟨1923247313935412808626435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282164875956941872417623 1923247313935412808626435)
      ·
        refine ⟨2884870970903119212939653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923247313935412808626435 2884870970903119212939653)
        ·
          refine ⟨540913307044334852426185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2884870970903119212939653 540913307044334852426185)
          ·
            refine ⟨405684980283251139319639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540913307044334852426185 405684980283251139319639)
            ·
              refine ⟨608527470424876708979459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405684980283251139319639 608527470424876708979459)
              ·
                refine ⟨912791205637315063469189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608527470424876708979459 912791205637315063469189)
                ·
                  refine ⟨171148351056996574400473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912791205637315063469189 171148351056996574400473)
                  ·
                    rfl

theorem cell20_374974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_374974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374974 prefixEnd_374974 := by exact prefixLift 374974
  have htrace : WordTrace (prefixWord ++ tailWord_374974) baseStart_374974 baseEnd_374974 := by
    simpa [prefixWord, tailWord_374974, baseEnd_374974] using wordTrace_append hprefix tailTrace_374974
  have hstable : (prefixWord ++ tailWord_374974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374974).length < 2 ^ (prefixWord ++ tailWord_374974).sum := by decide
  have hdescent : baseEnd_374974 < baseStart_374974 := by decide
  rcases family_descends (prefixWord ++ tailWord_374974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374999 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_374999 : Nat := 118140960795 + 374999 * 2 ^ 59
def prefixEnd_374999 : Nat := 4983230072969 + 3 ^ 40 * 374999 * 2
def baseEnd_374999 : Nat := 171159761738207598567037

theorem tailTrace_374999 : CollatzResearch.WordTrace tailWord_374999 prefixEnd_374999 171159761738207598567037 := by
  unfold tailWord_374999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13677337168450142575448051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9118224778966761716965367 13677337168450142575448051)
  ·
    refine ⟨20516005752675213863172077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13677337168450142575448051 20516005752675213863172077)
    ·
      refine ⟨7693502157253205198689529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20516005752675213863172077 7693502157253205198689529)
      ·
        refine ⟨5770126617939903899017147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7693502157253205198689529 5770126617939903899017147)
        ·
          refine ⟨8655189926909855848525721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770126617939903899017147 8655189926909855848525721)
          ·
            refine ⟨6491392445182391886394291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8655189926909855848525721 6491392445182391886394291)
            ·
              refine ⟨9737088667773587829591437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491392445182391886394291 9737088667773587829591437)
              ·
                refine ⟨3651408250415095436096789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9737088667773587829591437 3651408250415095436096789)
                ·
                  refine ⟨171159761738207598567037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3651408250415095436096789 171159761738207598567037)
                  ·
                    rfl

theorem cell20_374999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_374999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_374999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_374999 prefixEnd_374999 := by exact prefixLift 374999
  have htrace : WordTrace (prefixWord ++ tailWord_374999) baseStart_374999 baseEnd_374999 := by
    simpa [prefixWord, tailWord_374999, baseEnd_374999] using wordTrace_append hprefix tailTrace_374999
  have hstable : (prefixWord ++ tailWord_374999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374999).length < 2 ^ (prefixWord ++ tailWord_374999).sum := by decide
  have hdescent : baseEnd_374999 < baseStart_374999 := by decide
  rcases family_descends (prefixWord ++ tailWord_374999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375026 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_375026 : Nat := 118140960795 + 375026 * 2 ^ 59
def prefixEnd_375026 : Nat := 4983230072969 + 3 ^ 40 * 375026 * 2
def baseEnd_375026 : Nat := 171172085273915504666927

theorem tailTrace_375026 : CollatzResearch.WordTrace tailWord_375026 prefixEnd_375026 171172085273915504666927 := by
  unfold tailWord_375026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419580484838081546670233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9118881292901550791120621 3419580484838081546670233)
  ·
    refine ⟨2564685363628561160002675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3419580484838081546670233 2564685363628561160002675)
    ·
      refine ⟨3847028045442841740004013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564685363628561160002675 3847028045442841740004013)
      ·
        refine ⟨1442635517041065652501505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3847028045442841740004013 1442635517041065652501505)
        ·
          refine ⟨1081976637780799239376129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442635517041065652501505 1081976637780799239376129)
          ·
            refine ⟨811482478335599429532097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081976637780799239376129 811482478335599429532097)
            ·
              refine ⟨608611858751699572149073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811482478335599429532097 608611858751699572149073)
              ·
                refine ⟨456458894063774679111805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608611858751699572149073 456458894063774679111805)
                ·
                  refine ⟨171172085273915504666927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456458894063774679111805 171172085273915504666927)
                  ·
                    rfl

theorem cell20_375026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_375026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375026 prefixEnd_375026 := by exact prefixLift 375026
  have htrace : WordTrace (prefixWord ++ tailWord_375026) baseStart_375026 baseEnd_375026 := by
    simpa [prefixWord, tailWord_375026, baseEnd_375026] using wordTrace_append hprefix tailTrace_375026
  have hstable : (prefixWord ++ tailWord_375026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375026).length < 2 ^ (prefixWord ++ tailWord_375026).sum := by decide
  have hdescent : baseEnd_375026 < baseStart_375026 := by decide
  rcases family_descends (prefixWord ++ tailWord_375026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375037 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_375037 : Nat := 118140960795 + 375037 * 2 ^ 59
def prefixEnd_375037 : Nat := 4983230072969 + 3 ^ 40 * 375037 * 2
def baseEnd_375037 : Nat := 171177105973648355300215

theorem tailTrace_375037 : CollatzResearch.WordTrace tailWord_375037 prefixEnd_375037 171177105973648355300215 := by
  unfold tailWord_375037
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678723142312475065331365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9119148761541650043554243 13678723142312475065331365)
  ·
    refine ⟨2564760589183589074749631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13678723142312475065331365 2564760589183589074749631)
    ·
      refine ⟨3847140883775383612124447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564760589183589074749631 3847140883775383612124447)
      ·
        refine ⟨5770711325663075418186671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847140883775383612124447 5770711325663075418186671)
        ·
          refine ⟨8656066988494613127280007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770711325663075418186671 8656066988494613127280007)
          ·
            refine ⟨12984100482741919690920011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656066988494613127280007 12984100482741919690920011)
            ·
              refine ⟨19476150724112879536380017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12984100482741919690920011 19476150724112879536380017)
              ·
                refine ⟨14607113043084659652285013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19476150724112879536380017 14607113043084659652285013)
                ·
                  refine ⟨171177105973648355300215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14607113043084659652285013 171177105973648355300215)
                  ·
                    rfl

theorem cell20_375037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_375037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375037 prefixEnd_375037 := by exact prefixLift 375037
  have htrace : WordTrace (prefixWord ++ tailWord_375037) baseStart_375037 baseEnd_375037 := by
    simpa [prefixWord, tailWord_375037, baseEnd_375037] using wordTrace_append hprefix tailTrace_375037
  have hstable : (prefixWord ++ tailWord_375037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375037).length < 2 ^ (prefixWord ++ tailWord_375037).sum := by decide
  have hdescent : baseEnd_375037 < baseStart_375037 := by decide
  rcases family_descends (prefixWord ++ tailWord_375037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375054 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_375054 : Nat := 118140960795 + 375054 * 2 ^ 59
def prefixEnd_375054 : Nat := 4983230072969 + 3 ^ 40 * 375054 * 2
def baseEnd_375054 : Nat := 171184865236871851733479

theorem tailTrace_375054 : CollatzResearch.WordTrace tailWord_375054 prefixEnd_375054 171184865236871851733479 := by
  unfold tailWord_375054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709917897906360871087527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9119562122167257979133477 1709917897906360871087527)
  ·
    refine ⟨2564876846859541306631291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1709917897906360871087527 2564876846859541306631291)
    ·
      refine ⟨3847315270289311959946937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564876846859541306631291 3847315270289311959946937)
      ·
        refine ⟨2885486452716983969960203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3847315270289311959946937 2885486452716983969960203)
        ·
          refine ⟨4328229679075475954940305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885486452716983969960203 4328229679075475954940305)
          ·
            refine ⟨3246172259306606966205229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4328229679075475954940305 3246172259306606966205229)
            ·
              refine ⟨1217314597239977612326961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3246172259306606966205229 1217314597239977612326961)
              ·
                refine ⟨912985947929983209245221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217314597239977612326961 912985947929983209245221)
                ·
                  refine ⟨171184865236871851733479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912985947929983209245221 171184865236871851733479)
                  ·
                    rfl

theorem cell20_375054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_375054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375054 prefixEnd_375054 := by exact prefixLift 375054
  have htrace : WordTrace (prefixWord ++ tailWord_375054) baseStart_375054 baseEnd_375054 := by
    simpa [prefixWord, tailWord_375054, baseEnd_375054] using wordTrace_append hprefix tailTrace_375054
  have hstable : (prefixWord ++ tailWord_375054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375054).length < 2 ^ (prefixWord ++ tailWord_375054).sum := by decide
  have hdescent : baseEnd_375054 < baseStart_375054 := by decide
  rcases family_descends (prefixWord ++ tailWord_375054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375068 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_375068 : Nat := 118140960795 + 375068 * 2 ^ 59
def prefixEnd_375068 : Nat := 4983230072969 + 3 ^ 40 * 375068 * 2
def baseEnd_375068 : Nat := 171191255218350025266755

theorem tailTrace_375068 : CollatzResearch.WordTrace tailWord_375068 prefixEnd_375068 171191255218350025266755 := by
  unfold tailWord_375068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839926902600083679854929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9119902536800111573139905 6839926902600083679854929)
  ·
    refine ⟨5129945176950062759891197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6839926902600083679854929 5129945176950062759891197)
    ·
      refine ⟨1923729441356273534959199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5129945176950062759891197 1923729441356273534959199)
      ·
        refine ⟨2885594162034410302438799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923729441356273534959199 2885594162034410302438799)
        ·
          refine ⟨4328391243051615453658199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885594162034410302438799 4328391243051615453658199)
          ·
            refine ⟨6492586864577423180487299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328391243051615453658199 6492586864577423180487299)
            ·
              refine ⟨9738880296866134770730949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492586864577423180487299 9738880296866134770730949)
              ·
                refine ⟨1826040055662400269512053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9738880296866134770730949 1826040055662400269512053)
                ·
                  refine ⟨171191255218350025266755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1826040055662400269512053 171191255218350025266755)
                  ·
                    rfl

theorem cell20_375068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_375068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375068 prefixEnd_375068 := by exact prefixLift 375068
  have htrace : WordTrace (prefixWord ++ tailWord_375068) baseStart_375068 baseEnd_375068 := by
    simpa [prefixWord, tailWord_375068, baseEnd_375068] using wordTrace_append hprefix tailTrace_375068
  have hstable : (prefixWord ++ tailWord_375068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375068).length < 2 ^ (prefixWord ++ tailWord_375068).sum := by decide
  have hdescent : baseEnd_375068 < baseStart_375068 := by decide
  rcases family_descends (prefixWord ++ tailWord_375068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375071 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 2]
def baseStart_375071 : Nat := 118140960795 + 375071 * 2 ^ 59
def prefixEnd_375071 : Nat := 4983230072969 + 3 ^ 40 * 375071 * 2
def baseEnd_375071 : Nat := 171192624500095348166743

theorem tailTrace_375071 : CollatzResearch.WordTrace tailWord_375071 prefixEnd_375071 171192624500095348166743 := by
  unfold tailWord_375071
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679963224189298872069067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9119975482792865914712711 13679963224189298872069067)
  ·
    refine ⟨20519944836283948308103601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13679963224189298872069067 20519944836283948308103601)
    ·
      refine ⟨15389958627212961231077701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20519944836283948308103601 15389958627212961231077701)
      ·
        refine ⟨2885617242602430230827069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15389958627212961231077701 2885617242602430230827069)
        ·
          refine ⟨1082106465975911336560151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2885617242602430230827069 1082106465975911336560151)
          ·
            refine ⟨1623159698963867004840227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082106465975911336560151 1623159698963867004840227)
            ·
              refine ⟨2434739548445800507260341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623159698963867004840227 2434739548445800507260341)
              ·
                refine ⟨228256832666793797555657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2434739548445800507260341 228256832666793797555657)
                ·
                  refine ⟨171192624500095348166743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228256832666793797555657 171192624500095348166743)
                  ·
                    rfl

theorem cell20_375071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 2].length) (baseStart_375071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375071 prefixEnd_375071 := by exact prefixLift 375071
  have htrace : WordTrace (prefixWord ++ tailWord_375071) baseStart_375071 baseEnd_375071 := by
    simpa [prefixWord, tailWord_375071, baseEnd_375071] using wordTrace_append hprefix tailTrace_375071
  have hstable : (prefixWord ++ tailWord_375071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375071).length < 2 ^ (prefixWord ++ tailWord_375071).sum := by decide
  have hdescent : baseEnd_375071 < baseStart_375071 := by decide
  rcases family_descends (prefixWord ++ tailWord_375071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375075 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_375075 : Nat := 118140960795 + 375075 * 2 ^ 59
def prefixEnd_375075 : Nat := 4983230072969 + 3 ^ 40 * 375075 * 2
def baseEnd_375075 : Nat := 171194450209089112033393

theorem tailTrace_375075 : CollatzResearch.WordTrace tailWord_375075 prefixEnd_375075 171194450209089112033393 := by
  unfold tailWord_375075
  simp only [CollatzResearch.WordTrace]
  refine ⟨13680109116174807555214679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9120072744116538370143119 13680109116174807555214679)
  ·
    refine ⟨20520163674262211332822019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13680109116174807555214679 20520163674262211332822019)
    ·
      refine ⟨30780245511393316999233029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20520163674262211332822019 30780245511393316999233029)
      ·
        refine ⟨5771296033386246937356193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30780245511393316999233029 5771296033386246937356193)
        ·
          refine ⟨4328472025039685203017145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771296033386246937356193 4328472025039685203017145)
          ·
            refine ⟨3246354018779763902262859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4328472025039685203017145 3246354018779763902262859)
            ·
              refine ⟨4869531028169645853394289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246354018779763902262859 4869531028169645853394289)
              ·
                refine ⟨3652148271127234390045717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869531028169645853394289 3652148271127234390045717)
                ·
                  refine ⟨171194450209089112033393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3652148271127234390045717 171194450209089112033393)
                  ·
                    rfl

theorem cell20_375075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_375075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375075 prefixEnd_375075 := by exact prefixLift 375075
  have htrace : WordTrace (prefixWord ++ tailWord_375075) baseStart_375075 baseEnd_375075 := by
    simpa [prefixWord, tailWord_375075, baseEnd_375075] using wordTrace_append hprefix tailTrace_375075
  have hstable : (prefixWord ++ tailWord_375075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375075).length < 2 ^ (prefixWord ++ tailWord_375075).sum := by decide
  have hdescent : baseEnd_375075 < baseStart_375075 := by decide
  rcases family_descends (prefixWord ++ tailWord_375075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375151 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_375151 : Nat := 118140960795 + 375151 * 2 ^ 59
def prefixEnd_375151 : Nat := 4983230072969 + 3 ^ 40 * 375151 * 2
def baseEnd_375151 : Nat := 171229138679970625499749

theorem tailTrace_375151 : CollatzResearch.WordTrace tailWord_375151 prefixEnd_375151 171229138679970625499749 := by
  unfold tailWord_375151
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682881063899472534981307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9121920709266315023320871 13682881063899472534981307)
  ·
    refine ⟨20524321595849208802471961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13682881063899472534981307 20524321595849208802471961)
    ·
      refine ⟨15393241196886906601853971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20524321595849208802471961 15393241196886906601853971)
      ·
        refine ⟨23089861795330359902780957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393241196886906601853971 23089861795330359902780957)
        ·
          refine ⟨8658698173248884963542859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23089861795330359902780957 8658698173248884963542859)
          ·
            refine ⟨12988047259873327445314289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658698173248884963542859 12988047259873327445314289)
            ·
              refine ⟨9741035444904995583985717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12988047259873327445314289 9741035444904995583985717)
              ·
                refine ⟨913222072959843335998661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9741035444904995583985717 913222072959843335998661)
                ·
                  refine ⟨171229138679970625499749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913222072959843335998661 171229138679970625499749)
                  ·
                    rfl

theorem cell20_375151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_375151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375151 prefixEnd_375151 := by exact prefixLift 375151
  have htrace : WordTrace (prefixWord ++ tailWord_375151) baseStart_375151 baseEnd_375151 := by
    simpa [prefixWord, tailWord_375151, baseEnd_375151] using wordTrace_append hprefix tailTrace_375151
  have hstable : (prefixWord ++ tailWord_375151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375151).length < 2 ^ (prefixWord ++ tailWord_375151).sum := by decide
  have hdescent : baseEnd_375151 < baseStart_375151 := by decide
  rcases family_descends (prefixWord ++ tailWord_375151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375157 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 3]
def baseStart_375157 : Nat := 118140960795 + 375157 * 2 ^ 59
def prefixEnd_375157 : Nat := 4983230072969 + 3 ^ 40 * 375157 * 2
def baseEnd_375157 : Nat := 171231877243461271299725

theorem tailTrace_375157 : CollatzResearch.WordTrace tailWord_375157 prefixEnd_375157 171231877243461271299725 := by
  unfold tailWord_375157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683099901877735559699725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9122066601251823706466483 13683099901877735559699725)
  ·
    refine ⟨5131162463204150834887397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13683099901877735559699725 5131162463204150834887397)
    ·
      refine ⟨962092961850778281541387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5131162463204150834887397 962092961850778281541387)
      ·
        refine ⟨1443139442776167422312081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962092961850778281541387 1443139442776167422312081)
        ·
          refine ⟨1082354582082125566734061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1443139442776167422312081 1082354582082125566734061)
          ·
            refine ⟨405882968280797087525273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1082354582082125566734061 405882968280797087525273)
            ·
              refine ⟨304412226210597815643955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405882968280797087525273 304412226210597815643955)
              ·
                refine ⟨456618339315896723465933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304412226210597815643955 456618339315896723465933)
                ·
                  refine ⟨171231877243461271299725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456618339315896723465933 171231877243461271299725)
                  ·
                    rfl

theorem cell20_375157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_375157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375157 prefixEnd_375157 := by exact prefixLift 375157
  have htrace : WordTrace (prefixWord ++ tailWord_375157) baseStart_375157 baseEnd_375157 := by
    simpa [prefixWord, tailWord_375157, baseEnd_375157] using wordTrace_append hprefix tailTrace_375157
  have hstable : (prefixWord ++ tailWord_375157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375157).length < 2 ^ (prefixWord ++ tailWord_375157).sum := by decide
  have hdescent : baseEnd_375157 < baseStart_375157 := by decide
  rcases family_descends (prefixWord ++ tailWord_375157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375196 : List Nat := [2, 2, 3, 13]
def baseStart_375196 : Nat := 118140960795 + 375196 * 2 ^ 59
def prefixEnd_375196 : Nat := 4983230072969 + 3 ^ 40 * 375196 * 2
def baseEnd_375196 : Nat := 704731184798973123455

theorem tailTrace_375196 : CollatzResearch.WordTrace tailWord_375196 prefixEnd_375196 704731184798973123455 := by
  unfold tailWord_375196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842261174368222610184721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9123014899157630146912961 6842261174368222610184721)
  ·
    refine ⟨5131695880776166957638541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6842261174368222610184721 5131695880776166957638541)
    ·
      refine ⟨1924385955291062609114453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5131695880776166957638541 1924385955291062609114453)
      ·
        refine ⟨704731184798973123455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1924385955291062609114453 704731184798973123455)
        ·
          rfl

theorem cell20_375196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 13].length) (baseStart_375196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375196 prefixEnd_375196 := by exact prefixLift 375196
  have htrace : WordTrace (prefixWord ++ tailWord_375196) baseStart_375196 baseEnd_375196 := by
    simpa [prefixWord, tailWord_375196, baseEnd_375196] using wordTrace_append hprefix tailTrace_375196
  have hstable : (prefixWord ++ tailWord_375196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375196).length < 2 ^ (prefixWord ++ tailWord_375196).sum := by decide
  have hdescent : baseEnd_375196 < baseStart_375196 := by decide
  rcases family_descends (prefixWord ++ tailWord_375196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375198 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_375198 : Nat := 118140960795 + 375198 * 2 ^ 59
def prefixEnd_375198 : Nat := 4983230072969 + 3 ^ 40 * 375198 * 2
def baseEnd_375198 : Nat := 171250590760647350932891

theorem tailTrace_375198 : CollatzResearch.WordTrace tailWord_375198 prefixEnd_375198 171250590760647350932891 := by
  unfold tailWord_375198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1710574411841149945242781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9123063529819466374628165 1710574411841149945242781)
  ·
    refine ⟨641465404440431229466043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1710574411841149945242781 641465404440431229466043)
    ·
      refine ⟨962198106660646844199065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641465404440431229466043 962198106660646844199065)
      ·
        refine ⟨721648579995485133149299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962198106660646844199065 721648579995485133149299)
        ·
          refine ⟨1082472869993227699723949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721648579995485133149299 1082472869993227699723949)
          ·
            refine ⟨405927326247460387396481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1082472869993227699723949 405927326247460387396481)
            ·
              refine ⟨304445494685595290547361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405927326247460387396481 304445494685595290547361)
              ·
                refine ⟨228334121014196467910521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304445494685595290547361 228334121014196467910521)
                ·
                  refine ⟨171250590760647350932891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228334121014196467910521 171250590760647350932891)
                  ·
                    rfl

theorem cell20_375198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_375198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375198 prefixEnd_375198 := by exact prefixLift 375198
  have htrace : WordTrace (prefixWord ++ tailWord_375198) baseStart_375198 baseEnd_375198 := by
    simpa [prefixWord, tailWord_375198, baseEnd_375198] using wordTrace_append hprefix tailTrace_375198
  have hstable : (prefixWord ++ tailWord_375198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375198).length < 2 ^ (prefixWord ++ tailWord_375198).sum := by decide
  have hdescent : baseEnd_375198 < baseStart_375198 := by decide
  rcases family_descends (prefixWord ++ tailWord_375198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375199 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_375199 : Nat := 118140960795 + 375199 * 2 ^ 59
def prefixEnd_375199 : Nat := 4983230072969 + 3 ^ 40 * 375199 * 2
def baseEnd_375199 : Nat := 171251047187895791899553

theorem tailTrace_375199 : CollatzResearch.WordTrace tailWord_375199 prefixEnd_375199 171251047187895791899553 := by
  unfold tailWord_375199
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684631767725576732728651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9123087845150384488485767 13684631767725576732728651)
  ·
    refine ⟨20526947651588365099092977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13684631767725576732728651 20526947651588365099092977)
    ·
      refine ⟨15395210738691273824319733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20526947651588365099092977 15395210738691273824319733)
      ·
        refine ⟨1443301006752306921029975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15395210738691273824319733 1443301006752306921029975)
        ·
          refine ⟨2164951510128460381544963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443301006752306921029975 2164951510128460381544963)
          ·
            refine ⟨3247427265192690572317445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164951510128460381544963 3247427265192690572317445)
            ·
              refine ⟨608892612223629482309521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3247427265192690572317445 608892612223629482309521)
              ·
                refine ⟨456669459167722111732141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608892612223629482309521 456669459167722111732141)
                ·
                  refine ⟨171251047187895791899553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456669459167722111732141 171251047187895791899553)
                  ·
                    rfl

theorem cell20_375199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_375199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375199 prefixEnd_375199 := by exact prefixLift 375199
  have htrace : WordTrace (prefixWord ++ tailWord_375199) baseStart_375199 baseEnd_375199 := by
    simpa [prefixWord, tailWord_375199, baseEnd_375199] using wordTrace_append hprefix tailTrace_375199
  have hstable : (prefixWord ++ tailWord_375199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375199).length < 2 ^ (prefixWord ++ tailWord_375199).sum := by decide
  have hdescent : baseEnd_375199 < baseStart_375199 := by decide
  rcases family_descends (prefixWord ++ tailWord_375199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375250 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_375250 : Nat := 118140960795 + 375250 * 2 ^ 59
def prefixEnd_375250 : Nat := 4983230072969 + 3 ^ 40 * 375250 * 2
def baseEnd_375250 : Nat := 171274324977566281199345

theorem tailTrace_375250 : CollatzResearch.WordTrace tailWord_375250 prefixEnd_375250 171274324977566281199345 := by
  unfold tailWord_375250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3421622972635203110708801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9124327927027208295223469 3421622972635203110708801)
  ·
    refine ⟨2566217229476402333031601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3421622972635203110708801 2566217229476402333031601)
    ·
      refine ⟨1924662922107301749773701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2566217229476402333031601 1924662922107301749773701)
      ·
        refine ⟨360874297895119078082569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1924662922107301749773701 360874297895119078082569)
        ·
          refine ⟨270655723421339308561927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360874297895119078082569 270655723421339308561927)
          ·
            refine ⟨405983585132008962842891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270655723421339308561927 405983585132008962842891)
            ·
              refine ⟨608975377698013444264337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405983585132008962842891 608975377698013444264337)
              ·
                refine ⟨456731533273510083198253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608975377698013444264337 456731533273510083198253)
                ·
                  refine ⟨171274324977566281199345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456731533273510083198253 171274324977566281199345)
                  ·
                    rfl

theorem cell20_375250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_375250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375250 prefixEnd_375250 := by exact prefixLift 375250
  have htrace : WordTrace (prefixWord ++ tailWord_375250) baseStart_375250 baseEnd_375250 := by
    simpa [prefixWord, tailWord_375250, baseEnd_375250] using wordTrace_append hprefix tailTrace_375250
  have hstable : (prefixWord ++ tailWord_375250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375250).length < 2 ^ (prefixWord ++ tailWord_375250).sum := by decide
  have hdescent : baseEnd_375250 < baseStart_375250 := by decide
  rcases family_descends (prefixWord ++ tailWord_375250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375258 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_375258 : Nat := 118140960795 + 375258 * 2 ^ 59
def prefixEnd_375258 : Nat := 4983230072969 + 3 ^ 40 * 375258 * 2
def baseEnd_375258 : Nat := 171277976395553808932645

theorem tailTrace_375258 : CollatzResearch.WordTrace tailWord_375258 prefixEnd_375258 171277976395553808932645 := by
  unfold tailWord_375258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3421695918627957452281607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9124522449674553206084285 3421695918627957452281607)
  ·
    refine ⟨5132543877941936178422411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3421695918627957452281607 5132543877941936178422411)
    ·
      refine ⟨7698815816912904267633617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132543877941936178422411 7698815816912904267633617)
      ·
        refine ⟨5774111862684678200725213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7698815816912904267633617 5774111862684678200725213)
        ·
          refine ⟨2165291948506754325271955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5774111862684678200725213 2165291948506754325271955)
          ·
            refine ⟨3247937922760131487907933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165291948506754325271955 3247937922760131487907933)
            ·
              refine ⟨1217976721035049307965475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3247937922760131487907933 1217976721035049307965475)
              ·
                refine ⟨1826965081552573961948213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217976721035049307965475 1826965081552573961948213)
                ·
                  refine ⟨171277976395553808932645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1826965081552573961948213 171277976395553808932645)
                  ·
                    rfl

theorem cell20_375258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_375258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375258 prefixEnd_375258 := by exact prefixLift 375258
  have htrace : WordTrace (prefixWord ++ tailWord_375258) baseStart_375258 baseEnd_375258 := by
    simpa [prefixWord, tailWord_375258, baseEnd_375258] using wordTrace_append hprefix tailTrace_375258
  have hstable : (prefixWord ++ tailWord_375258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375258).length < 2 ^ (prefixWord ++ tailWord_375258).sum := by decide
  have hdescent : baseEnd_375258 < baseStart_375258 := by decide
  rcases family_descends (prefixWord ++ tailWord_375258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375261 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 2]
def baseStart_375261 : Nat := 118140960795 + 375261 * 2 ^ 59
def prefixEnd_375261 : Nat := 4983230072969 + 3 ^ 40 * 375261 * 2
def baseEnd_375261 : Nat := 171279345677299131832633

theorem tailTrace_375261 : CollatzResearch.WordTrace tailWord_375261 prefixEnd_375261 171279345677299131832633 := by
  unfold tailWord_375261
  simp only [CollatzResearch.WordTrace]
  refine ⟨13686893093500961321485637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9124595395667307547657091 13686893093500961321485637)
  ·
    refine ⟨2566292455031430247778557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13686893093500961321485637 2566292455031430247778557)
    ·
      refine ⟨962359670636786342916959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2566292455031430247778557 962359670636786342916959)
      ·
        refine ⟨1443539505955179514375439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962359670636786342916959 1443539505955179514375439)
        ·
          refine ⟨2165309258932769271563159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443539505955179514375439 2165309258932769271563159)
          ·
            refine ⟨3247963888399153907344739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165309258932769271563159 3247963888399153907344739)
            ·
              refine ⟨4871945832598730861017109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247963888399153907344739 4871945832598730861017109)
              ·
                refine ⟨228372460903065509110177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4871945832598730861017109 228372460903065509110177)
                ·
                  refine ⟨171279345677299131832633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228372460903065509110177 171279345677299131832633)
                  ·
                    rfl

theorem cell20_375261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_375261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375261 prefixEnd_375261 := by exact prefixLift 375261
  have htrace : WordTrace (prefixWord ++ tailWord_375261) baseStart_375261 baseEnd_375261 := by
    simpa [prefixWord, tailWord_375261, baseEnd_375261] using wordTrace_append hprefix tailTrace_375261
  have hstable : (prefixWord ++ tailWord_375261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375261).length < 2 ^ (prefixWord ++ tailWord_375261).sum := by decide
  have hdescent : baseEnd_375261 < baseStart_375261 := by decide
  rcases family_descends (prefixWord ++ tailWord_375261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375275 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 3]
def baseStart_375275 : Nat := 118140960795 + 375275 * 2 ^ 59
def prefixEnd_375275 : Nat := 4983230072969 + 3 ^ 40 * 375275 * 2
def baseEnd_375275 : Nat := 171285735658777305365909

theorem tailTrace_375275 : CollatzResearch.WordTrace tailWord_375275 prefixEnd_375275 171285735658777305365909 := by
  unfold tailWord_375275
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687403715450241712495279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9124935810300161141663519 13687403715450241712495279)
  ·
    refine ⟨20531105573175362568742919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13687403715450241712495279 20531105573175362568742919)
    ·
      refine ⟨30796658359763043853114379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20531105573175362568742919 30796658359763043853114379)
      ·
        refine ⟨46194987539644565779671569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30796658359763043853114379 46194987539644565779671569)
        ·
          refine ⟨34646240654733424334753677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46194987539644565779671569 34646240654733424334753677)
          ·
            refine ⟨12992340245525034125532629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34646240654733424334753677 12992340245525034125532629)
            ·
              refine ⟨304507974504492987317171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12992340245525034125532629 304507974504492987317171)
              ·
                refine ⟨456761961756739480975757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304507974504492987317171 456761961756739480975757)
                ·
                  refine ⟨171285735658777305365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456761961756739480975757 171285735658777305365909)
                  ·
                    rfl

theorem cell20_375275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_375275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375275 prefixEnd_375275 := by exact prefixLift 375275
  have htrace : WordTrace (prefixWord ++ tailWord_375275) baseStart_375275 baseEnd_375275 := by
    simpa [prefixWord, tailWord_375275, baseEnd_375275] using wordTrace_append hprefix tailTrace_375275
  have hstable : (prefixWord ++ tailWord_375275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375275).length < 2 ^ (prefixWord ++ tailWord_375275).sum := by decide
  have hdescent : baseEnd_375275 < baseStart_375275 := by decide
  rcases family_descends (prefixWord ++ tailWord_375275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375289 : List Nat := [1, 2, 1, 3, 1, 2, 6, 4]
def baseStart_375289 : Nat := 118140960795 + 375289 * 2 ^ 59
def prefixEnd_375289 : Nat := 4983230072969 + 3 ^ 40 * 375289 * 2
def baseEnd_375289 : Nat := 57097375213418492966395

theorem tailTrace_375289 : CollatzResearch.WordTrace tailWord_375289 prefixEnd_375289 57097375213418492966395 := by
  unfold tailWord_375289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687914337399522103504921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9125276224933014735669947 13687914337399522103504921)
  ·
    refine ⟨10265935753049641577628691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13687914337399522103504921 10265935753049641577628691)
    ·
      refine ⟨15398903629574462366443037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10265935753049641577628691 15398903629574462366443037)
      ·
        refine ⟨5774588861090423387416139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15398903629574462366443037 5774588861090423387416139)
        ·
          refine ⟨8661883291635635081124209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774588861090423387416139 8661883291635635081124209)
          ·
            refine ⟨6496412468726726310843157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8661883291635635081124209 6496412468726726310843157)
            ·
              refine ⟨304519334471565295820773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6496412468726726310843157 304519334471565295820773)
              ·
                refine ⟨57097375213418492966395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304519334471565295820773 57097375213418492966395)
                ·
                  rfl

theorem cell20_375289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_375289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375289 prefixEnd_375289 := by exact prefixLift 375289
  have htrace : WordTrace (prefixWord ++ tailWord_375289) baseStart_375289 baseEnd_375289 := by
    simpa [prefixWord, tailWord_375289, baseEnd_375289] using wordTrace_append hprefix tailTrace_375289
  have hstable : (prefixWord ++ tailWord_375289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375289).length < 2 ^ (prefixWord ++ tailWord_375289).sum := by decide
  have hdescent : baseEnd_375289 < baseStart_375289 := by decide
  rcases family_descends (prefixWord ++ tailWord_375289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375302 : List Nat := [6, 2, 1, 1, 1, 3, 6]
def baseStart_375302 : Nat := 118140960795 + 375302 * 2 ^ 59
def prefixEnd_375302 : Nat := 4983230072969 + 3 ^ 40 * 375302 * 2
def baseEnd_375302 : Nat := 19033117688276134607311

theorem tailTrace_375302 : CollatzResearch.WordTrace tailWord_375302 prefixEnd_375302 19033117688276134607311 := by
  unfold tailWord_375302
  simp only [CollatzResearch.WordTrace]
  refine ⟨427762140198513291366505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9125592324234950215818773 427762140198513291366505)
  ·
    refine ⟨320821605148884968524879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 427762140198513291366505 320821605148884968524879)
    ·
      refine ⟨481232407723327452787319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320821605148884968524879 481232407723327452787319)
      ·
        refine ⟨721848611584991179180979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481232407723327452787319 721848611584991179180979)
        ·
          refine ⟨1082772917377486768771469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721848611584991179180979 1082772917377486768771469)
          ·
            refine ⟨406039844016557538289301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1082772917377486768771469 406039844016557538289301)
            ·
              refine ⟨19033117688276134607311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 406039844016557538289301 19033117688276134607311)
              ·
                rfl

theorem cell20_375302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 6].length) (baseStart_375302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375302 prefixEnd_375302 := by exact prefixLift 375302
  have htrace : WordTrace (prefixWord ++ tailWord_375302) baseStart_375302 baseEnd_375302 := by
    simpa [prefixWord, tailWord_375302, baseEnd_375302] using wordTrace_append hprefix tailTrace_375302
  have hstable : (prefixWord ++ tailWord_375302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375302).length < 2 ^ (prefixWord ++ tailWord_375302).sum := by decide
  have hdescent : baseEnd_375302 < baseStart_375302 := by decide
  rcases family_descends (prefixWord ++ tailWord_375302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375316 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_375316 : Nat := 118140960795 + 375316 * 2 ^ 59
def prefixEnd_375316 : Nat := 4983230072969 + 3 ^ 40 * 375316 * 2
def baseEnd_375316 : Nat := 171304449175963384999075

theorem tailTrace_375316 : CollatzResearch.WordTrace tailWord_375316 prefixEnd_375316 171304449175963384999075 := by
  unfold tailWord_375316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844449554150852857368901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9125932738867803809825201 6844449554150852857368901)
  ·
    refine ⟨1283334291403284910756669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6844449554150852857368901 1283334291403284910756669)
    ·
      refine ⟨481250359276231841533751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1283334291403284910756669 481250359276231841533751)
      ·
        refine ⟨721875538914347762300627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481250359276231841533751 721875538914347762300627)
        ·
          refine ⟨1082813308371521643450941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721875538914347762300627 1082813308371521643450941)
          ·
            refine ⟨406054990639320616294103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1082813308371521643450941 406054990639320616294103)
            ·
              refine ⟨609082485958980924441155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406054990639320616294103 609082485958980924441155)
              ·
                refine ⟨913623728938471386661733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609082485958980924441155 913623728938471386661733)
                ·
                  refine ⟨171304449175963384999075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913623728938471386661733 171304449175963384999075)
                  ·
                    rfl

theorem cell20_375316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_375316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375316 prefixEnd_375316 := by exact prefixLift 375316
  have htrace : WordTrace (prefixWord ++ tailWord_375316) baseStart_375316 baseEnd_375316 := by
    simpa [prefixWord, tailWord_375316, baseEnd_375316] using wordTrace_append hprefix tailTrace_375316
  have hstable : (prefixWord ++ tailWord_375316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375316).length < 2 ^ (prefixWord ++ tailWord_375316).sum := by decide
  have hdescent : baseEnd_375316 < baseStart_375316 := by decide
  rcases family_descends (prefixWord ++ tailWord_375316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375320 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_375320 : Nat := 118140960795 + 375320 * 2 ^ 59
def prefixEnd_375320 : Nat := 4983230072969 + 3 ^ 40 * 375320 * 2
def baseEnd_375320 : Nat := 171306274884957148865725

theorem tailTrace_375320 : CollatzResearch.WordTrace tailWord_375320 prefixEnd_375320 171306274884957148865725 := by
  unfold tailWord_375320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844522500143607198941707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9126030000191476265255609 6844522500143607198941707)
  ·
    refine ⟨10266783750215410798412561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6844522500143607198941707 10266783750215410798412561)
    ·
      refine ⟨7700087812661558098809421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266783750215410798412561 7700087812661558098809421)
      ·
        refine ⟨2887532929748084287053533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7700087812661558098809421 2887532929748084287053533)
        ·
          refine ⟨1082824848655531607645075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2887532929748084287053533 1082824848655531607645075)
          ·
            refine ⟨1624237272983297411467613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082824848655531607645075 1624237272983297411467613)
            ·
              refine ⟨609088977368736529300355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1624237272983297411467613 609088977368736529300355)
              ·
                refine ⟨913633466053104793950533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609088977368736529300355 913633466053104793950533)
                ·
                  refine ⟨171306274884957148865725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913633466053104793950533 171306274884957148865725)
                  ·
                    rfl

theorem cell20_375320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_375320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375320 prefixEnd_375320 := by exact prefixLift 375320
  have htrace : WordTrace (prefixWord ++ tailWord_375320) baseStart_375320 baseEnd_375320 := by
    simpa [prefixWord, tailWord_375320, baseEnd_375320] using wordTrace_append hprefix tailTrace_375320
  have hstable : (prefixWord ++ tailWord_375320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375320).length < 2 ^ (prefixWord ++ tailWord_375320).sum := by decide
  have hdescent : baseEnd_375320 < baseStart_375320 := by decide
  rcases family_descends (prefixWord ++ tailWord_375320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375364 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 3]
def baseStart_375364 : Nat := 118140960795 + 375364 * 2 ^ 59
def prefixEnd_375364 : Nat := 4983230072969 + 3 ^ 40 * 375364 * 2
def baseEnd_375364 : Nat := 171326357683888551398879

theorem tailTrace_375364 : CollatzResearch.WordTrace tailWord_375364 prefixEnd_375364 171326357683888551398879 := by
  unfold tailWord_375364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845324906063904956242573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9127099874751873274990097 6845324906063904956242573)
  ·
    refine ⟨2566996839773964358590965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6845324906063904956242573 2566996839773964358590965)
    ·
      refine ⟨240655953728809158617903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2566996839773964358590965 240655953728809158617903)
      ·
        refine ⟨360983930593213737926855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240655953728809158617903 360983930593213737926855)
        ·
          refine ⟨541475895889820606890283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360983930593213737926855 541475895889820606890283)
          ·
            refine ⟨812213843834730910335425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541475895889820606890283 812213843834730910335425)
            ·
              refine ⟨609160382876048182751569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812213843834730910335425 609160382876048182751569)
              ·
                refine ⟨456870287157036137063677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609160382876048182751569 456870287157036137063677)
                ·
                  refine ⟨171326357683888551398879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456870287157036137063677 171326357683888551398879)
                  ·
                    rfl

theorem cell20_375364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_375364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375364 prefixEnd_375364 := by exact prefixLift 375364
  have htrace : WordTrace (prefixWord ++ tailWord_375364) baseStart_375364 baseEnd_375364 := by
    simpa [prefixWord, tailWord_375364, baseEnd_375364] using wordTrace_append hprefix tailTrace_375364
  have hstable : (prefixWord ++ tailWord_375364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375364).length < 2 ^ (prefixWord ++ tailWord_375364).sum := by decide
  have hdescent : baseEnd_375364 < baseStart_375364 := by decide
  rcases family_descends (prefixWord ++ tailWord_375364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375375 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 2]
def baseStart_375375 : Nat := 118140960795 + 375375 * 2 ^ 59
def prefixEnd_375375 : Nat := 4983230072969 + 3 ^ 40 * 375375 * 2
def baseEnd_375375 : Nat := 171331378383621402032167

theorem tailTrace_375375 : CollatzResearch.WordTrace tailWord_375375 prefixEnd_375375 171331378383621402032167 := by
  unfold tailWord_375375
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691051015087958791135579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9127367343391972527423719 13691051015087958791135579)
  ·
    refine ⟨20536576522631938186703369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13691051015087958791135579 20536576522631938186703369)
    ·
      refine ⟨15402432391973953640027527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20536576522631938186703369 15402432391973953640027527)
      ·
        refine ⟨23103648587960930460041291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15402432391973953640027527 23103648587960930460041291)
        ·
          refine ⟨34655472881941395690061937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23103648587960930460041291 34655472881941395690061937)
          ·
            refine ⟨25991604661456046767546453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34655472881941395690061937 25991604661456046767546453)
            ·
              refine ⟨304589117126438048057185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 25991604661456046767546453 304589117126438048057185)
              ·
                refine ⟨228441837844828536042889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304589117126438048057185 228441837844828536042889)
                ·
                  refine ⟨171331378383621402032167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228441837844828536042889 171331378383621402032167)
                  ·
                    rfl

theorem cell20_375375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 2].length) (baseStart_375375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375375 prefixEnd_375375 := by exact prefixLift 375375
  have htrace : WordTrace (prefixWord ++ tailWord_375375) baseStart_375375 baseEnd_375375 := by
    simpa [prefixWord, tailWord_375375, baseEnd_375375] using wordTrace_append hprefix tailTrace_375375
  have hstable : (prefixWord ++ tailWord_375375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375375).length < 2 ^ (prefixWord ++ tailWord_375375).sum := by decide
  have hdescent : baseEnd_375375 < baseStart_375375 := by decide
  rcases family_descends (prefixWord ++ tailWord_375375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375424 : List Nat := [2, 1, 1, 2, 1, 6, 7]
def baseStart_375424 : Nat := 118140960795 + 375424 * 2 ^ 59
def prefixEnd_375424 : Nat := 4983230072969 + 3 ^ 40 * 375424 * 2
def baseEnd_375424 : Nat := 19039304813199445488737

theorem tailTrace_375424 : CollatzResearch.WordTrace tailWord_375424 prefixEnd_375424 19039304813199445488737 := by
  unfold tailWord_375424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6846419095955220079834663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9128558794606960106446217 6846419095955220079834663)
  ·
    refine ⟨10269628643932830119751995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6846419095955220079834663 10269628643932830119751995)
    ·
      refine ⟨15404442965899245179627993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10269628643932830119751995 15404442965899245179627993)
      ·
        refine ⟨11553332224424433884720995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15404442965899245179627993 11553332224424433884720995)
        ·
          refine ⟨17329998336636650827081493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11553332224424433884720995 17329998336636650827081493)
          ·
            refine ⟨812343672029843007519445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17329998336636650827081493 812343672029843007519445)
            ·
              refine ⟨19039304813199445488737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 812343672029843007519445 19039304813199445488737)
              ·
                rfl

theorem cell20_375424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_375424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375424 prefixEnd_375424 := by exact prefixLift 375424
  have htrace : WordTrace (prefixWord ++ tailWord_375424) baseStart_375424 baseEnd_375424 := by
    simpa [prefixWord, tailWord_375424, baseEnd_375424] using wordTrace_append hprefix tailTrace_375424
  have hstable : (prefixWord ++ tailWord_375424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375424).length < 2 ^ (prefixWord ++ tailWord_375424).sum := by decide
  have hdescent : baseEnd_375424 < baseStart_375424 := by decide
  rcases family_descends (prefixWord ++ tailWord_375424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375479 : List Nat := [1, 1, 3, 1, 6, 2, 6]
def baseStart_375479 : Nat := 118140960795 + 375479 * 2 ^ 59
def prefixEnd_375479 : Nat := 4983230072969 + 3 ^ 40 * 375479 * 2
def baseEnd_375479 : Nat := 19042094090828806951675

theorem tailTrace_375479 : CollatzResearch.WordTrace tailWord_375479 prefixEnd_375479 19042094090828806951675 := by
  unfold tailWord_375479
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694844206711184552921491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9129896137807456368614327 13694844206711184552921491)
  ·
    refine ⟨20542266310066776829382237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13694844206711184552921491 20542266310066776829382237)
    ·
      refine ⟨7703349866275041311018339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20542266310066776829382237 7703349866275041311018339)
      ·
        refine ⟨11555024799412561966527509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703349866275041311018339 11555024799412561966527509)
        ·
          refine ⟨541641787472463842180977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11555024799412561966527509 541641787472463842180977)
          ·
            refine ⟨406231340604347881635733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541641787472463842180977 406231340604347881635733)
            ·
              refine ⟨19042094090828806951675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 406231340604347881635733 19042094090828806951675)
              ·
                rfl

theorem cell20_375479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_375479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375479 prefixEnd_375479 := by exact prefixLift 375479
  have htrace : WordTrace (prefixWord ++ tailWord_375479) baseStart_375479 baseEnd_375479 := by
    simpa [prefixWord, tailWord_375479, baseEnd_375479] using wordTrace_append hprefix tailTrace_375479
  have hstable : (prefixWord ++ tailWord_375479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375479).length < 2 ^ (prefixWord ++ tailWord_375479).sum := by decide
  have hdescent : baseEnd_375479 < baseStart_375479 := by decide
  rcases family_descends (prefixWord ++ tailWord_375479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375486 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_375486 : Nat := 118140960795 + 375486 * 2 ^ 59
def prefixEnd_375486 : Nat := 4983230072969 + 3 ^ 40 * 375486 * 2
def baseEnd_375486 : Nat := 171382041808198349331713

theorem tailTrace_375486 : CollatzResearch.WordTrace tailWord_375486 prefixEnd_375486 171382041808198349331713 := by
  unfold tailWord_375486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711887439710728093553289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9130066345123883165617541 1711887439710728093553289)
  ·
    refine ⟨1283915579783046070164967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1711887439710728093553289 1283915579783046070164967)
    ·
      refine ⟨1925873369674569105247451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283915579783046070164967 1925873369674569105247451)
      ·
        refine ⟨2888810054511853657871177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925873369674569105247451 2888810054511853657871177)
        ·
          refine ⟨2166607540883890243403383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2888810054511853657871177 2166607540883890243403383)
          ·
            refine ⟨3249911311325835365105075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166607540883890243403383 3249911311325835365105075)
            ·
              refine ⟨4874866966988753047657613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249911311325835365105075 4874866966988753047657613)
              ·
                refine ⟨1828075112620782392871605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4874866966988753047657613 1828075112620782392871605)
                ·
                  refine ⟨171382041808198349331713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1828075112620782392871605 171382041808198349331713)
                  ·
                    rfl

theorem cell20_375486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_375486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375486 prefixEnd_375486 := by exact prefixLift 375486
  have htrace : WordTrace (prefixWord ++ tailWord_375486) baseStart_375486 baseEnd_375486 := by
    simpa [prefixWord, tailWord_375486, baseEnd_375486] using wordTrace_append hprefix tailTrace_375486
  have hstable : (prefixWord ++ tailWord_375486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375486).length < 2 ^ (prefixWord ++ tailWord_375486).sum := by decide
  have hdescent : baseEnd_375486 < baseStart_375486 := by decide
  rcases family_descends (prefixWord ++ tailWord_375486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375538 : List Nat := [3, 2, 1, 3, 1, 10]
def baseStart_375538 : Nat := 118140960795 + 375538 * 2 ^ 59
def prefixEnd_375538 : Nat := 4983230072969 + 3 ^ 40 * 375538 * 2
def baseEnd_375538 : Nat := 6348362075004343688821

theorem tailTrace_375538 : CollatzResearch.WordTrace tailWord_375538 prefixEnd_375538 6348362075004343688821 := by
  unfold tailWord_375538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424249028374359407329817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9131330742331625086212845 3424249028374359407329817)
  ·
    refine ⟨2568186771280769555497363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3424249028374359407329817 2568186771280769555497363)
    ·
      refine ⟨3852280156921154333246045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568186771280769555497363 3852280156921154333246045)
      ·
        refine ⟨1444605058845432874967267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3852280156921154333246045 1444605058845432874967267)
        ·
          refine ⟨2166907588268149312450901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444605058845432874967267 2166907588268149312450901)
          ·
            refine ⟨6348362075004343688821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2166907588268149312450901 6348362075004343688821)
            ·
              rfl

theorem cell20_375538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 10].length) (baseStart_375538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375538 prefixEnd_375538 := by exact prefixLift 375538
  have htrace : WordTrace (prefixWord ++ tailWord_375538) baseStart_375538 baseEnd_375538 := by
    simpa [prefixWord, tailWord_375538, baseEnd_375538] using wordTrace_append hprefix tailTrace_375538
  have hstable : (prefixWord ++ tailWord_375538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375538).length < 2 ^ (prefixWord ++ tailWord_375538).sum := by decide
  have hdescent : baseEnd_375538 < baseStart_375538 := by decide
  rcases family_descends (prefixWord ++ tailWord_375538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375545 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_375545 : Nat := 118140960795 + 375545 * 2 ^ 59
def prefixEnd_375545 : Nat := 4983230072969 + 3 ^ 40 * 375545 * 2
def baseEnd_375545 : Nat := 171408971015856366364805

theorem tailTrace_375545 : CollatzResearch.WordTrace tailWord_375545 prefixEnd_375545 171408971015856366364805 := by
  unfold tailWord_375545
  simp only [CollatzResearch.WordTrace]
  refine ⟨13697251424472077824824089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9131500949648051883216059 13697251424472077824824089)
  ·
    refine ⟨10272938568354058368618067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13697251424472077824824089 10272938568354058368618067)
    ·
      refine ⟨15409407852531087552927101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10272938568354058368618067 15409407852531087552927101)
      ·
        refine ⟨5778527944699157832347663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15409407852531087552927101 5778527944699157832347663)
        ·
          refine ⟨8667791917048736748521495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778527944699157832347663 8667791917048736748521495)
          ·
            refine ⟨13001687875573105122782243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667791917048736748521495 13001687875573105122782243)
            ·
              refine ⟨19502531813359657684173365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13001687875573105122782243 19502531813359657684173365)
              ·
                refine ⟨1828362357502467907891253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19502531813359657684173365 1828362357502467907891253)
                ·
                  refine ⟨171408971015856366364805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1828362357502467907891253 171408971015856366364805)
                  ·
                    rfl

theorem cell20_375545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_375545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375545 prefixEnd_375545 := by exact prefixLift 375545
  have htrace : WordTrace (prefixWord ++ tailWord_375545) baseStart_375545 baseEnd_375545 := by
    simpa [prefixWord, tailWord_375545, baseEnd_375545] using wordTrace_append hprefix tailTrace_375545
  have hstable : (prefixWord ++ tailWord_375545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375545).length < 2 ^ (prefixWord ++ tailWord_375545).sum := by decide
  have hdescent : baseEnd_375545 < baseStart_375545 := by decide
  rcases family_descends (prefixWord ++ tailWord_375545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375562 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_375562 : Nat := 118140960795 + 375562 * 2 ^ 59
def prefixEnd_375562 : Nat := 4983230072969 + 3 ^ 40 * 375562 * 2
def baseEnd_375562 : Nat := 171416730279079862798069

theorem tailTrace_375562 : CollatzResearch.WordTrace tailWord_375562 prefixEnd_375562 171416730279079862798069 := by
  unfold tailWord_375562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424467866352622432048235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9131914310273659818795293 3424467866352622432048235)
  ·
    refine ⟨5136701799528933648072353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3424467866352622432048235 5136701799528933648072353)
    ·
      refine ⟨3852526349646700236054265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5136701799528933648072353 3852526349646700236054265)
      ·
        refine ⟨2889394762235025177040699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3852526349646700236054265 2889394762235025177040699)
        ·
          refine ⟨4334092143352537765561049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889394762235025177040699 4334092143352537765561049)
          ·
            refine ⟨3250569107514403324170787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334092143352537765561049 3250569107514403324170787)
            ·
              refine ⟨4875853661271604986256181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250569107514403324170787 4875853661271604986256181)
              ·
                refine ⟨457111280744212967461517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4875853661271604986256181 457111280744212967461517)
                ·
                  refine ⟨171416730279079862798069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457111280744212967461517 171416730279079862798069)
                  ·
                    rfl

theorem cell20_375562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_375562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375562 prefixEnd_375562 := by exact prefixLift 375562
  have htrace : WordTrace (prefixWord ++ tailWord_375562) baseStart_375562 baseEnd_375562 := by
    simpa [prefixWord, tailWord_375562, baseEnd_375562] using wordTrace_append hprefix tailTrace_375562
  have hstable : (prefixWord ++ tailWord_375562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375562).length < 2 ^ (prefixWord ++ tailWord_375562).sum := by decide
  have hdescent : baseEnd_375562 < baseStart_375562 := by decide
  rcases family_descends (prefixWord ++ tailWord_375562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375607 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_375607 : Nat := 118140960795 + 375607 * 2 ^ 59
def prefixEnd_375607 : Nat := 4983230072969 + 3 ^ 40 * 375607 * 2
def baseEnd_375607 : Nat := 171437269505259706297885

theorem tailTrace_375607 : CollatzResearch.WordTrace tailWord_375607 prefixEnd_375607 171437269505259706297885 := by
  unfold tailWord_375607
  simp only [CollatzResearch.WordTrace]
  refine ⟨13699512750247462413581075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9133008500164974942387383 13699512750247462413581075)
  ·
    refine ⟨20549269125371193620371613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13699512750247462413581075 20549269125371193620371613)
    ·
      refine ⟨7705975922014197607639355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20549269125371193620371613 7705975922014197607639355)
      ·
        refine ⟨11558963883021296411459033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7705975922014197607639355 11558963883021296411459033)
        ·
          refine ⟨8669222912265972308594275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11558963883021296411459033 8669222912265972308594275)
          ·
            refine ⟨13003834368398958462891413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8669222912265972308594275 13003834368398958462891413)
            ·
              refine ⟨609554736018701177948035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13003834368398958462891413 609554736018701177948035)
              ·
                refine ⟨914332104028051766922053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609554736018701177948035 914332104028051766922053)
                ·
                  refine ⟨171437269505259706297885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914332104028051766922053 171437269505259706297885)
                  ·
                    rfl

theorem cell20_375607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_375607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375607 prefixEnd_375607 := by exact prefixLift 375607
  have htrace : WordTrace (prefixWord ++ tailWord_375607) baseStart_375607 baseEnd_375607 := by
    simpa [prefixWord, tailWord_375607, baseEnd_375607] using wordTrace_append hprefix tailTrace_375607
  have hstable : (prefixWord ++ tailWord_375607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375607).length < 2 ^ (prefixWord ++ tailWord_375607).sum := by decide
  have hdescent : baseEnd_375607 < baseStart_375607 := by decide
  rcases family_descends (prefixWord ++ tailWord_375607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375641 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 2]
def baseStart_375641 : Nat := 118140960795 + 375641 * 2 ^ 59
def prefixEnd_375641 : Nat := 4983230072969 + 3 ^ 40 * 375641 * 2
def baseEnd_375641 : Nat := 171452788031706699164413

theorem tailTrace_375641 : CollatzResearch.WordTrace tailWord_375641 prefixEnd_375641 171452788031706699164413 := by
  unfold tailWord_375641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13700752832124286220318777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9133835221416190813545851 13700752832124286220318777)
  ·
    refine ⟨10275564624093214665239083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13700752832124286220318777 10275564624093214665239083)
    ·
      refine ⟨15413346936139821997858625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10275564624093214665239083 15413346936139821997858625)
      ·
        refine ⟨11560010202104866498393969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15413346936139821997858625 11560010202104866498393969)
        ·
          refine ⟨8670007651578649873795477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11560010202104866498393969 8670007651578649873795477)
          ·
            refine ⟨406406608667749212834163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8670007651578649873795477 406406608667749212834163)
            ·
              refine ⟨609609913001623819251245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406406608667749212834163 609609913001623819251245)
              ·
                refine ⟨228603717375608932219217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609609913001623819251245 228603717375608932219217)
                ·
                  refine ⟨171452788031706699164413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228603717375608932219217 171452788031706699164413)
                  ·
                    rfl

theorem cell20_375641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_375641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375641 prefixEnd_375641 := by exact prefixLift 375641
  have htrace : WordTrace (prefixWord ++ tailWord_375641) baseStart_375641 baseEnd_375641 := by
    simpa [prefixWord, tailWord_375641, baseEnd_375641] using wordTrace_append hprefix tailTrace_375641
  have hstable : (prefixWord ++ tailWord_375641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375641).length < 2 ^ (prefixWord ++ tailWord_375641).sum := by decide
  have hdescent : baseEnd_375641 < baseStart_375641 := by decide
  rcases family_descends (prefixWord ++ tailWord_375641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375652 : List Nat := [2, 3, 1, 1, 4, 1, 8]
def baseStart_375652 : Nat := 118140960795 + 375652 * 2 ^ 59
def prefixEnd_375652 : Nat := 4983230072969 + 3 ^ 40 * 375652 * 2
def baseEnd_375652 : Nat := 19050867636826616644189

theorem tailTrace_375652 : CollatzResearch.WordTrace tailWord_375652 prefixEnd_375652 19050867636826616644189 := by
  unfold tailWord_375652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850577017542217549484605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9134102690056290065979473 6850577017542217549484605)
  ·
    refine ⟨2568966381578331581056727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6850577017542217549484605 2568966381578331581056727)
    ·
      refine ⟨3853449572367497371585091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568966381578331581056727 3853449572367497371585091)
      ·
        refine ⟨5780174358551246057377637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853449572367497371585091 5780174358551246057377637)
        ·
          refine ⟨1083782692228358635758307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5780174358551246057377637 1083782692228358635758307)
          ·
            refine ⟨1625674038342537953637461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083782692228358635758307 1625674038342537953637461)
            ·
              refine ⟨19050867636826616644189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1625674038342537953637461 19050867636826616644189)
              ·
                rfl

theorem cell20_375652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_375652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375652 prefixEnd_375652 := by exact prefixLift 375652
  have htrace : WordTrace (prefixWord ++ tailWord_375652) baseStart_375652 baseEnd_375652 := by
    simpa [prefixWord, tailWord_375652, baseEnd_375652] using wordTrace_append hprefix tailTrace_375652
  have hstable : (prefixWord ++ tailWord_375652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375652).length < 2 ^ (prefixWord ++ tailWord_375652).sum := by decide
  have hdescent : baseEnd_375652 < baseStart_375652 := by decide
  rcases family_descends (prefixWord ++ tailWord_375652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375659 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_375659 : Nat := 118140960795 + 375659 * 2 ^ 59
def prefixEnd_375659 : Nat := 4983230072969 + 3 ^ 40 * 375659 * 2
def baseEnd_375659 : Nat := 171461003722178636564339

theorem tailTrace_375659 : CollatzResearch.WordTrace tailWord_375659 prefixEnd_375659 171461003722178636564339 := by
  unfold tailWord_375659
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701409346059075294474031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9134272897372716862982687 13701409346059075294474031)
  ·
    refine ⟨20552114019088612941711047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13701409346059075294474031 20552114019088612941711047)
    ·
      refine ⟨30828171028632919412566571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20552114019088612941711047 30828171028632919412566571)
      ·
        refine ⟨46242256542949379118849857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30828171028632919412566571 46242256542949379118849857)
        ·
          refine ⟨34681692407212034339137393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46242256542949379118849857 34681692407212034339137393)
          ·
            refine ⟨26011269305409025754353045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34681692407212034339137393 26011269305409025754353045)
            ·
              refine ⟨1219278248691048082235299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26011269305409025754353045 1219278248691048082235299)
              ·
                refine ⟨1828917373036572123352949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219278248691048082235299 1828917373036572123352949)
                ·
                  refine ⟨171461003722178636564339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1828917373036572123352949 171461003722178636564339)
                  ·
                    rfl

theorem cell20_375659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_375659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375659 prefixEnd_375659 := by exact prefixLift 375659
  have htrace : WordTrace (prefixWord ++ tailWord_375659) baseStart_375659 baseEnd_375659 := by
    simpa [prefixWord, tailWord_375659, baseEnd_375659] using wordTrace_append hprefix tailTrace_375659
  have hstable : (prefixWord ++ tailWord_375659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375659).length < 2 ^ (prefixWord ++ tailWord_375659).sum := by decide
  have hdescent : baseEnd_375659 < baseStart_375659 := by decide
  rcases family_descends (prefixWord ++ tailWord_375659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375669 : List Nat := [1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_375669 : Nat := 118140960795 + 375669 * 2 ^ 59
def prefixEnd_375669 : Nat := 4983230072969 + 3 ^ 40 * 375669 * 2
def baseEnd_375669 : Nat := 57155189331554348743655

theorem tailTrace_375669 : CollatzResearch.WordTrace tailWord_375669 prefixEnd_375669 57155189331554348743655 := by
  unfold tailWord_375669
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701774076022847002338061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9134516050681898001558707 13701774076022847002338061)
  ·
    refine ⟨5138165278508567625876773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13701774076022847002338061 5138165278508567625876773)
    ·
      refine ⟨963405989720356429851895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5138165278508567625876773 963405989720356429851895)
      ·
        refine ⟨1445108984580534644777843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963405989720356429851895 1445108984580534644777843)
        ·
          refine ⟨2167663476870801967166765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445108984580534644777843 2167663476870801967166765)
          ·
            refine ⟨812873803826550737687537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2167663476870801967166765 812873803826550737687537)
            ·
              refine ⟨609655352869913053265653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812873803826550737687537 609655352869913053265653)
              ·
                refine ⟨57155189331554348743655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 609655352869913053265653 57155189331554348743655)
                ·
                  rfl

theorem cell20_375669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_375669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375669 prefixEnd_375669 := by exact prefixLift 375669
  have htrace : WordTrace (prefixWord ++ tailWord_375669) baseStart_375669 baseEnd_375669 := by
    simpa [prefixWord, tailWord_375669, baseEnd_375669] using wordTrace_append hprefix tailTrace_375669
  have hstable : (prefixWord ++ tailWord_375669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375669).length < 2 ^ (prefixWord ++ tailWord_375669).sum := by decide
  have hdescent : baseEnd_375669 < baseStart_375669 := by decide
  rcases family_descends (prefixWord ++ tailWord_375669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375769 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 3]
def baseStart_375769 : Nat := 118140960795 + 375769 * 2 ^ 59
def prefixEnd_375769 : Nat := 4983230072969 + 3 ^ 40 * 375769 * 2
def baseEnd_375769 : Nat := 171511210719507142897223

theorem tailTrace_375769 : CollatzResearch.WordTrace tailWord_375769 prefixEnd_375769 171511210719507142897223 := by
  unfold tailWord_375769
  simp only [CollatzResearch.WordTrace]
  refine ⟨13705421375660564080978361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9136947583773709387318907 13705421375660564080978361)
  ·
    refine ⟨10279066031745423060733771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13705421375660564080978361 10279066031745423060733771)
    ·
      refine ⟨15418599047618134591100657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10279066031745423060733771 15418599047618134591100657)
      ·
        refine ⟨11563949285713600943325493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15418599047618134591100657 11563949285713600943325493)
        ·
          refine ⟨1084120245535650088436765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11563949285713600943325493 1084120245535650088436765)
          ·
            refine ⟨406545092075868783163787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084120245535650088436765 406545092075868783163787)
            ·
              refine ⟨609817638113803174745681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406545092075868783163787 609817638113803174745681)
              ·
                refine ⟨457363228585352381059261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609817638113803174745681 457363228585352381059261)
                ·
                  refine ⟨171511210719507142897223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457363228585352381059261 171511210719507142897223)
                  ·
                    rfl

theorem cell20_375769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_375769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375769 prefixEnd_375769 := by exact prefixLift 375769
  have htrace : WordTrace (prefixWord ++ tailWord_375769) baseStart_375769 baseEnd_375769 := by
    simpa [prefixWord, tailWord_375769, baseEnd_375769] using wordTrace_append hprefix tailTrace_375769
  have hstable : (prefixWord ++ tailWord_375769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375769).length < 2 ^ (prefixWord ++ tailWord_375769).sum := by decide
  have hdescent : baseEnd_375769 < baseStart_375769 := by decide
  rcases family_descends (prefixWord ++ tailWord_375769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375796 : List Nat := [2, 6, 2, 1, 1, 1, 1, 6]
def baseStart_375796 : Nat := 118140960795 + 375796 * 2 ^ 59
def prefixEnd_375796 : Nat := 4983230072969 + 3 ^ 40 * 375796 * 2
def baseEnd_375796 : Nat := 57174511418405016332371

theorem tailTrace_375796 : CollatzResearch.WordTrace tailWord_375796 prefixEnd_375796 57174511418405016332371 := by
  unfold tailWord_375796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6853203073281373846105621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9137604097708498461474161 6853203073281373846105621)
  ·
    refine ⟨321243894060064399036201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6853203073281373846105621 321243894060064399036201)
    ·
      refine ⟨240932920545048299277151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321243894060064399036201 240932920545048299277151)
      ·
        refine ⟨361399380817572448915727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240932920545048299277151 361399380817572448915727)
        ·
          refine ⟨542099071226358673373591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361399380817572448915727 542099071226358673373591)
          ·
            refine ⟨813148606839538010060387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542099071226358673373591 813148606839538010060387)
            ·
              refine ⟨1219722910259307015090581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813148606839538010060387 1219722910259307015090581)
              ·
                refine ⟨57174511418405016332371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1219722910259307015090581 57174511418405016332371)
                ·
                  rfl

theorem cell20_375796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_375796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375796 prefixEnd_375796 := by exact prefixLift 375796
  have htrace : WordTrace (prefixWord ++ tailWord_375796) baseStart_375796 baseEnd_375796 := by
    simpa [prefixWord, tailWord_375796, baseEnd_375796] using wordTrace_append hprefix tailTrace_375796
  have hstable : (prefixWord ++ tailWord_375796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375796).length < 2 ^ (prefixWord ++ tailWord_375796).sum := by decide
  have hdescent : baseEnd_375796 < baseStart_375796 := by decide
  rcases family_descends (prefixWord ++ tailWord_375796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375804 : List Nat := [2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_375804 : Nat := 118140960795 + 375804 * 2 ^ 59
def prefixEnd_375804 : Nat := 4983230072969 + 3 ^ 40 * 375804 * 2
def baseEnd_375804 : Nat := 57175728557734192243471

theorem tailTrace_375804 : CollatzResearch.WordTrace tailWord_375804 prefixEnd_375804 57175728557734192243471 := by
  unfold tailWord_375804
  simp only [CollatzResearch.WordTrace]
  refine ⟨6853348965266882529251233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9137798620355843372334977 6853348965266882529251233)
  ·
    refine ⟨5140011723950161896938425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6853348965266882529251233 5140011723950161896938425)
    ·
      refine ⟨3855008792962621422703819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5140011723950161896938425 3855008792962621422703819)
      ·
        refine ⟨5782513189443932134055729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855008792962621422703819 5782513189443932134055729)
        ·
          refine ⟨4336884892082949100541797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5782513189443932134055729 4336884892082949100541797)
          ·
            refine ⟨813165917265552956351587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4336884892082949100541797 813165917265552956351587)
            ·
              refine ⟨1219748875898329434527381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813165917265552956351587 1219748875898329434527381)
              ·
                refine ⟨57175728557734192243471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1219748875898329434527381 57175728557734192243471)
                ·
                  rfl

theorem cell20_375804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_375804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375804 prefixEnd_375804 := by exact prefixLift 375804
  have htrace : WordTrace (prefixWord ++ tailWord_375804) baseStart_375804 baseEnd_375804 := by
    simpa [prefixWord, tailWord_375804, baseEnd_375804] using wordTrace_append hprefix tailTrace_375804
  have hstable : (prefixWord ++ tailWord_375804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375804).length < 2 ^ (prefixWord ++ tailWord_375804).sum := by decide
  have hdescent : baseEnd_375804 < baseStart_375804 := by decide
  rcases family_descends (prefixWord ++ tailWord_375804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375842 : List Nat := [3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_375842 : Nat := 118140960795 + 375842 * 2 ^ 59
def prefixEnd_375842 : Nat := 4983230072969 + 3 ^ 40 * 375842 * 2
def baseEnd_375842 : Nat := 57181509969547777821197

theorem tailTrace_375842 : CollatzResearch.WordTrace tailWord_375842 prefixEnd_375842 57181509969547777821197 := by
  unfold tailWord_375842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427020976099024387096445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9138722602930731698923853 3427020976099024387096445)
  ·
    refine ⟨1285132866037134145161167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3427020976099024387096445 1285132866037134145161167)
    ·
      refine ⟨1927699299055701217741751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285132866037134145161167 1927699299055701217741751)
      ·
        refine ⟨2891548948583551826612627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1927699299055701217741751 2891548948583551826612627)
        ·
          refine ⟨4337323422875327739918941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891548948583551826612627 4337323422875327739918941)
          ·
            refine ⟨1626496283578247902469603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4337323422875327739918941 1626496283578247902469603)
            ·
              refine ⟨2439744425367371853704405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626496283578247902469603 2439744425367371853704405)
              ·
                refine ⟨57181509969547777821197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2439744425367371853704405 57181509969547777821197)
                ·
                  rfl

theorem cell20_375842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_375842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375842 prefixEnd_375842 := by exact prefixLift 375842
  have htrace : WordTrace (prefixWord ++ tailWord_375842) baseStart_375842 baseEnd_375842 := by
    simpa [prefixWord, tailWord_375842, baseEnd_375842] using wordTrace_append hprefix tailTrace_375842
  have hstable : (prefixWord ++ tailWord_375842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375842).length < 2 ^ (prefixWord ++ tailWord_375842).sum := by decide
  have hdescent : baseEnd_375842 < baseStart_375842 := by decide
  rcases family_descends (prefixWord ++ tailWord_375842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375856 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_375856 : Nat := 118140960795 + 375856 * 2 ^ 59
def prefixEnd_375856 : Nat := 4983230072969 + 3 ^ 40 * 375856 * 2
def baseEnd_375856 : Nat := 171550919890121506996867

theorem tailTrace_375856 : CollatzResearch.WordTrace tailWord_375856 prefixEnd_375856 171550919890121506996867 := by
  unfold tailWord_375856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854297263172688969697711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9139063017563585292930281 6854297263172688969697711)
  ·
    refine ⟨10281445894759033454546567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6854297263172688969697711 10281445894759033454546567)
    ·
      refine ⟨15422168842138550181819851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10281445894759033454546567 15422168842138550181819851)
      ·
        refine ⟨23133253263207825272729777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15422168842138550181819851 23133253263207825272729777)
        ·
          refine ⟨17349939947405868954547333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23133253263207825272729777 17349939947405868954547333)
          ·
            refine ⟨3253113740138600428977625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17349939947405868954547333 3253113740138600428977625)
            ·
              refine ⟨2439835305103950321733219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253113740138600428977625 2439835305103950321733219)
              ·
                refine ⟨3659752957655925482599829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439835305103950321733219 3659752957655925482599829)
                ·
                  refine ⟨171550919890121506996867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3659752957655925482599829 171550919890121506996867)
                  ·
                    rfl

theorem cell20_375856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_375856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375856 prefixEnd_375856 := by exact prefixLift 375856
  have htrace : WordTrace (prefixWord ++ tailWord_375856) baseStart_375856 baseEnd_375856 := by
    simpa [prefixWord, tailWord_375856, baseEnd_375856] using wordTrace_append hprefix tailTrace_375856
  have hstable : (prefixWord ++ tailWord_375856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375856).length < 2 ^ (prefixWord ++ tailWord_375856).sum := by decide
  have hdescent : baseEnd_375856 < baseStart_375856 := by decide
  rcases family_descends (prefixWord ++ tailWord_375856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375911 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_375911 : Nat := 118140960795 + 375911 * 2 ^ 59
def prefixEnd_375911 : Nat := 4983230072969 + 3 ^ 40 * 375911 * 2
def baseEnd_375911 : Nat := 171576023388785760163309

theorem tailTrace_375911 : CollatzResearch.WordTrace tailWord_375911 prefixEnd_375911 171576023388785760163309 := by
  unfold tailWord_375911
  simp only [CollatzResearch.WordTrace]
  refine ⟨13710600541146122332647587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9140400360764081555098391 13710600541146122332647587)
  ·
    refine ⟨20565900811719183498971381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13710600541146122332647587 20565900811719183498971381)
    ·
      refine ⟨1928053201098673453028567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20565900811719183498971381 1928053201098673453028567)
      ·
        refine ⟨2892079801648010179542851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928053201098673453028567 2892079801648010179542851)
        ·
          refine ⟨4338119702472015269314277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892079801648010179542851 4338119702472015269314277)
          ·
            refine ⟨813397444213502862996427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4338119702472015269314277 813397444213502862996427)
            ·
              refine ⟨1220096166320254294494641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813397444213502862996427 1220096166320254294494641)
              ·
                refine ⟨915072124740190720870981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220096166320254294494641 915072124740190720870981)
                ·
                  refine ⟨171576023388785760163309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915072124740190720870981 171576023388785760163309)
                  ·
                    rfl

theorem cell20_375911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_375911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375911 prefixEnd_375911 := by exact prefixLift 375911
  have htrace : WordTrace (prefixWord ++ tailWord_375911) baseStart_375911 baseEnd_375911 := by
    simpa [prefixWord, tailWord_375911, baseEnd_375911] using wordTrace_append hprefix tailTrace_375911
  have hstable : (prefixWord ++ tailWord_375911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375911).length < 2 ^ (prefixWord ++ tailWord_375911).sum := by decide
  have hdescent : baseEnd_375911 < baseStart_375911 := by decide
  rcases family_descends (prefixWord ++ tailWord_375911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375932 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_375932 : Nat := 118140960795 + 375932 * 2 ^ 59
def prefixEnd_375932 : Nat := 4983230072969 + 3 ^ 40 * 375932 * 2
def baseEnd_375932 : Nat := 171585608361003020463223

theorem tailTrace_375932 : CollatzResearch.WordTrace tailWord_375932 prefixEnd_375932 171585608361003020463223 := by
  unfold tailWord_375932
  simp only [CollatzResearch.WordTrace]
  refine ⟨6855683237035021459581025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9140910982713361946108033 6855683237035021459581025)
  ·
    refine ⟨5141762427776266094685769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6855683237035021459581025 5141762427776266094685769)
    ·
      refine ⟨3856321820832199571014327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5141762427776266094685769 3856321820832199571014327)
      ·
        refine ⟨5784482731248299356521491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856321820832199571014327 5784482731248299356521491)
        ·
          refine ⟨8676724096872449034782237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784482731248299356521491 8676724096872449034782237)
          ·
            refine ⟨3253771536327168388043339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8676724096872449034782237 3253771536327168388043339)
            ·
              refine ⟨4880657304490752582065009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253771536327168388043339 4880657304490752582065009)
              ·
                refine ⟨3660492978368064436548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4880657304490752582065009 3660492978368064436548757)
                ·
                  refine ⟨171585608361003020463223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3660492978368064436548757 171585608361003020463223)
                  ·
                    rfl

theorem cell20_375932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_375932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375932 prefixEnd_375932 := by exact prefixLift 375932
  have htrace : WordTrace (prefixWord ++ tailWord_375932) baseStart_375932 baseEnd_375932 := by
    simpa [prefixWord, tailWord_375932, baseEnd_375932] using wordTrace_append hprefix tailTrace_375932
  have hstable : (prefixWord ++ tailWord_375932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375932).length < 2 ^ (prefixWord ++ tailWord_375932).sum := by decide
  have hdescent : baseEnd_375932 < baseStart_375932 := by decide
  rcases family_descends (prefixWord ++ tailWord_375932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375934 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_375934 : Nat := 118140960795 + 375934 * 2 ^ 59
def prefixEnd_375934 : Nat := 4983230072969 + 3 ^ 40 * 375934 * 2
def baseEnd_375934 : Nat := 171586521215499902396549

theorem tailTrace_375934 : CollatzResearch.WordTrace tailWord_375934 prefixEnd_375934 171586521215499902396549 := by
  unfold tailWord_375934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713929927507849657591857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9140959613375198173823237 1713929927507849657591857)
  ·
    refine ⟨1285447445630887243193893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1713929927507849657591857 1285447445630887243193893)
    ·
      refine ⟨241021396055791358098855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1285447445630887243193893 241021396055791358098855)
      ·
        refine ⟨361532094083687037148283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241021396055791358098855 361532094083687037148283)
        ·
          refine ⟨542298141125530555722425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361532094083687037148283 542298141125530555722425)
          ·
            refine ⟨406723605844147916791819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542298141125530555722425 406723605844147916791819)
            ·
              refine ⟨610085408766221875187729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406723605844147916791819 610085408766221875187729)
              ·
                refine ⟨457564056574666406390797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610085408766221875187729 457564056574666406390797)
                ·
                  refine ⟨171586521215499902396549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457564056574666406390797 171586521215499902396549)
                  ·
                    rfl

theorem cell20_375934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_375934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375934 prefixEnd_375934 := by exact prefixLift 375934
  have htrace : WordTrace (prefixWord ++ tailWord_375934) baseStart_375934 baseEnd_375934 := by
    simpa [prefixWord, tailWord_375934, baseEnd_375934] using wordTrace_append hprefix tailTrace_375934
  have hstable : (prefixWord ++ tailWord_375934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375934).length < 2 ^ (prefixWord ++ tailWord_375934).sum := by decide
  have hdescent : baseEnd_375934 < baseStart_375934 := by decide
  rcases family_descends (prefixWord ++ tailWord_375934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375939 : List Nat := [1, 1, 1, 3, 3, 2, 9]
def baseStart_375939 : Nat := 118140960795 + 375939 * 2 ^ 59
def prefixEnd_375939 : Nat := 4983230072969 + 3 ^ 40 * 375939 * 2
def baseEnd_375939 : Nat := 19065422594638011914429

theorem tailTrace_375939 : CollatzResearch.WordTrace tailWord_375939 prefixEnd_375939 19065422594638011914429 := by
  unfold tailWord_375939
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711621785044683114666871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9141081190029788743111247 13711621785044683114666871)
  ·
    refine ⟨20567432677567024672000307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13711621785044683114666871 20567432677567024672000307)
    ·
      refine ⟨30851149016350537008000461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20567432677567024672000307 30851149016350537008000461)
      ·
        refine ⟨11569180881131451378000173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30851149016350537008000461 11569180881131451378000173)
        ·
          refine ⟨4338442830424294266750065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11569180881131451378000173 4338442830424294266750065)
          ·
            refine ⟨3253832122818220700062549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4338442830424294266750065 3253832122818220700062549)
            ·
              refine ⟨19065422594638011914429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3253832122818220700062549 19065422594638011914429)
              ·
                rfl

theorem cell20_375939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_375939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375939 prefixEnd_375939 := by exact prefixLift 375939
  have htrace : WordTrace (prefixWord ++ tailWord_375939) baseStart_375939 baseEnd_375939 := by
    simpa [prefixWord, tailWord_375939, baseEnd_375939] using wordTrace_append hprefix tailTrace_375939
  have hstable : (prefixWord ++ tailWord_375939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375939).length < 2 ^ (prefixWord ++ tailWord_375939).sum := by decide
  have hdescent : baseEnd_375939 < baseStart_375939 := by decide
  rcases family_descends (prefixWord ++ tailWord_375939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375959 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 3]
def baseStart_375959 : Nat := 118140960795 + 375959 * 2 ^ 59
def prefixEnd_375959 : Nat := 4983230072969 + 3 ^ 40 * 375959 * 2
def baseEnd_375959 : Nat := 171597931896710926563113

theorem tailTrace_375959 : CollatzResearch.WordTrace tailWord_375959 prefixEnd_375959 171597931896710926563113 := by
  unfold tailWord_375959
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712351244972226530394931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9141567496648151020263287 13712351244972226530394931)
  ·
    refine ⟨20568526867458339795592397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13712351244972226530394931 20568526867458339795592397)
    ·
      refine ⟨7713197575296877423347149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20568526867458339795592397 7713197575296877423347149)
      ·
        refine ⟨2892449090736329033755181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7713197575296877423347149 2892449090736329033755181)
        ·
          refine ⟨1084668409026123387658193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2892449090736329033755181 1084668409026123387658193)
          ·
            refine ⟨813501306769592540743645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084668409026123387658193 813501306769592540743645)
            ·
              refine ⟨305062990038597202778867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 813501306769592540743645 305062990038597202778867)
              ·
                refine ⟨457594485057895804168301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305062990038597202778867 457594485057895804168301)
                ·
                  refine ⟨171597931896710926563113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457594485057895804168301 171597931896710926563113)
                  ·
                    rfl

theorem cell20_375959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_375959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375959 prefixEnd_375959 := by exact prefixLift 375959
  have htrace : WordTrace (prefixWord ++ tailWord_375959) baseStart_375959 baseEnd_375959 := by
    simpa [prefixWord, tailWord_375959, baseEnd_375959] using wordTrace_append hprefix tailTrace_375959
  have hstable : (prefixWord ++ tailWord_375959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375959).length < 2 ^ (prefixWord ++ tailWord_375959).sum := by decide
  have hdescent : baseEnd_375959 < baseStart_375959 := by decide
  rcases family_descends (prefixWord ++ tailWord_375959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375966 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_375966 : Nat := 118140960795 + 375966 * 2 ^ 59
def prefixEnd_375966 : Nat := 4983230072969 + 3 ^ 40 * 375966 * 2
def baseEnd_375966 : Nat := 171601126887450013329751

theorem tailTrace_375966 : CollatzResearch.WordTrace tailWord_375966 prefixEnd_375966 171601126887450013329751 := by
  unfold tailWord_375966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714075819493358340737469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9141737703964577817266501 1714075819493358340737469)
  ·
    refine ⟨642778432310009377776551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1714075819493358340737469 642778432310009377776551)
    ·
      refine ⟨964167648465014066664827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642778432310009377776551 964167648465014066664827)
      ·
        refine ⟨1446251472697521099997241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964167648465014066664827 1446251472697521099997241)
        ·
          refine ⟨1084688604523140824997931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1446251472697521099997241 1084688604523140824997931)
          ·
            refine ⟨1627032906784711237496897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084688604523140824997931 1627032906784711237496897)
            ·
              refine ⟨1220274680088533428122673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1627032906784711237496897 1220274680088533428122673)
              ·
                refine ⟨915206010066400071092005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220274680088533428122673 915206010066400071092005)
                ·
                  refine ⟨171601126887450013329751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915206010066400071092005 171601126887450013329751)
                  ·
                    rfl

theorem cell20_375966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_375966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375966 prefixEnd_375966 := by exact prefixLift 375966
  have htrace : WordTrace (prefixWord ++ tailWord_375966) baseStart_375966 baseEnd_375966 := by
    simpa [prefixWord, tailWord_375966, baseEnd_375966] using wordTrace_append hprefix tailTrace_375966
  have hstable : (prefixWord ++ tailWord_375966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375966).length < 2 ^ (prefixWord ++ tailWord_375966).sum := by decide
  have hdescent : baseEnd_375966 < baseStart_375966 := by decide
  rcases family_descends (prefixWord ++ tailWord_375966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375973 : List Nat := [1, 3, 1, 2, 1, 6, 2, 4]
def baseStart_375973 : Nat := 118140960795 + 375973 * 2 ^ 59
def prefixEnd_375973 : Nat := 4983230072969 + 3 ^ 40 * 375973 * 2
def baseEnd_375973 : Nat := 57201440626063033365463

theorem tailTrace_375973 : CollatzResearch.WordTrace tailWord_375973 prefixEnd_375973 57201440626063033365463 := by
  unfold tailWord_375973
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712861866921506921404573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9141907911281004614269715 13712861866921506921404573)
  ·
    refine ⟨5142323200095565095526715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13712861866921506921404573 5142323200095565095526715)
    ·
      refine ⟨7713484800143347643290073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142323200095565095526715 7713484800143347643290073)
      ·
        refine ⟨5785113600107510732467555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7713484800143347643290073 5785113600107510732467555)
        ·
          refine ⟨8677670400161266098701333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785113600107510732467555 8677670400161266098701333)
          ·
            refine ⟨406765800007559348376625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8677670400161266098701333 406765800007559348376625)
            ·
              refine ⟨305074350005669511282469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406765800007559348376625 305074350005669511282469)
              ·
                refine ⟨57201440626063033365463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305074350005669511282469 57201440626063033365463)
                ·
                  rfl

theorem cell20_375973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_375973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_375973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_375973 prefixEnd_375973 := by exact prefixLift 375973
  have htrace : WordTrace (prefixWord ++ tailWord_375973) baseStart_375973 baseEnd_375973 := by
    simpa [prefixWord, tailWord_375973, baseEnd_375973] using wordTrace_append hprefix tailTrace_375973
  have hstable : (prefixWord ++ tailWord_375973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375973).length < 2 ^ (prefixWord ++ tailWord_375973).sum := by decide
  have hdescent : baseEnd_375973 < baseStart_375973 := by decide
  rcases family_descends (prefixWord ++ tailWord_375973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376014 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_376014 : Nat := 118140960795 + 376014 * 2 ^ 59
def prefixEnd_376014 : Nat := 4983230072969 + 3 ^ 40 * 376014 * 2
def baseEnd_376014 : Nat := 171623035395375179729555

theorem tailTrace_376014 : CollatzResearch.WordTrace tailWord_376014 prefixEnd_376014 171623035395375179729555 := by
  unfold tailWord_376014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714294657471621365455887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9142904839848647282431397 1714294657471621365455887)
  ·
    refine ⟨2571441986207432048183831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1714294657471621365455887 2571441986207432048183831)
    ·
      refine ⟨3857162979311148072275747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571441986207432048183831 3857162979311148072275747)
      ·
        refine ⟨5785744468966722108413621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857162979311148072275747 5785744468966722108413621)
        ·
          refine ⟨542413543965630197663777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5785744468966722108413621 542413543965630197663777)
          ·
            refine ⟨406810157974222648247833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542413543965630197663777 406810157974222648247833)
            ·
              refine ⟨305107618480666986185875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406810157974222648247833 305107618480666986185875)
              ·
                refine ⟨457661427721000479278813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305107618480666986185875 457661427721000479278813)
                ·
                  refine ⟨171623035395375179729555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457661427721000479278813 171623035395375179729555)
                  ·
                    rfl

theorem cell20_376014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_376014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376014 prefixEnd_376014 := by exact prefixLift 376014
  have htrace : WordTrace (prefixWord ++ tailWord_376014) baseStart_376014 baseEnd_376014 := by
    simpa [prefixWord, tailWord_376014, baseEnd_376014] using wordTrace_append hprefix tailTrace_376014
  have hstable : (prefixWord ++ tailWord_376014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376014).length < 2 ^ (prefixWord ++ tailWord_376014).sum := by decide
  have hdescent : baseEnd_376014 < baseStart_376014 := by decide
  rcases family_descends (prefixWord ++ tailWord_376014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376018 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_376018 : Nat := 118140960795 + 376018 * 2 ^ 59
def prefixEnd_376018 : Nat := 4983230072969 + 3 ^ 40 * 376018 * 2
def baseEnd_376018 : Nat := 171624861104368943596205

theorem tailTrace_376018 : CollatzResearch.WordTrace tailWord_376018 prefixEnd_376018 171624861104368943596205 := by
  unfold tailWord_376018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428625787939619901698177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9143002101172319737861805 3428625787939619901698177)
  ·
    refine ⟨2571469340954714926273633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3428625787939619901698177 2571469340954714926273633)
    ·
      refine ⟨1928602005716036194705225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2571469340954714926273633 1928602005716036194705225)
      ·
        refine ⟨1446451504287027146028919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1928602005716036194705225 1446451504287027146028919)
        ·
          refine ⟨2169677256430540719043379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446451504287027146028919 2169677256430540719043379)
          ·
            refine ⟨3254515884645811078565069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169677256430540719043379 3254515884645811078565069)
            ·
              refine ⟨1220443456742179154461901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3254515884645811078565069 1220443456742179154461901)
              ·
                refine ⟨457666296278317182923213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1220443456742179154461901 457666296278317182923213)
                ·
                  refine ⟨171624861104368943596205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457666296278317182923213 171624861104368943596205)
                  ·
                    rfl

theorem cell20_376018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_376018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376018 prefixEnd_376018 := by exact prefixLift 376018
  have htrace : WordTrace (prefixWord ++ tailWord_376018) baseStart_376018 baseEnd_376018 := by
    simpa [prefixWord, tailWord_376018, baseEnd_376018] using wordTrace_append hprefix tailTrace_376018
  have hstable : (prefixWord ++ tailWord_376018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376018).length < 2 ^ (prefixWord ++ tailWord_376018).sum := by decide
  have hdescent : baseEnd_376018 < baseStart_376018 := by decide
  rcases family_descends (prefixWord ++ tailWord_376018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376066 : List Nat := [3, 4, 1, 1, 3, 2, 1, 5]
def baseStart_376066 : Nat := 118140960795 + 376066 * 2 ^ 59
def prefixEnd_376066 : Nat := 4983230072969 + 3 ^ 40 * 376066 * 2
def baseEnd_376066 : Nat := 57215589870764703332003

theorem tailTrace_376066 : CollatzResearch.WordTrace tailWord_376066 prefixEnd_376066 57215589870764703332003 := by
  unfold tailWord_376066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429063463896145951135013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9144169237056389203026701 3429063463896145951135013)
  ·
    refine ⟨642949399480527365837815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3429063463896145951135013 642949399480527365837815)
    ·
      refine ⟨964424099220791048756723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642949399480527365837815 964424099220791048756723)
      ·
        refine ⟨1446636148831186573135085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964424099220791048756723 1446636148831186573135085)
        ·
          refine ⟨542488555811694964925657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1446636148831186573135085 542488555811694964925657)
          ·
            refine ⟨406866416858771223694243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542488555811694964925657 406866416858771223694243)
            ·
              refine ⟨610299625288156835541365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406866416858771223694243 610299625288156835541365)
              ·
                refine ⟨57215589870764703332003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610299625288156835541365 57215589870764703332003)
                ·
                  rfl

theorem cell20_376066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_376066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376066 prefixEnd_376066 := by exact prefixLift 376066
  have htrace : WordTrace (prefixWord ++ tailWord_376066) baseStart_376066 baseEnd_376066 := by
    simpa [prefixWord, tailWord_376066, baseEnd_376066] using wordTrace_append hprefix tailTrace_376066
  have hstable : (prefixWord ++ tailWord_376066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376066).length < 2 ^ (prefixWord ++ tailWord_376066).sum := by decide
  have hdescent : baseEnd_376066 < baseStart_376066 := by decide
  rcases family_descends (prefixWord ++ tailWord_376066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376115 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_376115 : Nat := 118140960795 + 376115 * 2 ^ 59
def prefixEnd_376115 : Nat := 4983230072969 + 3 ^ 40 * 376115 * 2
def baseEnd_376115 : Nat := 171669134547467717362475

theorem tailTrace_376115 : CollatzResearch.WordTrace tailWord_376115 prefixEnd_376115 171669134547467717362475 := by
  unfold tailWord_376115
  simp only [CollatzResearch.WordTrace]
  refine ⟨13718041032407065173073799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9145360688271376782049199 13718041032407065173073799)
  ·
    refine ⟨20577061548610597759610699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13718041032407065173073799 20577061548610597759610699)
    ·
      refine ⟨30865592322915896639416049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20577061548610597759610699 30865592322915896639416049)
      ·
        refine ⟨23149194242186922479562037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30865592322915896639416049 23149194242186922479562037)
        ·
          refine ⟨2170236960205023982458941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23149194242186922479562037 2170236960205023982458941)
          ·
            refine ⟨813838860076883993422103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2170236960205023982458941 813838860076883993422103)
            ·
              refine ⟨1220758290115325990133155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813838860076883993422103 1220758290115325990133155)
              ·
                refine ⟨1831137435172988985199733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220758290115325990133155 1831137435172988985199733)
                ·
                  refine ⟨171669134547467717362475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831137435172988985199733 171669134547467717362475)
                  ·
                    rfl

theorem cell20_376115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_376115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376115 prefixEnd_376115 := by exact prefixLift 376115
  have htrace : WordTrace (prefixWord ++ tailWord_376115) baseStart_376115 baseEnd_376115 := by
    simpa [prefixWord, tailWord_376115, baseEnd_376115] using wordTrace_append hprefix tailTrace_376115
  have hstable : (prefixWord ++ tailWord_376115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376115).length < 2 ^ (prefixWord ++ tailWord_376115).sum := by decide
  have hdescent : baseEnd_376115 < baseStart_376115 := by decide
  rcases family_descends (prefixWord ++ tailWord_376115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376173 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 2]
def baseStart_376173 : Nat := 118140960795 + 376173 * 2 ^ 59
def prefixEnd_376173 : Nat := 4983230072969 + 3 ^ 40 * 376173 * 2
def baseEnd_376173 : Nat := 171695607327877293428905

theorem tailTrace_376173 : CollatzResearch.WordTrace tailWord_376173 prefixEnd_376173 171695607327877293428905 := by
  unfold tailWord_376173
  simp only [CollatzResearch.WordTrace]
  refine ⟨13720156466196941078685173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9146770977464627385790115 13720156466196941078685173)
  ·
    refine ⟨1286264668705963226126735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13720156466196941078685173 1286264668705963226126735)
    ·
      refine ⟨1929397003058944839190103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286264668705963226126735 1929397003058944839190103)
      ·
        refine ⟨2894095504588417258785155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929397003058944839190103 2894095504588417258785155)
        ·
          refine ⟨4341143256882625888177733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894095504588417258785155 4341143256882625888177733)
          ·
            refine ⟨813964360665492354033325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4341143256882625888177733 813964360665492354033325)
            ·
              refine ⟨305236635249559632762497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 813964360665492354033325 305236635249559632762497)
              ·
                refine ⟨228927476437169724571873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305236635249559632762497 228927476437169724571873)
                ·
                  refine ⟨171695607327877293428905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228927476437169724571873 171695607327877293428905)
                  ·
                    rfl

theorem cell20_376173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_376173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376173 prefixEnd_376173 := by exact prefixLift 376173
  have htrace : WordTrace (prefixWord ++ tailWord_376173) baseStart_376173 baseEnd_376173 := by
    simpa [prefixWord, tailWord_376173, baseEnd_376173] using wordTrace_append hprefix tailTrace_376173
  have hstable : (prefixWord ++ tailWord_376173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376173).length < 2 ^ (prefixWord ++ tailWord_376173).sum := by decide
  have hdescent : baseEnd_376173 < baseStart_376173 := by decide
  rcases family_descends (prefixWord ++ tailWord_376173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376177 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 2]
def baseStart_376177 : Nat := 118140960795 + 376177 * 2 ^ 59
def prefixEnd_376177 : Nat := 4983230072969 + 3 ^ 40 * 376177 * 2
def baseEnd_376177 : Nat := 171697433036871057295555

theorem tailTrace_376177 : CollatzResearch.WordTrace tailWord_376177 prefixEnd_376177 171697433036871057295555 := by
  unfold tailWord_376177
  simp only [CollatzResearch.WordTrace]
  refine ⟨13720302358182449761830785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9146868238788299841220523 13720302358182449761830785)
  ·
    refine ⟨10290226768636837321373089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13720302358182449761830785 10290226768636837321373089)
    ·
      refine ⟨7717670076477627991029817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10290226768636837321373089 7717670076477627991029817)
      ·
        refine ⟨5788252557358220993272363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7717670076477627991029817 5788252557358220993272363)
        ·
          refine ⟨8682378836037331489908545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788252557358220993272363 8682378836037331489908545)
          ·
            refine ⟨6511784127027998617431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682378836037331489908545 6511784127027998617431409)
            ·
              refine ⟨4883838095270998963073557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511784127027998617431409 4883838095270998963073557)
              ·
                refine ⟨228929910715828076394073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4883838095270998963073557 228929910715828076394073)
                ·
                  refine ⟨171697433036871057295555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228929910715828076394073 171697433036871057295555)
                  ·
                    rfl

theorem cell20_376177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_376177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376177 prefixEnd_376177 := by exact prefixLift 376177
  have htrace : WordTrace (prefixWord ++ tailWord_376177) baseStart_376177 baseEnd_376177 := by
    simpa [prefixWord, tailWord_376177, baseEnd_376177] using wordTrace_append hprefix tailTrace_376177
  have hstable : (prefixWord ++ tailWord_376177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376177).length < 2 ^ (prefixWord ++ tailWord_376177).sum := by decide
  have hdescent : baseEnd_376177 < baseStart_376177 := by decide
  rcases family_descends (prefixWord ++ tailWord_376177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376215 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 2]
def baseStart_376215 : Nat := 118140960795 + 376215 * 2 ^ 59
def prefixEnd_376215 : Nat := 4983230072969 + 3 ^ 40 * 376215 * 2
def baseEnd_376215 : Nat := 171714777272311814028733

theorem tailTrace_376215 : CollatzResearch.WordTrace tailWord_376215 prefixEnd_376215 171714777272311814028733 := by
  unfold tailWord_376215
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721688332044782251714099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9147792221363188167809399 13721688332044782251714099)
  ·
    refine ⟨20582532498067173377571149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721688332044782251714099 20582532498067173377571149)
    ·
      refine ⟨7718449686775190016589181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20582532498067173377571149 7718449686775190016589181)
      ·
        refine ⟨2894418632540696256220943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7718449686775190016589181 2894418632540696256220943)
        ·
          refine ⟨4341627948811044384331415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894418632540696256220943 4341627948811044384331415)
          ·
            refine ⟨6512441923216566576497123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341627948811044384331415 6512441923216566576497123)
            ·
              refine ⟨9768662884824849864745685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6512441923216566576497123 9768662884824849864745685)
              ·
                refine ⟨228953036363082418704977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9768662884824849864745685 228953036363082418704977)
                ·
                  refine ⟨171714777272311814028733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228953036363082418704977 171714777272311814028733)
                  ·
                    rfl

theorem cell20_376215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 2].length) (baseStart_376215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376215 prefixEnd_376215 := by exact prefixLift 376215
  have htrace : WordTrace (prefixWord ++ tailWord_376215) baseStart_376215 baseEnd_376215 := by
    simpa [prefixWord, tailWord_376215, baseEnd_376215] using wordTrace_append hprefix tailTrace_376215
  have hstable : (prefixWord ++ tailWord_376215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376215).length < 2 ^ (prefixWord ++ tailWord_376215).sum := by decide
  have hdescent : baseEnd_376215 < baseStart_376215 := by decide
  rcases family_descends (prefixWord ++ tailWord_376215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376222 : List Nat := [4, 3, 1, 2, 10]
def baseStart_376222 : Nat := 118140960795 + 376222 * 2 ^ 59
def prefixEnd_376222 : Nat := 4983230072969 + 3 ^ 40 * 376222 * 2
def baseEnd_376222 : Nat := 2119974966210504948091

theorem tailTrace_376222 : CollatzResearch.WordTrace tailWord_376222 prefixEnd_376222 2119974966210504948091 := by
  unfold tailWord_376222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715242955377427805902365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9147962428679614964812613 1715242955377427805902365)
  ·
    refine ⟨643216108266535427213387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1715242955377427805902365 643216108266535427213387)
    ·
      refine ⟨964824162399803140820081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643216108266535427213387 964824162399803140820081)
      ·
        refine ⟨723618121799852355615061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 964824162399803140820081 723618121799852355615061)
        ·
          refine ⟨2119974966210504948091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 723618121799852355615061 2119974966210504948091)
          ·
            rfl

theorem cell20_376222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 10].length) (baseStart_376222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376222 prefixEnd_376222 := by exact prefixLift 376222
  have htrace : WordTrace (prefixWord ++ tailWord_376222) baseStart_376222 baseEnd_376222 := by
    simpa [prefixWord, tailWord_376222, baseEnd_376222] using wordTrace_append hprefix tailTrace_376222
  have hstable : (prefixWord ++ tailWord_376222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376222).length < 2 ^ (prefixWord ++ tailWord_376222).sum := by decide
  have hdescent : baseEnd_376222 < baseStart_376222 := by decide
  rcases family_descends (prefixWord ++ tailWord_376222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376250 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_376250 : Nat := 118140960795 + 376250 * 2 ^ 59
def prefixEnd_376250 : Nat := 4983230072969 + 3 ^ 40 * 376250 * 2
def baseEnd_376250 : Nat := 171730752226007247861923

theorem tailTrace_376250 : CollatzResearch.WordTrace tailWord_376250 prefixEnd_376250 171730752226007247861923 := by
  unfold tailWord_376250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430741221729495807309551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9148643257945322152825469 3430741221729495807309551)
  ·
    refine ⟨5146111832594243710964327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3430741221729495807309551 5146111832594243710964327)
    ·
      refine ⟨7719167748891365566446491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5146111832594243710964327 7719167748891365566446491)
      ·
        refine ⟨11578751623337048349669737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719167748891365566446491 11578751623337048349669737)
        ·
          refine ⟨8684063717502786262252303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11578751623337048349669737 8684063717502786262252303)
          ·
            refine ⟨13026095576254179393378455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684063717502786262252303 13026095576254179393378455)
            ·
              refine ⟨19539143364381269090067683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13026095576254179393378455 19539143364381269090067683)
              ·
                refine ⟨29308715046571903635101525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19539143364381269090067683 29308715046571903635101525)
                ·
                  refine ⟨171730752226007247861923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29308715046571903635101525 171730752226007247861923)
                  ·
                    rfl

theorem cell20_376250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_376250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376250 prefixEnd_376250 := by exact prefixLift 376250
  have htrace : WordTrace (prefixWord ++ tailWord_376250) baseStart_376250 baseEnd_376250 := by
    simpa [prefixWord, tailWord_376250, baseEnd_376250] using wordTrace_append hprefix tailTrace_376250
  have hstable : (prefixWord ++ tailWord_376250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376250).length < 2 ^ (prefixWord ++ tailWord_376250).sum := by decide
  have hdescent : baseEnd_376250 < baseStart_376250 := by decide
  rcases family_descends (prefixWord ++ tailWord_376250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376281 : List Nat := [1, 2, 1, 2, 4, 3, 7]
def baseStart_376281 : Nat := 118140960795 + 376281 * 2 ^ 59
def prefixEnd_376281 : Nat := 4983230072969 + 3 ^ 40 * 376281 * 2
def baseEnd_376281 : Nat := 19082766830078768647607

theorem tailTrace_376281 : CollatzResearch.WordTrace tailWord_376281 prefixEnd_376281 19082766830078768647607 := by
  unfold tailWord_376281
  simp only [CollatzResearch.WordTrace]
  refine ⟨13724095549805675523616697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9149397033203783682411131 13724095549805675523616697)
  ·
    refine ⟨10293071662354256642712523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13724095549805675523616697 10293071662354256642712523)
    ·
      refine ⟨15439607493531384964068785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10293071662354256642712523 15439607493531384964068785)
      ·
        refine ⟨11579705620148538723051589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15439607493531384964068785 11579705620148538723051589)
        ·
          refine ⟨2171194803777851010572173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11579705620148538723051589 2171194803777851010572173)
          ·
            refine ⟨814198051416694128964565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171194803777851010572173 814198051416694128964565)
            ·
              refine ⟨19082766830078768647607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 814198051416694128964565 19082766830078768647607)
              ·
                rfl

theorem cell20_376281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_376281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376281 prefixEnd_376281 := by exact prefixLift 376281
  have htrace : WordTrace (prefixWord ++ tailWord_376281) baseStart_376281 baseEnd_376281 := by
    simpa [prefixWord, tailWord_376281, baseEnd_376281] using wordTrace_append hprefix tailTrace_376281
  have hstable : (prefixWord ++ tailWord_376281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376281).length < 2 ^ (prefixWord ++ tailWord_376281).sum := by decide
  have hdescent : baseEnd_376281 < baseStart_376281 := by decide
  rcases family_descends (prefixWord ++ tailWord_376281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376291 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_376291 : Nat := 118140960795 + 376291 * 2 ^ 59
def prefixEnd_376291 : Nat := 4983230072969 + 3 ^ 40 * 376291 * 2
def baseEnd_376291 : Nat := 171749465743193327495089

theorem tailTrace_376291 : CollatzResearch.WordTrace tailWord_376291 prefixEnd_376291 171749465743193327495089 := by
  unfold tailWord_376291
  simp only [CollatzResearch.WordTrace]
  refine ⟨13724460279769447231480727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9149640186512964820987151 13724460279769447231480727)
  ·
    refine ⟨20586690419654170847221091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13724460279769447231480727 20586690419654170847221091)
    ·
      refine ⟨30880035629481256270831637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20586690419654170847221091 30880035629481256270831637)
      ·
        refine ⟨1447501670131933887695233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30880035629481256270831637 1447501670131933887695233)
        ·
          refine ⟨1085626252598950415771425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447501670131933887695233 1085626252598950415771425)
          ·
            refine ⟨814219689449212811828569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085626252598950415771425 814219689449212811828569)
            ·
              refine ⟨610664767086909608871427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814219689449212811828569 610664767086909608871427)
              ·
                refine ⟨915997150630364413307141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610664767086909608871427 915997150630364413307141)
                ·
                  refine ⟨171749465743193327495089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915997150630364413307141 171749465743193327495089)
                  ·
                    rfl

theorem cell20_376291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_376291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376291 prefixEnd_376291 := by exact prefixLift 376291
  have htrace : WordTrace (prefixWord ++ tailWord_376291) baseStart_376291 baseEnd_376291 := by
    simpa [prefixWord, tailWord_376291, baseEnd_376291] using wordTrace_append hprefix tailTrace_376291
  have hstable : (prefixWord ++ tailWord_376291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376291).length < 2 ^ (prefixWord ++ tailWord_376291).sum := by decide
  have hdescent : baseEnd_376291 < baseStart_376291 := by decide
  rcases family_descends (prefixWord ++ tailWord_376291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376312 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_376312 : Nat := 118140960795 + 376312 * 2 ^ 59
def prefixEnd_376312 : Nat := 4983230072969 + 3 ^ 40 * 376312 * 2
def baseEnd_376312 : Nat := 171759050715410587795003

theorem tailTrace_376312 : CollatzResearch.WordTrace tailWord_376312 prefixEnd_376312 171759050715410587795003 := by
  unfold tailWord_376312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6862613106346683908997595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9150150808462245211996793 6862613106346683908997595)
  ·
    refine ⟨10293919659520025863496393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6862613106346683908997595 10293919659520025863496393)
    ·
      refine ⟨7720439744640019397622295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10293919659520025863496393 7720439744640019397622295)
      ·
        refine ⟨11580659616960029096433443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7720439744640019397622295 11580659616960029096433443)
        ·
          refine ⟨17370989425440043644650165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11580659616960029096433443 17370989425440043644650165)
          ·
            refine ⟨1628530258635004091685953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17370989425440043644650165 1628530258635004091685953)
            ·
              refine ⟨1221397693976253068764465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628530258635004091685953 1221397693976253068764465)
              ·
                refine ⟨916048270482189801573349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221397693976253068764465 916048270482189801573349)
                ·
                  refine ⟨171759050715410587795003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 916048270482189801573349 171759050715410587795003)
                  ·
                    rfl

theorem cell20_376312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_376312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376312 prefixEnd_376312 := by exact prefixLift 376312
  have htrace : WordTrace (prefixWord ++ tailWord_376312) baseStart_376312 baseEnd_376312 := by
    simpa [prefixWord, tailWord_376312, baseEnd_376312] using wordTrace_append hprefix tailTrace_376312
  have hstable : (prefixWord ++ tailWord_376312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376312).length < 2 ^ (prefixWord ++ tailWord_376312).sum := by decide
  have hdescent : baseEnd_376312 < baseStart_376312 := by decide
  rcases family_descends (prefixWord ++ tailWord_376312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376322 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_376322 : Nat := 118140960795 + 376322 * 2 ^ 59
def prefixEnd_376322 : Nat := 4983230072969 + 3 ^ 40 * 376322 * 2
def baseEnd_376322 : Nat := 171763614987894997461629

theorem tailTrace_376322 : CollatzResearch.WordTrace tailWord_376322 prefixEnd_376322 171763614987894997461629 := by
  unfold tailWord_376322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431397735664284881464805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9150393961771426350572813 3431397735664284881464805)
  ·
    refine ⟨643387075437053415274651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3431397735664284881464805 643387075437053415274651)
    ·
      refine ⟨965080613155580122911977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643387075437053415274651 965080613155580122911977)
      ·
        refine ⟨723810459866685092183983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965080613155580122911977 723810459866685092183983)
        ·
          refine ⟨1085715689800027638275975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723810459866685092183983 1085715689800027638275975)
          ·
            refine ⟨1628573534700041457413963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085715689800027638275975 1628573534700041457413963)
            ·
              refine ⟨2442860302050062186120945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628573534700041457413963 2442860302050062186120945)
              ·
                refine ⟨1832145226537546639590709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442860302050062186120945 1832145226537546639590709)
                ·
                  refine ⟨171763614987894997461629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1832145226537546639590709 171763614987894997461629)
                  ·
                    rfl

theorem cell20_376322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_376322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376322 prefixEnd_376322 := by exact prefixLift 376322
  have htrace : WordTrace (prefixWord ++ tailWord_376322) baseStart_376322 baseEnd_376322 := by
    simpa [prefixWord, tailWord_376322, baseEnd_376322] using wordTrace_append hprefix tailTrace_376322
  have hstable : (prefixWord ++ tailWord_376322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376322).length < 2 ^ (prefixWord ++ tailWord_376322).sum := by decide
  have hdescent : baseEnd_376322 < baseStart_376322 := by decide
  rcases family_descends (prefixWord ++ tailWord_376322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376397 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 2]
def baseStart_376397 : Nat := 118140960795 + 376397 * 2 ^ 59
def prefixEnd_376397 : Nat := 4983230072969 + 3 ^ 40 * 376397 * 2
def baseEnd_376397 : Nat := 171797847031528069961323

theorem tailTrace_376397 : CollatzResearch.WordTrace tailWord_376397 prefixEnd_376397 171797847031528069961323 := by
  unfold tailWord_376397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728326417385427334839445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9152217611590284889892963 13728326417385427334839445)
  ·
    refine ⟨643515300814941906320599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13728326417385427334839445 643515300814941906320599)
    ·
      refine ⟨965272951222412859480899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643515300814941906320599 965272951222412859480899)
      ·
        refine ⟨1447909426833619289221349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965272951222412859480899 1447909426833619289221349)
        ·
          refine ⟨271483017531303616729003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1447909426833619289221349 271483017531303616729003)
          ·
            refine ⟨407224526296955425093505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271483017531303616729003 407224526296955425093505)
            ·
              refine ⟨305418394722716568820129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407224526296955425093505 305418394722716568820129)
              ·
                refine ⟨229063796042037426615097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305418394722716568820129 229063796042037426615097)
                ·
                  refine ⟨171797847031528069961323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229063796042037426615097 171797847031528069961323)
                  ·
                    rfl

theorem cell20_376397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_376397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376397 prefixEnd_376397 := by exact prefixLift 376397
  have htrace : WordTrace (prefixWord ++ tailWord_376397) baseStart_376397 baseEnd_376397 := by
    simpa [prefixWord, tailWord_376397, baseEnd_376397] using wordTrace_append hprefix tailTrace_376397
  have hstable : (prefixWord ++ tailWord_376397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376397).length < 2 ^ (prefixWord ++ tailWord_376397).sum := by decide
  have hdescent : baseEnd_376397 < baseStart_376397 := by decide
  rcases family_descends (prefixWord ++ tailWord_376397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376409 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_376409 : Nat := 118140960795 + 376409 * 2 ^ 59
def prefixEnd_376409 : Nat := 4983230072969 + 3 ^ 40 * 376409 * 2
def baseEnd_376409 : Nat := 171803324158509361561273

theorem tailTrace_376409 : CollatzResearch.WordTrace tailWord_376409 prefixEnd_376409 171803324158509361561273 := by
  unfold tailWord_376409
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728764093341953384276281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9152509395561302256184187 13728764093341953384276281)
  ·
    refine ⟨10296573070006465038207211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13728764093341953384276281 10296573070006465038207211)
    ·
      refine ⟨15444859605009697557310817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10296573070006465038207211 15444859605009697557310817)
      ·
        refine ⟨11583644703757273167983113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15444859605009697557310817 11583644703757273167983113)
        ·
          refine ⟨8687733527817954875987335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11583644703757273167983113 8687733527817954875987335)
          ·
            refine ⟨13031600291726932313981003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687733527817954875987335 13031600291726932313981003)
            ·
              refine ⟨19547400437590398470971505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13031600291726932313981003 19547400437590398470971505)
              ·
                refine ⟨14660550328192798853228629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19547400437590398470971505 14660550328192798853228629)
                ·
                  refine ⟨171803324158509361561273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14660550328192798853228629 171803324158509361561273)
                  ·
                    rfl

theorem cell20_376409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_376409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376409 prefixEnd_376409 := by exact prefixLift 376409
  have htrace : WordTrace (prefixWord ++ tailWord_376409) baseStart_376409 baseEnd_376409 := by
    simpa [prefixWord, tailWord_376409, baseEnd_376409] using wordTrace_append hprefix tailTrace_376409
  have hstable : (prefixWord ++ tailWord_376409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376409).length < 2 ^ (prefixWord ++ tailWord_376409).sum := by decide
  have hdescent : baseEnd_376409 < baseStart_376409 := by decide
  rcases family_descends (prefixWord ++ tailWord_376409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376412 : List Nat := [2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_376412 : Nat := 118140960795 + 376412 * 2 ^ 59
def prefixEnd_376412 : Nat := 4983230072969 + 3 ^ 40 * 376412 * 2
def baseEnd_376412 : Nat := 57268231146751561487087

theorem tailTrace_376412 : CollatzResearch.WordTrace tailWord_376412 prefixEnd_376412 57268231146751561487087 := by
  unfold tailWord_376412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864436756165542448317745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9152582341554056597756993 6864436756165542448317745)
  ·
    refine ⟨5148327567124156836238309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6864436756165542448317745 5148327567124156836238309)
    ·
      refine ⟨965311418835779406794683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5148327567124156836238309 965311418835779406794683)
      ·
        refine ⟨1447967128253669110192025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965311418835779406794683 1447967128253669110192025)
        ·
          refine ⟨1085975346190251832644019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447967128253669110192025 1085975346190251832644019)
          ·
            refine ⟨1628963019285377748966029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085975346190251832644019 1628963019285377748966029)
            ·
              refine ⟨610861132232016655862261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1628963019285377748966029 610861132232016655862261)
              ·
                refine ⟨57268231146751561487087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610861132232016655862261 57268231146751561487087)
                ·
                  rfl

theorem cell20_376412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_376412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376412 prefixEnd_376412 := by exact prefixLift 376412
  have htrace : WordTrace (prefixWord ++ tailWord_376412) baseStart_376412 baseEnd_376412 := by
    simpa [prefixWord, tailWord_376412, baseEnd_376412] using wordTrace_append hprefix tailTrace_376412
  have hstable : (prefixWord ++ tailWord_376412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376412).length < 2 ^ (prefixWord ++ tailWord_376412).sum := by decide
  have hdescent : baseEnd_376412 < baseStart_376412 := by decide
  rcases family_descends (prefixWord ++ tailWord_376412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376419 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_376419 : Nat := 118140960795 + 376419 * 2 ^ 59
def prefixEnd_376419 : Nat := 4983230072969 + 3 ^ 40 * 376419 * 2
def baseEnd_376419 : Nat := 171807888430993771227899

theorem tailTrace_376419 : CollatzResearch.WordTrace tailWord_376419 prefixEnd_376419 171807888430993771227899 := by
  unfold tailWord_376419
  simp only [CollatzResearch.WordTrace]
  refine ⟨13729128823305725092140311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9152752548870483394760207 13729128823305725092140311)
  ·
    refine ⟨20593693234958587638210467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13729128823305725092140311 20593693234958587638210467)
    ·
      refine ⟨30890539852437881457315701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20593693234958587638210467 30890539852437881457315701)
      ·
        refine ⟨2895988111166051386623347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30890539852437881457315701 2895988111166051386623347)
        ·
          refine ⟨4343982166749077079935021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895988111166051386623347 4343982166749077079935021)
          ·
            refine ⟨1628993312530903904975633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4343982166749077079935021 1628993312530903904975633)
            ·
              refine ⟨1221744984398177928731725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628993312530903904975633 1221744984398177928731725)
              ·
                refine ⟨458154369149316723274397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221744984398177928731725 458154369149316723274397)
                ·
                  refine ⟨171807888430993771227899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458154369149316723274397 171807888430993771227899)
                  ·
                    rfl

theorem cell20_376419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_376419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376419 prefixEnd_376419 := by exact prefixLift 376419
  have htrace : WordTrace (prefixWord ++ tailWord_376419) baseStart_376419 baseEnd_376419 := by
    simpa [prefixWord, tailWord_376419, baseEnd_376419] using wordTrace_append hprefix tailTrace_376419
  have hstable : (prefixWord ++ tailWord_376419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376419).length < 2 ^ (prefixWord ++ tailWord_376419).sum := by decide
  have hdescent : baseEnd_376419 < baseStart_376419 := by decide
  rcases family_descends (prefixWord ++ tailWord_376419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376426 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_376426 : Nat := 118140960795 + 376426 * 2 ^ 59
def prefixEnd_376426 : Nat := 4983230072969 + 3 ^ 40 * 376426 * 2
def baseEnd_376426 : Nat := 171811083421732857994537

theorem tailTrace_376426 : CollatzResearch.WordTrace tailWord_376426 prefixEnd_376426 171811083421732857994537 := by
  unfold tailWord_376426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432346033570091321911283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9152922756186910191763421 3432346033570091321911283)
  ·
    refine ⟨5148519050355136982866925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3432346033570091321911283 5148519050355136982866925)
    ·
      refine ⟨1930694643883176368575097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5148519050355136982866925 1930694643883176368575097)
      ·
        refine ⟨1448020982912382276431323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1930694643883176368575097 1448020982912382276431323)
        ·
          refine ⟨2172031474368573414646985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448020982912382276431323 2172031474368573414646985)
          ·
            refine ⟨1629023605776430060985239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2172031474368573414646985 1629023605776430060985239)
            ·
              refine ⟨2443535408664645091477859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629023605776430060985239 2443535408664645091477859)
              ·
                refine ⟨3665303112996967637216789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443535408664645091477859 3665303112996967637216789)
                ·
                  refine ⟨171811083421732857994537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3665303112996967637216789 171811083421732857994537)
                  ·
                    rfl

theorem cell20_376426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_376426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376426 prefixEnd_376426 := by exact prefixLift 376426
  have htrace : WordTrace (prefixWord ++ tailWord_376426) baseStart_376426 baseEnd_376426 := by
    simpa [prefixWord, tailWord_376426, baseEnd_376426] using wordTrace_append hprefix tailTrace_376426
  have hstable : (prefixWord ++ tailWord_376426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376426).length < 2 ^ (prefixWord ++ tailWord_376426).sum := by decide
  have hdescent : baseEnd_376426 < baseStart_376426 := by decide
  rcases family_descends (prefixWord ++ tailWord_376426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376429 : List Nat := [1, 5, 1, 1, 4, 1, 3, 4]
def baseStart_376429 : Nat := 118140960795 + 376429 * 2 ^ 59
def prefixEnd_376429 : Nat := 4983230072969 + 3 ^ 40 * 376429 * 2
def baseEnd_376429 : Nat := 57270817567826060298175

theorem tailTrace_376429 : CollatzResearch.WordTrace tailWord_376429 prefixEnd_376429 57270817567826060298175 := by
  unfold tailWord_376429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13729493553269496800004341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9152995702179664533336227 13729493553269496800004341)
  ·
    refine ⟨1287140020619015325000407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13729493553269496800004341 1287140020619015325000407)
    ·
      refine ⟨1930710030928522987500611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1287140020619015325000407 1930710030928522987500611)
      ·
        refine ⟨2896065046392784481250917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930710030928522987500611 2896065046392784481250917)
        ·
          refine ⟨543012196198647090234547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2896065046392784481250917 543012196198647090234547)
          ·
            refine ⟨814518294297970635351821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543012196198647090234547 814518294297970635351821)
            ·
              refine ⟨305444360361738988256933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 814518294297970635351821 305444360361738988256933)
              ·
                refine ⟨57270817567826060298175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305444360361738988256933 57270817567826060298175)
                ·
                  rfl

theorem cell20_376429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_376429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376429 prefixEnd_376429 := by exact prefixLift 376429
  have htrace : WordTrace (prefixWord ++ tailWord_376429) baseStart_376429 baseEnd_376429 := by
    simpa [prefixWord, tailWord_376429, baseEnd_376429] using wordTrace_append hprefix tailTrace_376429
  have hstable : (prefixWord ++ tailWord_376429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376429).length < 2 ^ (prefixWord ++ tailWord_376429).sum := by decide
  have hdescent : baseEnd_376429 < baseStart_376429 := by decide
  rcases family_descends (prefixWord ++ tailWord_376429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376443 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 2]
def baseStart_376443 : Nat := 118140960795 + 376443 * 2 ^ 59
def prefixEnd_376443 : Nat := 4983230072969 + 3 ^ 40 * 376443 * 2
def baseEnd_376443 : Nat := 171818842684956354427801

theorem tailTrace_376443 : CollatzResearch.WordTrace tailWord_376443 prefixEnd_376443 171818842684956354427801 := by
  unfold tailWord_376443
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730004175218777191013983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9153336116812518127342655 13730004175218777191013983)
  ·
    refine ⟨20595006262828165786520975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13730004175218777191013983 20595006262828165786520975)
    ·
      refine ⟨30892509394242248679781463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20595006262828165786520975 30892509394242248679781463)
      ·
        refine ⟨46338764091363373019672195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30892509394242248679781463 46338764091363373019672195)
        ·
          refine ⟨69508146137045059529508293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46338764091363373019672195 69508146137045059529508293)
          ·
            refine ⟨13032777400695948661782805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69508146137045059529508293 13032777400695948661782805)
            ·
              refine ⟨610911440657622593521069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13032777400695948661782805 610911440657622593521069)
              ·
                refine ⟨229091790246608472570401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610911440657622593521069 229091790246608472570401)
                ·
                  refine ⟨171818842684956354427801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229091790246608472570401 171818842684956354427801)
                  ·
                    rfl

theorem cell20_376443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 2].length) (baseStart_376443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376443 prefixEnd_376443 := by exact prefixLift 376443
  have htrace : WordTrace (prefixWord ++ tailWord_376443) baseStart_376443 baseEnd_376443 := by
    simpa [prefixWord, tailWord_376443, baseEnd_376443] using wordTrace_append hprefix tailTrace_376443
  have hstable : (prefixWord ++ tailWord_376443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376443).length < 2 ^ (prefixWord ++ tailWord_376443).sum := by decide
  have hdescent : baseEnd_376443 < baseStart_376443 := by decide
  rcases family_descends (prefixWord ++ tailWord_376443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376457 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_376457 : Nat := 118140960795 + 376457 * 2 ^ 59
def prefixEnd_376457 : Nat := 4983230072969 + 3 ^ 40 * 376457 * 2
def baseEnd_376457 : Nat := 171825232666434527961077

theorem tailTrace_376457 : CollatzResearch.WordTrace tailWord_376457 prefixEnd_376457 171825232666434527961077 := by
  unfold tailWord_376457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730514797168057582023625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9153676531445371721349083 13730514797168057582023625)
  ·
    refine ⟨10297886097876043186517719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13730514797168057582023625 10297886097876043186517719)
    ·
      refine ⟨15446829146814064779776579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10297886097876043186517719 15446829146814064779776579)
      ·
        refine ⟨23170243720221097169664869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15446829146814064779776579 23170243720221097169664869)
        ·
          refine ⟨4344420697541455719312163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23170243720221097169664869 4344420697541455719312163)
          ·
            refine ⟨6516631046312183578968245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344420697541455719312163 6516631046312183578968245)
            ·
              refine ⟨610934160591767210528273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6516631046312183578968245 610934160591767210528273)
              ·
                refine ⟨458200620443825407896205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610934160591767210528273 458200620443825407896205)
                ·
                  refine ⟨171825232666434527961077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458200620443825407896205 171825232666434527961077)
                  ·
                    rfl

theorem cell20_376457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_376457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376457 prefixEnd_376457 := by exact prefixLift 376457
  have htrace : WordTrace (prefixWord ++ tailWord_376457) baseStart_376457 baseEnd_376457 := by
    simpa [prefixWord, tailWord_376457, baseEnd_376457] using wordTrace_append hprefix tailTrace_376457
  have hstable : (prefixWord ++ tailWord_376457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376457).length < 2 ^ (prefixWord ++ tailWord_376457).sum := by decide
  have hdescent : baseEnd_376457 < baseStart_376457 := by decide
  rcases family_descends (prefixWord ++ tailWord_376457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376494 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_376494 : Nat := 118140960795 + 376494 * 2 ^ 59
def prefixEnd_376494 : Nat := 4983230072969 + 3 ^ 40 * 376494 * 2
def baseEnd_376494 : Nat := 171842120474626843727593

theorem tailTrace_376494 : CollatzResearch.WordTrace tailWord_376494 prefixEnd_376494 171842120474626843727593 := by
  unfold tailWord_376494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716483037254251612640067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9154576198689341934080357 1716483037254251612640067)
  ·
    refine ⟨2574724555881377418960101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1716483037254251612640067 2574724555881377418960101)
    ·
      refine ⟨482760854227758266055019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2574724555881377418960101 482760854227758266055019)
      ·
        refine ⟨724141281341637399082529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482760854227758266055019 724141281341637399082529)
        ·
          refine ⟨543105961006228049311897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724141281341637399082529 543105961006228049311897)
          ·
            refine ⟨407329470754671036983923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543105961006228049311897 407329470754671036983923)
            ·
              refine ⟨610994206132006555475885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407329470754671036983923 610994206132006555475885)
              ·
                refine ⟨229122827299502458303457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610994206132006555475885 229122827299502458303457)
                ·
                  refine ⟨171842120474626843727593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229122827299502458303457 171842120474626843727593)
                  ·
                    rfl

theorem cell20_376494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_376494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376494 prefixEnd_376494 := by exact prefixLift 376494
  have htrace : WordTrace (prefixWord ++ tailWord_376494) baseStart_376494 baseEnd_376494 := by
    simpa [prefixWord, tailWord_376494, baseEnd_376494] using wordTrace_append hprefix tailTrace_376494
  have hstable : (prefixWord ++ tailWord_376494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376494).length < 2 ^ (prefixWord ++ tailWord_376494).sum := by decide
  have hdescent : baseEnd_376494 < baseStart_376494 := by decide
  rcases family_descends (prefixWord ++ tailWord_376494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376554 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_376554 : Nat := 118140960795 + 376554 * 2 ^ 59
def prefixEnd_376554 : Nat := 4983230072969 + 3 ^ 40 * 376554 * 2
def baseEnd_376554 : Nat := 171869506109533301727347

theorem tailTrace_376554 : CollatzResearch.WordTrace tailWord_376554 prefixEnd_376554 171869506109533301727347 := by
  unfold tailWord_376554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433513169454160787076179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9156035118544428765536477 3433513169454160787076179)
  ·
    refine ⟨5150269754181241180614269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3433513169454160787076179 5150269754181241180614269)
    ·
      refine ⟨1931351157817965442730351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5150269754181241180614269 1931351157817965442730351)
      ·
        refine ⟨2897026736726948164095527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931351157817965442730351 2897026736726948164095527)
        ·
          refine ⟨4345540105090422246143291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897026736726948164095527 4345540105090422246143291)
          ·
            refine ⟨6518310157635633369214937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345540105090422246143291 6518310157635633369214937)
            ·
              refine ⟨4888732618226725026911203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518310157635633369214937 4888732618226725026911203)
              ·
                refine ⟨7333098927340087540366805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888732618226725026911203 7333098927340087540366805)
                ·
                  refine ⟨171869506109533301727347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7333098927340087540366805 171869506109533301727347)
                  ·
                    rfl

theorem cell20_376554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_376554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376554 prefixEnd_376554 := by exact prefixLift 376554
  have htrace : WordTrace (prefixWord ++ tailWord_376554) baseStart_376554 baseEnd_376554 := by
    simpa [prefixWord, tailWord_376554, baseEnd_376554] using wordTrace_append hprefix tailTrace_376554
  have hstable : (prefixWord ++ tailWord_376554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376554).length < 2 ^ (prefixWord ++ tailWord_376554).sum := by decide
  have hdescent : baseEnd_376554 < baseStart_376554 := by decide
  rcases family_descends (prefixWord ++ tailWord_376554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376602 : List Nat := [3, 1, 1, 3, 2, 3, 3, 4]
def baseStart_376602 : Nat := 118140960795 + 376602 * 2 ^ 59
def prefixEnd_376602 : Nat := 4983230072969 + 3 ^ 40 * 376602 * 2
def baseEnd_376602 : Nat := 57297138205819489375717

theorem tailTrace_376602 : CollatzResearch.WordTrace tailWord_376602 prefixEnd_376602 57297138205819489375717 := by
  unfold tailWord_376602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433950845410686836513015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9157202254428498230701373 3433950845410686836513015)
  ·
    refine ⟨5150926268116030254769523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3433950845410686836513015 5150926268116030254769523)
    ·
      refine ⟨7726389402174045382154285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150926268116030254769523 7726389402174045382154285)
      ·
        refine ⟨2897396025815267018307857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7726389402174045382154285 2897396025815267018307857)
        ·
          refine ⟨2173047019361450263730893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897396025815267018307857 2173047019361450263730893)
          ·
            refine ⟨814892632260543848899085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2173047019361450263730893 814892632260543848899085)
            ·
              refine ⟨305584737097703943337157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 814892632260543848899085 305584737097703943337157)
              ·
                refine ⟨57297138205819489375717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305584737097703943337157 57297138205819489375717)
                ·
                  rfl

theorem cell20_376602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_376602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376602 prefixEnd_376602 := by exact prefixLift 376602
  have htrace : WordTrace (prefixWord ++ tailWord_376602) baseStart_376602 baseEnd_376602 := by
    simpa [prefixWord, tailWord_376602, baseEnd_376602] using wordTrace_append hprefix tailTrace_376602
  have hstable : (prefixWord ++ tailWord_376602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376602).length < 2 ^ (prefixWord ++ tailWord_376602).sum := by decide
  have hdescent : baseEnd_376602 < baseStart_376602 := by decide
  rcases family_descends (prefixWord ++ tailWord_376602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376612 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 2]
def baseStart_376612 : Nat := 118140960795 + 376612 * 2 ^ 59
def prefixEnd_376612 : Nat := 4983230072969 + 3 ^ 40 * 376612 * 2
def baseEnd_376612 : Nat := 171895978889942877793777

theorem tailTrace_376612 : CollatzResearch.WordTrace tailWord_376612 prefixEnd_376612 171895978889942877793777 := by
  unfold tailWord_376612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868084055803259526958045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9157445407737679369277393 6868084055803259526958045)
  ·
    refine ⟨2575531520926222322609267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6868084055803259526958045 2575531520926222322609267)
    ·
      refine ⟨3863297281389333483913901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575531520926222322609267 3863297281389333483913901)
      ·
        refine ⟨1448736480521000056467713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3863297281389333483913901 1448736480521000056467713)
        ·
          refine ⟨1086552360390750042350785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448736480521000056467713 1086552360390750042350785)
          ·
            refine ⟨814914270293062531763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086552360390750042350785 814914270293062531763089)
            ·
              refine ⟨611185702719796898822317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814914270293062531763089 611185702719796898822317)
              ·
                refine ⟨229194638519923837058369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611185702719796898822317 229194638519923837058369)
                ·
                  refine ⟨171895978889942877793777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229194638519923837058369 171895978889942877793777)
                  ·
                    rfl

theorem cell20_376612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_376612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376612 prefixEnd_376612 := by exact prefixLift 376612
  have htrace : WordTrace (prefixWord ++ tailWord_376612) baseStart_376612 baseEnd_376612 := by
    simpa [prefixWord, tailWord_376612, baseEnd_376612] using wordTrace_append hprefix tailTrace_376612
  have hstable : (prefixWord ++ tailWord_376612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376612).length < 2 ^ (prefixWord ++ tailWord_376612).sum := by decide
  have hdescent : baseEnd_376612 < baseStart_376612 := by decide
  rcases family_descends (prefixWord ++ tailWord_376612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376622 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_376622 : Nat := 118140960795 + 376622 * 2 ^ 59
def prefixEnd_376622 : Nat := 4983230072969 + 3 ^ 40 * 376622 * 2
def baseEnd_376622 : Nat := 171900543162427287460403

theorem tailTrace_376622 : CollatzResearch.WordTrace tailWord_376622 prefixEnd_376622 171900543162427287460403 := by
  unfold tailWord_376622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717066605196286345222515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9157688561046860507853413 1717066605196286345222515)
  ·
    refine ⟨2575599907794429517833773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717066605196286345222515 2575599907794429517833773)
    ·
      refine ⟨965849965422911069187665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2575599907794429517833773 965849965422911069187665)
      ·
        refine ⟨724387474067183301890749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965849965422911069187665 724387474067183301890749)
        ·
          refine ⟨271645302775193738209031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 724387474067183301890749 271645302775193738209031)
          ·
            refine ⟨407467954162790607313547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271645302775193738209031 407467954162790607313547)
            ·
              refine ⟨611201931244185910970321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407467954162790607313547 611201931244185910970321)
              ·
                refine ⟨458401448433139433227741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611201931244185910970321 458401448433139433227741)
                ·
                  refine ⟨171900543162427287460403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458401448433139433227741 171900543162427287460403)
                  ·
                    rfl

theorem cell20_376622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_376622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376622 prefixEnd_376622 := by exact prefixLift 376622
  have htrace : WordTrace (prefixWord ++ tailWord_376622) baseStart_376622 baseEnd_376622 := by
    simpa [prefixWord, tailWord_376622, baseEnd_376622] using wordTrace_append hprefix tailTrace_376622
  have hstable : (prefixWord ++ tailWord_376622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376622).length < 2 ^ (prefixWord ++ tailWord_376622).sum := by decide
  have hdescent : baseEnd_376622 < baseStart_376622 := by decide
  rcases family_descends (prefixWord ++ tailWord_376622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376626 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_376626 : Nat := 118140960795 + 376626 * 2 ^ 59
def prefixEnd_376626 : Nat := 4983230072969 + 3 ^ 40 * 376626 * 2
def baseEnd_376626 : Nat := 171902368871421051327053

theorem tailTrace_376626 : CollatzResearch.WordTrace tailWord_376626 prefixEnd_376626 171902368871421051327053 := by
  unfold tailWord_376626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434169683388949861231433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9157785822370532963283821 3434169683388949861231433)
  ·
    refine ⟨2575627262541712395923575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3434169683388949861231433 2575627262541712395923575)
    ·
      refine ⟨3863440893812568593885363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575627262541712395923575 3863440893812568593885363)
      ·
        refine ⟨5795161340718852890828045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863440893812568593885363 5795161340718852890828045)
        ·
          refine ⟨2173185502769569834060517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5795161340718852890828045 2173185502769569834060517)
          ·
            refine ⟨407472281769294343886347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2173185502769569834060517 407472281769294343886347)
            ·
              refine ⟨611208422653941515829521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407472281769294343886347 611208422653941515829521)
              ·
                refine ⟨458406316990456136872141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611208422653941515829521 458406316990456136872141)
                ·
                  refine ⟨171902368871421051327053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458406316990456136872141 171902368871421051327053)
                  ·
                    rfl

theorem cell20_376626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_376626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376626 prefixEnd_376626 := by exact prefixLift 376626
  have htrace : WordTrace (prefixWord ++ tailWord_376626) baseStart_376626 baseEnd_376626 := by
    simpa [prefixWord, tailWord_376626, baseEnd_376626] using wordTrace_append hprefix tailTrace_376626
  have hstable : (prefixWord ++ tailWord_376626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376626).length < 2 ^ (prefixWord ++ tailWord_376626).sum := by decide
  have hdescent : baseEnd_376626 < baseStart_376626 := by decide
  rcases family_descends (prefixWord ++ tailWord_376626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376661 : List Nat := [1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_376661 : Nat := 118140960795 + 376661 * 2 ^ 59
def prefixEnd_376661 : Nat := 4983230072969 + 3 ^ 40 * 376661 * 2
def baseEnd_376661 : Nat := 57306114608372161720081

theorem tailTrace_376661 : CollatzResearch.WordTrace tailWord_376661 prefixEnd_376661 57306114608372161720081 := by
  unfold tailWord_376661
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737955288429000422449837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9158636858952666948299891 13737955288429000422449837)
  ·
    refine ⟨5151733233160875158418689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13737955288429000422449837 5151733233160875158418689)
    ·
      refine ⟨3863799924870656368814017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5151733233160875158418689 3863799924870656368814017)
      ·
        refine ⟨2897849943652992276610513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3863799924870656368814017 2897849943652992276610513)
        ·
          refine ⟨2173387457739744207457885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897849943652992276610513 2173387457739744207457885)
          ·
            refine ⟨815020296652404077796707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2173387457739744207457885 815020296652404077796707)
            ·
              refine ⟨1222530444978606116695061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815020296652404077796707 1222530444978606116695061)
              ·
                refine ⟨57306114608372161720081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1222530444978606116695061 57306114608372161720081)
                ·
                  rfl

theorem cell20_376661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_376661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376661 prefixEnd_376661 := by exact prefixLift 376661
  have htrace : WordTrace (prefixWord ++ tailWord_376661) baseStart_376661 baseEnd_376661 := by
    simpa [prefixWord, tailWord_376661, baseEnd_376661] using wordTrace_append hprefix tailTrace_376661
  have hstable : (prefixWord ++ tailWord_376661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376661).length < 2 ^ (prefixWord ++ tailWord_376661).sum := by decide
  have hdescent : baseEnd_376661 < baseStart_376661 := by decide
  rcases family_descends (prefixWord ++ tailWord_376661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376671 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 2]
def baseStart_376671 : Nat := 118140960795 + 376671 * 2 ^ 59
def prefixEnd_376671 : Nat := 4983230072969 + 3 ^ 40 * 376671 * 2
def baseEnd_376671 : Nat := 171922908097600894826869

theorem tailTrace_376671 : CollatzResearch.WordTrace tailWord_376671 prefixEnd_376671 171922908097600894826869 := by
  unfold tailWord_376671
  simp only [CollatzResearch.WordTrace]
  refine ⟨13738320018392772130313867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9158880012261848086875911 13738320018392772130313867)
  ·
    refine ⟨20607480027589158195470801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13738320018392772130313867 20607480027589158195470801)
    ·
      refine ⟨15455610020691868646603101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20607480027589158195470801 15455610020691868646603101)
      ·
        refine ⟨5795853757759450742476163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15455610020691868646603101 5795853757759450742476163)
        ·
          refine ⟨8693780636639176113714245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795853757759450742476163 8693780636639176113714245)
          ·
            refine ⟨1630083869369845521321421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8693780636639176113714245 1630083869369845521321421)
            ·
              refine ⟨611281451013692070495533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1630083869369845521321421 611281451013692070495533)
              ·
                refine ⟨229230544130134526435825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611281451013692070495533 229230544130134526435825)
                ·
                  refine ⟨171922908097600894826869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229230544130134526435825 171922908097600894826869)
                  ·
                    rfl

theorem cell20_376671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 2].length) (baseStart_376671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376671 prefixEnd_376671 := by exact prefixLift 376671
  have htrace : WordTrace (prefixWord ++ tailWord_376671) baseStart_376671 baseEnd_376671 := by
    simpa [prefixWord, tailWord_376671, baseEnd_376671] using wordTrace_append hprefix tailTrace_376671
  have hstable : (prefixWord ++ tailWord_376671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376671).length < 2 ^ (prefixWord ++ tailWord_376671).sum := by decide
  have hdescent : baseEnd_376671 < baseStart_376671 := by decide
  rcases family_descends (prefixWord ++ tailWord_376671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376713 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_376713 : Nat := 118140960795 + 376713 * 2 ^ 59
def prefixEnd_376713 : Nat := 4983230072969 + 3 ^ 40 * 376713 * 2
def baseEnd_376713 : Nat := 171942078042035415426697

theorem tailTrace_376713 : CollatzResearch.WordTrace tailWord_376713 prefixEnd_376713 171942078042035415426697 := by
  unfold tailWord_376713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13739851884240613303342793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9159901256160408868895195 13739851884240613303342793)
  ·
    refine ⟨10304888913180459977507095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13739851884240613303342793 10304888913180459977507095)
    ·
      refine ⟨15457333369770689966260643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10304888913180459977507095 15457333369770689966260643)
      ·
        refine ⟨23186000054656034949390965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15457333369770689966260643 23186000054656034949390965)
        ·
          refine ⟨2173687505124003276505403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23186000054656034949390965 2173687505124003276505403)
          ·
            refine ⟨3260531257686004914758105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173687505124003276505403 3260531257686004914758105)
            ·
              refine ⟨2445398443264503686068579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260531257686004914758105 2445398443264503686068579)
              ·
                refine ⟨3668097664896755529102869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445398443264503686068579 3668097664896755529102869)
                ·
                  refine ⟨171942078042035415426697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3668097664896755529102869 171942078042035415426697)
                  ·
                    rfl

theorem cell20_376713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_376713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376713 prefixEnd_376713 := by exact prefixLift 376713
  have htrace : WordTrace (prefixWord ++ tailWord_376713) baseStart_376713 baseEnd_376713 := by
    simpa [prefixWord, tailWord_376713, baseEnd_376713] using wordTrace_append hprefix tailTrace_376713
  have hstable : (prefixWord ++ tailWord_376713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376713).length < 2 ^ (prefixWord ++ tailWord_376713).sum := by decide
  have hdescent : baseEnd_376713 < baseStart_376713 := by decide
  rcases family_descends (prefixWord ++ tailWord_376713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376737 : List Nat := [1, 2, 3, 4, 2, 8]
def baseStart_376737 : Nat := 118140960795 + 376737 * 2 ^ 59
def prefixEnd_376737 : Nat := 4983230072969 + 3 ^ 40 * 376737 * 2
def baseEnd_376737 : Nat := 6368630825777703652837

theorem tailTrace_376737 : CollatzResearch.WordTrace tailWord_376737 prefixEnd_376737 6368630825777703652837 := by
  unfold tailWord_376737
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740727236153665402216465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9160484824102443601477643 13740727236153665402216465)
  ·
    refine ⟨10305545427115249051662349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13740727236153665402216465 10305545427115249051662349)
    ·
      refine ⟨3864579535168218394373381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10305545427115249051662349 3864579535168218394373381)
      ·
        refine ⟨724608662844040948945009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3864579535168218394373381 724608662844040948945009)
        ·
          refine ⟨543456497133030711708757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724608662844040948945009 543456497133030711708757)
          ·
            refine ⟨6368630825777703652837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 543456497133030711708757 6368630825777703652837)
            ·
              rfl

theorem cell20_376737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 8].length) (baseStart_376737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376737 prefixEnd_376737 := by exact prefixLift 376737
  have htrace : WordTrace (prefixWord ++ tailWord_376737) baseStart_376737 baseEnd_376737 := by
    simpa [prefixWord, tailWord_376737, baseEnd_376737] using wordTrace_append hprefix tailTrace_376737
  have hstable : (prefixWord ++ tailWord_376737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376737).length < 2 ^ (prefixWord ++ tailWord_376737).sum := by decide
  have hdescent : baseEnd_376737 < baseStart_376737 := by decide
  rcases family_descends (prefixWord ++ tailWord_376737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376743 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 2]
def baseStart_376743 : Nat := 118140960795 + 376743 * 2 ^ 59
def prefixEnd_376743 : Nat := 4983230072969 + 3 ^ 40 * 376743 * 2
def baseEnd_376743 : Nat := 171955770859488644426575

theorem tailTrace_376743 : CollatzResearch.WordTrace tailWord_376743 prefixEnd_376743 171955770859488644426575 := by
  unfold tailWord_376743
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740946074131928426934883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9160630716087952284623255 13740946074131928426934883)
  ·
    refine ⟨20611419111197892640402325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13740946074131928426934883 20611419111197892640402325)
    ·
      refine ⟨966160270837401217518859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20611419111197892640402325 966160270837401217518859)
      ·
        refine ⟨1449240406256101826278289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966160270837401217518859 1449240406256101826278289)
        ·
          refine ⟨1086930304692076369708717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1449240406256101826278289 1086930304692076369708717)
          ·
            refine ⟨407598864259528638640769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1086930304692076369708717 407598864259528638640769)
            ·
              refine ⟨305699148194646478980577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407598864259528638640769 305699148194646478980577)
              ·
                refine ⟨229274361145984859235433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305699148194646478980577 229274361145984859235433)
                ·
                  refine ⟨171955770859488644426575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229274361145984859235433 171955770859488644426575)
                  ·
                    rfl

theorem cell20_376743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 2].length) (baseStart_376743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376743 prefixEnd_376743 := by exact prefixLift 376743
  have htrace : WordTrace (prefixWord ++ tailWord_376743) baseStart_376743 baseEnd_376743 := by
    simpa [prefixWord, tailWord_376743, baseEnd_376743] using wordTrace_append hprefix tailTrace_376743
  have hstable : (prefixWord ++ tailWord_376743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376743).length < 2 ^ (prefixWord ++ tailWord_376743).sum := by decide
  have hdescent : baseEnd_376743 < baseStart_376743 := by decide
  rcases family_descends (prefixWord ++ tailWord_376743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376751 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_376751 : Nat := 118140960795 + 376751 * 2 ^ 59
def prefixEnd_376751 : Nat := 4983230072969 + 3 ^ 40 * 376751 * 2
def baseEnd_376751 : Nat := 171959422277476172159875

theorem tailTrace_376751 : CollatzResearch.WordTrace tailWord_376751 prefixEnd_376751 171959422277476172159875 := by
  unfold tailWord_376751
  simp only [CollatzResearch.WordTrace]
  refine ⟨13741237858102945793226107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9160825238735297195484071 13741237858102945793226107)
  ·
    refine ⟨20611856787154418689839161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13741237858102945793226107 20611856787154418689839161)
    ·
      refine ⟨15458892590365814017379371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20611856787154418689839161 15458892590365814017379371)
      ·
        refine ⟨23188338885548721026069057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15458892590365814017379371 23188338885548721026069057)
        ·
          refine ⟨17391254164161540769551793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23188338885548721026069057 17391254164161540769551793)
          ·
            refine ⟨13043440623121155577163845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17391254164161540769551793 13043440623121155577163845)
            ·
              refine ⟨2445645116835216670718221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13043440623121155577163845 2445645116835216670718221)
              ·
                refine ⟨917116918813206251519333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2445645116835216670718221 917116918813206251519333)
                ·
                  refine ⟨171959422277476172159875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917116918813206251519333 171959422277476172159875)
                  ·
                    rfl

theorem cell20_376751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_376751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376751 prefixEnd_376751 := by exact prefixLift 376751
  have htrace : WordTrace (prefixWord ++ tailWord_376751) baseStart_376751 baseEnd_376751 := by
    simpa [prefixWord, tailWord_376751, baseEnd_376751] using wordTrace_append hprefix tailTrace_376751
  have hstable : (prefixWord ++ tailWord_376751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376751).length < 2 ^ (prefixWord ++ tailWord_376751).sum := by decide
  have hdescent : baseEnd_376751 < baseStart_376751 := by decide
  rcases family_descends (prefixWord ++ tailWord_376751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376782 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_376782 : Nat := 118140960795 + 376782 * 2 ^ 59
def prefixEnd_376782 : Nat := 4983230072969 + 3 ^ 40 * 376782 * 2
def baseEnd_376782 : Nat := 171973571522177842126415

theorem tailTrace_376782 : CollatzResearch.WordTrace tailWord_376782 prefixEnd_376782 171973571522177842126415 := by
  unfold tailWord_376782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717796065123829760950575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9161579013993758725069733 1717796065123829760950575)
  ·
    refine ⟨2576694097685744641425863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717796065123829760950575 2576694097685744641425863)
    ·
      refine ⟨3865041146528616962138795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576694097685744641425863 3865041146528616962138795)
      ·
        refine ⟨5797561719792925443208193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865041146528616962138795 5797561719792925443208193)
        ·
          refine ⟨4348171289844694082406145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5797561719792925443208193 4348171289844694082406145)
          ·
            refine ⟨3261128467383520561804609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4348171289844694082406145 3261128467383520561804609)
            ·
              refine ⟨2445846350537640421353457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261128467383520561804609 2445846350537640421353457)
              ·
                refine ⟨1834384762903230316015093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445846350537640421353457 1834384762903230316015093)
                ·
                  refine ⟨171973571522177842126415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1834384762903230316015093 171973571522177842126415)
                  ·
                    rfl

theorem cell20_376782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_376782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376782 prefixEnd_376782 := by exact prefixLift 376782
  have htrace : WordTrace (prefixWord ++ tailWord_376782) baseStart_376782 baseEnd_376782 := by
    simpa [prefixWord, tailWord_376782, baseEnd_376782] using wordTrace_append hprefix tailTrace_376782
  have hstable : (prefixWord ++ tailWord_376782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376782).length < 2 ^ (prefixWord ++ tailWord_376782).sum := by decide
  have hdescent : baseEnd_376782 < baseStart_376782 := by decide
  rcases family_descends (prefixWord ++ tailWord_376782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376799 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_376799 : Nat := 118140960795 + 376799 * 2 ^ 59
def prefixEnd_376799 : Nat := 4983230072969 + 3 ^ 40 * 376799 * 2
def baseEnd_376799 : Nat := 171981330785401338559679

theorem tailTrace_376799 : CollatzResearch.WordTrace tailWord_376799 prefixEnd_376799 171981330785401338559679 := by
  unfold tailWord_376799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742988561929049990973451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9161992374619366660648967 13742988561929049990973451)
  ·
    refine ⟨20614482842893574986460177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13742988561929049990973451 20614482842893574986460177)
    ·
      refine ⟨15460862132170181239845133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20614482842893574986460177 15460862132170181239845133)
      ·
        refine ⟨5797823299563817964941925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15460862132170181239845133 5797823299563817964941925)
        ·
          refine ⟨1087091868668215868426611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5797823299563817964941925 1087091868668215868426611)
          ·
            refine ⟨1630637803002323802639917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087091868668215868426611 1630637803002323802639917)
            ·
              refine ⟨611489176125871425989969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1630637803002323802639917 611489176125871425989969)
              ·
                refine ⟨458616882094403569492477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611489176125871425989969 458616882094403569492477)
                ·
                  refine ⟨171981330785401338559679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458616882094403569492477 171981330785401338559679)
                  ·
                    rfl

theorem cell20_376799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_376799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376799 prefixEnd_376799 := by exact prefixLift 376799
  have htrace : WordTrace (prefixWord ++ tailWord_376799) baseStart_376799 baseEnd_376799 := by
    simpa [prefixWord, tailWord_376799, baseEnd_376799] using wordTrace_append hprefix tailTrace_376799
  have hstable : (prefixWord ++ tailWord_376799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376799).length < 2 ^ (prefixWord ++ tailWord_376799).sum := by decide
  have hdescent : baseEnd_376799 < baseStart_376799 := by decide
  rcases family_descends (prefixWord ++ tailWord_376799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376802 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_376802 : Nat := 118140960795 + 376802 * 2 ^ 59
def prefixEnd_376802 : Nat := 4983230072969 + 3 ^ 40 * 376802 * 2
def baseEnd_376802 : Nat := 171982700067146661459667

theorem tailTrace_376802 : CollatzResearch.WordTrace tailWord_376802 prefixEnd_376802 171982700067146661459667 := by
  unfold tailWord_376802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435774495229545375833165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9162065320612121002221773 3435774495229545375833165)
  ·
    refine ⟨1288415435711079515937437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3435774495229545375833165 1288415435711079515937437)
    ·
      refine ⟨483155788391654818476539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1288415435711079515937437 483155788391654818476539)
      ·
        refine ⟨724733682587482227714809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483155788391654818476539 724733682587482227714809)
        ·
          refine ⟨543550261940611670786107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724733682587482227714809 543550261940611670786107)
          ·
            refine ⟨815325392910917506179161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543550261940611670786107 815325392910917506179161)
            ·
              refine ⟨611494044683188129634371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815325392910917506179161 611494044683188129634371)
              ·
                refine ⟨917241067024782194451557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611494044683188129634371 917241067024782194451557)
                ·
                  refine ⟨171982700067146661459667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917241067024782194451557 171982700067146661459667)
                  ·
                    rfl

theorem cell20_376802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_376802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376802 prefixEnd_376802 := by exact prefixLift 376802
  have htrace : WordTrace (prefixWord ++ tailWord_376802) baseStart_376802 baseEnd_376802 := by
    simpa [prefixWord, tailWord_376802, baseEnd_376802] using wordTrace_append hprefix tailTrace_376802
  have hstable : (prefixWord ++ tailWord_376802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376802).length < 2 ^ (prefixWord ++ tailWord_376802).sum := by decide
  have hdescent : baseEnd_376802 < baseStart_376802 := by decide
  rcases family_descends (prefixWord ++ tailWord_376802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376827 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_376827 : Nat := 118140960795 + 376827 * 2 ^ 59
def prefixEnd_376827 : Nat := 4983230072969 + 3 ^ 40 * 376827 * 2
def baseEnd_376827 : Nat := 171994110748357685626231

theorem tailTrace_376827 : CollatzResearch.WordTrace tailWord_376827 prefixEnd_376827 171994110748357685626231 := by
  unfold tailWord_376827
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744009805827610772992735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9162673203885073848661823 13744009805827610772992735)
  ·
    refine ⟨20616014708741416159489103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13744009805827610772992735 20616014708741416159489103)
    ·
      refine ⟨30924022063112124239233655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20616014708741416159489103 30924022063112124239233655)
      ·
        refine ⟨46386033094668186358850483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30924022063112124239233655 46386033094668186358850483)
        ·
          refine ⟨69579049642002279538275725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46386033094668186358850483 69579049642002279538275725)
          ·
            refine ⟨26092143615750854826853397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69579049642002279538275725 26092143615750854826853397)
            ·
              refine ⟨1223069231988321320008753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26092143615750854826853397 1223069231988321320008753)
              ·
                refine ⟨917301923991240990006565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223069231988321320008753 917301923991240990006565)
                ·
                  refine ⟨171994110748357685626231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917301923991240990006565 171994110748357685626231)
                  ·
                    rfl

theorem cell20_376827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_376827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376827 prefixEnd_376827 := by exact prefixLift 376827
  have htrace : WordTrace (prefixWord ++ tailWord_376827) baseStart_376827 baseEnd_376827 := by
    simpa [prefixWord, tailWord_376827, baseEnd_376827] using wordTrace_append hprefix tailTrace_376827
  have hstable : (prefixWord ++ tailWord_376827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376827).length < 2 ^ (prefixWord ++ tailWord_376827).sum := by decide
  have hdescent : baseEnd_376827 < baseStart_376827 := by decide
  rcases family_descends (prefixWord ++ tailWord_376827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376830 : List Nat := [4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_376830 : Nat := 118140960795 + 376830 * 2 ^ 59
def prefixEnd_376830 : Nat := 4983230072969 + 3 ^ 40 * 376830 * 2
def baseEnd_376830 : Nat := 57331826676701002842073

theorem tailTrace_376830 : CollatzResearch.WordTrace tailWord_376830 prefixEnd_376830 57331826676701002842073 := by
  unfold tailWord_376830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718014903102092785668993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9162746149877828190234629 1718014903102092785668993)
  ·
    refine ⟨1288511177326569589251745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1718014903102092785668993 1288511177326569589251745)
    ·
      refine ⟨966383382994927191938809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1288511177326569589251745 966383382994927191938809)
      ·
        refine ⟨724787537246195393954107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 966383382994927191938809 724787537246195393954107)
        ·
          refine ⟨1087181305869293090931161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724787537246195393954107 1087181305869293090931161)
          ·
            refine ⟨815385979401969818198371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087181305869293090931161 815385979401969818198371)
            ·
              refine ⟨1223078969102954727297557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815385979401969818198371 1223078969102954727297557)
              ·
                refine ⟨57331826676701002842073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1223078969102954727297557 57331826676701002842073)
                ·
                  rfl

theorem cell20_376830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_376830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376830 prefixEnd_376830 := by exact prefixLift 376830
  have htrace : WordTrace (prefixWord ++ tailWord_376830) baseStart_376830 baseEnd_376830 := by
    simpa [prefixWord, tailWord_376830, baseEnd_376830] using wordTrace_append hprefix tailTrace_376830
  have hstable : (prefixWord ++ tailWord_376830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376830).length < 2 ^ (prefixWord ++ tailWord_376830).sum := by decide
  have hdescent : baseEnd_376830 < baseStart_376830 := by decide
  rcases family_descends (prefixWord ++ tailWord_376830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376836 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 2]
def baseStart_376836 : Nat := 118140960795 + 376836 * 2 ^ 59
def prefixEnd_376836 : Nat := 4983230072969 + 3 ^ 40 * 376836 * 2
def baseEnd_376836 : Nat := 171998218593593654326195

theorem tailTrace_376836 : CollatzResearch.WordTrace tailWord_376836 prefixEnd_376836 171998218593593654326195 := by
  unfold tailWord_376836
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872169031397502655035181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9162892041863336873380241 6872169031397502655035181)
  ·
    refine ⟨2577063386774063495638193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6872169031397502655035181 2577063386774063495638193)
    ·
      refine ⟨1932797540080547621728645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2577063386774063495638193 1932797540080547621728645)
      ·
        refine ⟨362399538765102679074121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1932797540080547621728645 362399538765102679074121)
        ·
          refine ⟨271799654073827009305591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362399538765102679074121 271799654073827009305591)
          ·
            refine ⟨407699481110740513958387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271799654073827009305591 407699481110740513958387)
            ·
              refine ⟨611549221666110770937581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407699481110740513958387 611549221666110770937581)
              ·
                refine ⟨229330958124791539101593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611549221666110770937581 229330958124791539101593)
                ·
                  refine ⟨171998218593593654326195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229330958124791539101593 171998218593593654326195)
                  ·
                    rfl

theorem cell20_376836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_376836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376836 prefixEnd_376836 := by exact prefixLift 376836
  have htrace : WordTrace (prefixWord ++ tailWord_376836) baseStart_376836 baseEnd_376836 := by
    simpa [prefixWord, tailWord_376836, baseEnd_376836] using wordTrace_append hprefix tailTrace_376836
  have hstable : (prefixWord ++ tailWord_376836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376836).length < 2 ^ (prefixWord ++ tailWord_376836).sum := by decide
  have hdescent : baseEnd_376836 < baseStart_376836 := by decide
  rcases family_descends (prefixWord ++ tailWord_376836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376858 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_376858 : Nat := 118140960795 + 376858 * 2 ^ 59
def prefixEnd_376858 : Nat := 4983230072969 + 3 ^ 40 * 376858 * 2
def baseEnd_376858 : Nat := 172008259993059355592771

theorem tailTrace_376858 : CollatzResearch.WordTrace tailWord_376858 prefixEnd_376858 172008259993059355592771 := by
  unfold tailWord_376858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436285117178825766842807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9163426979143535378247485 3436285117178825766842807)
  ·
    refine ⟨5154427675768238650264211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3436285117178825766842807 5154427675768238650264211)
    ·
      refine ⟨7731641513652357975396317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5154427675768238650264211 7731641513652357975396317)
      ·
        refine ⟨2899365567619634240773619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7731641513652357975396317 2899365567619634240773619)
        ·
          refine ⟨4349048351429451361160429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899365567619634240773619 4349048351429451361160429)
          ·
            refine ⟨1630893131786044260435161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4349048351429451361160429 1630893131786044260435161)
            ·
              refine ⟨1223169848839533195326371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630893131786044260435161 1223169848839533195326371)
              ·
                refine ⟨1834754773259299792989557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223169848839533195326371 1834754773259299792989557)
                ·
                  refine ⟨172008259993059355592771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1834754773259299792989557 172008259993059355592771)
                  ·
                    rfl

theorem cell20_376858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_376858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376858 prefixEnd_376858 := by exact prefixLift 376858
  have htrace : WordTrace (prefixWord ++ tailWord_376858) baseStart_376858 baseEnd_376858 := by
    simpa [prefixWord, tailWord_376858, baseEnd_376858] using wordTrace_append hprefix tailTrace_376858
  have hstable : (prefixWord ++ tailWord_376858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376858).length < 2 ^ (prefixWord ++ tailWord_376858).sum := by decide
  have hdescent : baseEnd_376858 < baseStart_376858 := by decide
  rcases family_descends (prefixWord ++ tailWord_376858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376861 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 4]
def baseStart_376861 : Nat := 118140960795 + 376861 * 2 ^ 59
def prefixEnd_376861 : Nat := 4983230072969 + 3 ^ 40 * 376861 * 2
def baseEnd_376861 : Nat := 172009629274804678492759

theorem tailTrace_376861 : CollatzResearch.WordTrace tailWord_376861 prefixEnd_376861 172009629274804678492759 := by
  unfold tailWord_376861
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745249887704434579730437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9163499925136289719820291 13745249887704434579730437)
  ·
    refine ⟨2577234353944581483699457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13745249887704434579730437 2577234353944581483699457)
    ·
      refine ⟨1932925765458436112774593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2577234353944581483699457 1932925765458436112774593)
      ·
        refine ⟨1449694324093827084580945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1932925765458436112774593 1449694324093827084580945)
        ·
          refine ⟨1087270743070370313435709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1449694324093827084580945 1087270743070370313435709)
          ·
            refine ⟨407726528651388867538391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1087270743070370313435709 407726528651388867538391)
            ·
              refine ⟨611589792977083301307587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407726528651388867538391 611589792977083301307587)
              ·
                refine ⟨917384689465624951961381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611589792977083301307587 917384689465624951961381)
                ·
                  refine ⟨172009629274804678492759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917384689465624951961381 172009629274804678492759)
                  ·
                    rfl

theorem cell20_376861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_376861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376861 prefixEnd_376861 := by exact prefixLift 376861
  have htrace : WordTrace (prefixWord ++ tailWord_376861) baseStart_376861 baseEnd_376861 := by
    simpa [prefixWord, tailWord_376861, baseEnd_376861] using wordTrace_append hprefix tailTrace_376861
  have hstable : (prefixWord ++ tailWord_376861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376861).length < 2 ^ (prefixWord ++ tailWord_376861).sum := by decide
  have hdescent : baseEnd_376861 < baseStart_376861 := by decide
  rcases family_descends (prefixWord ++ tailWord_376861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376868 : List Nat := [2, 3, 1, 4, 2, 1, 2, 5]
def baseStart_376868 : Nat := 118140960795 + 376868 * 2 ^ 59
def prefixEnd_376868 : Nat := 4983230072969 + 3 ^ 40 * 376868 * 2
def baseEnd_376868 : Nat := 57337608088514588419799

theorem tailTrace_376868 : CollatzResearch.WordTrace tailWord_376868 prefixEnd_376868 57337608088514588419799 := by
  unfold tailWord_376868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872752599339537387617629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9163670132452716516823505 6872752599339537387617629)
  ·
    refine ⟨2577282224752326520356611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6872752599339537387617629 2577282224752326520356611)
    ·
      refine ⟨3865923337128489780534917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577282224752326520356611 3865923337128489780534917)
      ·
        refine ⟨724860625711591833850297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3865923337128489780534917 724860625711591833850297)
        ·
          refine ⟨543645469283693875387723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724860625711591833850297 543645469283693875387723)
          ·
            refine ⟨815468203925540813081585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543645469283693875387723 815468203925540813081585)
            ·
              refine ⟨611601152944155609811189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815468203925540813081585 611601152944155609811189)
              ·
                refine ⟨57337608088514588419799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 611601152944155609811189 57337608088514588419799)
                ·
                  rfl

theorem cell20_376868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_376868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376868 prefixEnd_376868 := by exact prefixLift 376868
  have htrace : WordTrace (prefixWord ++ tailWord_376868) baseStart_376868 baseEnd_376868 := by
    simpa [prefixWord, tailWord_376868, baseEnd_376868] using wordTrace_append hprefix tailTrace_376868
  have hstable : (prefixWord ++ tailWord_376868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376868).length < 2 ^ (prefixWord ++ tailWord_376868).sum := by decide
  have hdescent : baseEnd_376868 < baseStart_376868 := by decide
  rcases family_descends (prefixWord ++ tailWord_376868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376879 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_376879 : Nat := 118140960795 + 376879 * 2 ^ 59
def prefixEnd_376879 : Nat := 4983230072969 + 3 ^ 40 * 376879 * 2
def baseEnd_376879 : Nat := 172017844965276615892685

theorem tailTrace_376879 : CollatzResearch.WordTrace tailWord_376879 prefixEnd_376879 172017844965276615892685 := by
  unfold tailWord_376879
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745906401639223653885691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9163937601092815769257127 13745906401639223653885691)
  ·
    refine ⟨20618859602458835480828537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13745906401639223653885691 20618859602458835480828537)
    ·
      refine ⟨15464144701844126610621403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20618859602458835480828537 15464144701844126610621403)
      ·
        refine ⟨23196217052766189915932105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15464144701844126610621403 23196217052766189915932105)
        ·
          refine ⟨17397162789574642436949079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23196217052766189915932105 17397162789574642436949079)
          ·
            refine ⟨26095744184361963655423619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17397162789574642436949079 26095744184361963655423619)
            ·
              refine ⟨39143616276542945483135429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26095744184361963655423619 39143616276542945483135429)
              ·
                refine ⟨7339428051851802278087893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39143616276542945483135429 7339428051851802278087893)
                ·
                  refine ⟨172017844965276615892685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7339428051851802278087893 172017844965276615892685)
                  ·
                    rfl

theorem cell20_376879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_376879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376879 prefixEnd_376879 := by exact prefixLift 376879
  have htrace : WordTrace (prefixWord ++ tailWord_376879) baseStart_376879 baseEnd_376879 := by
    simpa [prefixWord, tailWord_376879, baseEnd_376879] using wordTrace_append hprefix tailTrace_376879
  have hstable : (prefixWord ++ tailWord_376879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376879).length < 2 ^ (prefixWord ++ tailWord_376879).sum := by decide
  have hdescent : baseEnd_376879 < baseStart_376879 := by decide
  rcases family_descends (prefixWord ++ tailWord_376879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376910 : List Nat := [4, 1, 1, 1, 1, 12]
def baseStart_376910 : Nat := 118140960795 + 376910 * 2 ^ 59
def prefixEnd_376910 : Nat := 4983230072969 + 3 ^ 40 * 376910 * 2
def baseEnd_376910 : Nat := 6371555341110306883675

theorem tailTrace_376910 : CollatzResearch.WordTrace tailWord_376910 prefixEnd_376910 6371555341110306883675 := by
  unfold tailWord_376910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718379633065864493533023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9164691376351277298842789 1718379633065864493533023)
  ·
    refine ⟨2577569449598796740299535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1718379633065864493533023 2577569449598796740299535)
    ·
      refine ⟨3866354174398195110449303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577569449598796740299535 3866354174398195110449303)
      ·
        refine ⟨5799531261597292665673955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866354174398195110449303 5799531261597292665673955)
        ·
          refine ⟨8699296892395938998510933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799531261597292665673955 8699296892395938998510933)
          ·
            refine ⟨6371555341110306883675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8699296892395938998510933 6371555341110306883675)
            ·
              rfl

theorem cell20_376910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 12].length) (baseStart_376910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376910 prefixEnd_376910 := by exact prefixLift 376910
  have htrace : WordTrace (prefixWord ++ tailWord_376910) baseStart_376910 baseEnd_376910 := by
    simpa [prefixWord, tailWord_376910, baseEnd_376910] using wordTrace_append hprefix tailTrace_376910
  have hstable : (prefixWord ++ tailWord_376910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376910).length < 2 ^ (prefixWord ++ tailWord_376910).sum := by decide
  have hdescent : baseEnd_376910 < baseStart_376910 := by decide
  rcases family_descends (prefixWord ++ tailWord_376910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376968 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_376968 : Nat := 118140960795 + 376968 * 2 ^ 59
def prefixEnd_376968 : Nat := 4983230072969 + 3 ^ 40 * 376968 * 2
def baseEnd_376968 : Nat := 172058466990387861925655

theorem tailTrace_376968 : CollatzResearch.WordTrace tailWord_376968 prefixEnd_376968 172058466990387861925655 := by
  unfold tailWord_376968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6874576249158395926937779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9166101665544527902583705 6874576249158395926937779)
  ·
    refine ⟨10311864373737593890406669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6874576249158395926937779 10311864373737593890406669)
    ·
      refine ⟨3866949140151597708902501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10311864373737593890406669 3866949140151597708902501)
      ·
        refine ⟨725052963778424570419219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3866949140151597708902501 725052963778424570419219)
        ·
          refine ⟨1087579445667636855628829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725052963778424570419219 1087579445667636855628829)
          ·
            refine ⟨407842292125363820860811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1087579445667636855628829 407842292125363820860811)
            ·
              refine ⟨611763438188045731291217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407842292125363820860811 611763438188045731291217)
              ·
                refine ⟨458822578641034298468413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611763438188045731291217 458822578641034298468413)
                ·
                  refine ⟨172058466990387861925655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458822578641034298468413 172058466990387861925655)
                  ·
                    rfl

theorem cell20_376968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_376968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376968 prefixEnd_376968 := by exact prefixLift 376968
  have htrace : WordTrace (prefixWord ++ tailWord_376968) baseStart_376968 baseEnd_376968 := by
    simpa [prefixWord, tailWord_376968, baseEnd_376968] using wordTrace_append hprefix tailTrace_376968
  have hstable : (prefixWord ++ tailWord_376968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376968).length < 2 ^ (prefixWord ++ tailWord_376968).sum := by decide
  have hdescent : baseEnd_376968 < baseStart_376968 := by decide
  rcases family_descends (prefixWord ++ tailWord_376968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376999 : List Nat := [1, 1, 6, 2, 2, 2, 2, 4]
def baseStart_376999 : Nat := 118140960795 + 376999 * 2 ^ 59
def prefixEnd_376999 : Nat := 4983230072969 + 3 ^ 40 * 376999 * 2
def baseEnd_376999 : Nat := 57357538745029843964065

theorem tailTrace_376999 : CollatzResearch.WordTrace tailWord_376999 prefixEnd_376999 57357538745029843964065 := by
  unfold tailWord_376999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13750283161204484148254051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9166855440802989432169367 13750283161204484148254051)
  ·
    refine ⟨20625424741806726222381077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13750283161204484148254051 20625424741806726222381077)
    ·
      refine ⟨966816784772190291674113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20625424741806726222381077 966816784772190291674113)
      ·
        refine ⟨725112588579142718755585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 966816784772190291674113 725112588579142718755585)
        ·
          refine ⟨543834441434357039066689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725112588579142718755585 543834441434357039066689)
          ·
            refine ⟨407875831075767779300017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543834441434357039066689 407875831075767779300017)
            ·
              refine ⟨305906873306825834475013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407875831075767779300017 305906873306825834475013)
              ·
                refine ⟨57357538745029843964065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305906873306825834475013 57357538745029843964065)
                ·
                  rfl

theorem cell20_376999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_376999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_376999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_376999 prefixEnd_376999 := by exact prefixLift 376999
  have htrace : WordTrace (prefixWord ++ tailWord_376999) baseStart_376999 baseEnd_376999 := by
    simpa [prefixWord, tailWord_376999, baseEnd_376999] using wordTrace_append hprefix tailTrace_376999
  have hstable : (prefixWord ++ tailWord_376999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376999).length < 2 ^ (prefixWord ++ tailWord_376999).sum := by decide
  have hdescent : baseEnd_376999 < baseStart_376999 := by decide
  rcases family_descends (prefixWord ++ tailWord_376999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377009 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 2]
def baseStart_377009 : Nat := 118140960795 + 377009 * 2 ^ 59
def prefixEnd_377009 : Nat := 4983230072969 + 3 ^ 40 * 377009 * 2
def baseEnd_377009 : Nat := 172077180507573941558821

theorem tailTrace_377009 : CollatzResearch.WordTrace tailWord_377009 prefixEnd_377009 172077180507573941558821 := by
  unfold tailWord_377009
  simp only [CollatzResearch.WordTrace]
  refine ⟨13750647891168255856118081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9167098594112170570745387 13750647891168255856118081)
  ·
    refine ⟨10312985918376191892088561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13750647891168255856118081 10312985918376191892088561)
    ·
      refine ⟨7734739438782143919066421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10312985918376191892088561 7734739438782143919066421)
      ·
        refine ⟨725131822385825992412477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7734739438782143919066421 725131822385825992412477)
        ·
          refine ⟨271924433394684747154679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 725131822385825992412477 271924433394684747154679)
          ·
            refine ⟨407886650092027120732019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271924433394684747154679 407886650092027120732019)
            ·
              refine ⟨611829975138040681098029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407886650092027120732019 611829975138040681098029)
              ·
                refine ⟨229436240676765255411761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611829975138040681098029 229436240676765255411761)
                ·
                  refine ⟨172077180507573941558821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229436240676765255411761 172077180507573941558821)
                  ·
                    rfl

theorem cell20_377009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_377009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377009 prefixEnd_377009 := by exact prefixLift 377009
  have htrace : WordTrace (prefixWord ++ tailWord_377009) baseStart_377009 baseEnd_377009 := by
    simpa [prefixWord, tailWord_377009, baseEnd_377009] using wordTrace_append hprefix tailTrace_377009
  have hstable : (prefixWord ++ tailWord_377009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377009).length < 2 ^ (prefixWord ++ tailWord_377009).sum := by decide
  have hdescent : baseEnd_377009 < baseStart_377009 := by decide
  rcases family_descends (prefixWord ++ tailWord_377009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377020 : List Nat := [2, 2, 2, 3, 4, 1, 6]
def baseStart_377020 : Nat := 118140960795 + 377020 * 2 ^ 59
def prefixEnd_377020 : Nat := 4983230072969 + 3 ^ 40 * 377020 * 2
def baseEnd_377020 : Nat := 19120244578589643576901

theorem tailTrace_377020 : CollatzResearch.WordTrace tailWord_377020 prefixEnd_377020 19120244578589643576901 := by
  unfold tailWord_377020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875524547064202367384257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9167366062752269823179009 6875524547064202367384257)
  ·
    refine ⟨5156643410298151775538193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6875524547064202367384257 5156643410298151775538193)
    ·
      refine ⟨3867482557723613831653645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5156643410298151775538193 3867482557723613831653645)
      ·
        refine ⟨1450305959146355186870117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3867482557723613831653645 1450305959146355186870117)
        ·
          refine ⟨271932367339941597538147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1450305959146355186870117 271932367339941597538147)
          ·
            refine ⟨407898551009912396307221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271932367339941597538147 407898551009912396307221)
            ·
              refine ⟨19120244578589643576901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 407898551009912396307221 19120244578589643576901)
              ·
                rfl

theorem cell20_377020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 6].length) (baseStart_377020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377020 prefixEnd_377020 := by exact prefixLift 377020
  have htrace : WordTrace (prefixWord ++ tailWord_377020) baseStart_377020 baseEnd_377020 := by
    simpa [prefixWord, tailWord_377020, baseEnd_377020] using wordTrace_append hprefix tailTrace_377020
  have hstable : (prefixWord ++ tailWord_377020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377020).length < 2 ^ (prefixWord ++ tailWord_377020).sum := by decide
  have hdescent : baseEnd_377020 < baseStart_377020 := by decide
  rcases family_descends (prefixWord ++ tailWord_377020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377024 : List Nat := [2, 1, 1, 2, 5, 1, 8]
def baseStart_377024 : Nat := 118140960795 + 377024 * 2 ^ 59
def prefixEnd_377024 : Nat := 4983230072969 + 3 ^ 40 * 377024 * 2
def baseEnd_377024 : Nat := 19120447435144506228751

theorem tailTrace_377024 : CollatzResearch.WordTrace tailWord_377024 prefixEnd_377024 19120447435144506228751 := by
  unfold tailWord_377024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875597493056956708957063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9167463324075942278609417 6875597493056956708957063)
  ·
    refine ⟨10313396239585435063435595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6875597493056956708957063 10313396239585435063435595)
    ·
      refine ⟨15470094359378152595153393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10313396239585435063435595 15470094359378152595153393)
      ·
        refine ⟨11602570769533614446365045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15470094359378152595153393 11602570769533614446365045)
        ·
          refine ⟨1087741009643776354346723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11602570769533614446365045 1087741009643776354346723)
          ·
            refine ⟨1631611514465664531520085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087741009643776354346723 1631611514465664531520085)
            ·
              refine ⟨19120447435144506228751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1631611514465664531520085 19120447435144506228751)
              ·
                rfl

theorem cell20_377024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_377024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377024 prefixEnd_377024 := by exact prefixLift 377024
  have htrace : WordTrace (prefixWord ++ tailWord_377024) baseStart_377024 baseEnd_377024 := by
    simpa [prefixWord, tailWord_377024, baseEnd_377024] using wordTrace_append hprefix tailTrace_377024
  have hstable : (prefixWord ++ tailWord_377024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377024).length < 2 ^ (prefixWord ++ tailWord_377024).sum := by decide
  have hdescent : baseEnd_377024 < baseStart_377024 := by decide
  rcases family_descends (prefixWord ++ tailWord_377024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377026 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_377026 : Nat := 118140960795 + 377026 * 2 ^ 59
def prefixEnd_377026 : Nat := 4983230072969 + 3 ^ 40 * 377026 * 2
def baseEnd_377026 : Nat := 172084939770797437992085

theorem tailTrace_377026 : CollatzResearch.WordTrace tailWord_377026 prefixEnd_377026 172084939770797437992085 := by
  unfold tailWord_377026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437816983026666939871733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9167511954737778506324621 3437816983026666939871733)
  ·
    refine ⟨322295342158750025612975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3437816983026666939871733 322295342158750025612975)
    ·
      refine ⟨483443013238125038419463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322295342158750025612975 483443013238125038419463)
      ·
        refine ⟨725164519857187557629195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483443013238125038419463 725164519857187557629195)
        ·
          refine ⟨1087746779785781336443793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725164519857187557629195 1087746779785781336443793)
          ·
            refine ⟨815810084839336002332845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087746779785781336443793 815810084839336002332845)
            ·
              refine ⟨305928781814751000874817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815810084839336002332845 305928781814751000874817)
              ·
                refine ⟨229446586361063250656113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305928781814751000874817 229446586361063250656113)
                ·
                  refine ⟨172084939770797437992085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229446586361063250656113 172084939770797437992085)
                  ·
                    rfl

theorem cell20_377026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_377026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377026 prefixEnd_377026 := by exact prefixLift 377026
  have htrace : WordTrace (prefixWord ++ tailWord_377026) baseStart_377026 baseEnd_377026 := by
    simpa [prefixWord, tailWord_377026, baseEnd_377026] using wordTrace_append hprefix tailTrace_377026
  have hstable : (prefixWord ++ tailWord_377026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377026).length < 2 ^ (prefixWord ++ tailWord_377026).sum := by decide
  have hdescent : baseEnd_377026 < baseStart_377026 := by decide
  rcases family_descends (prefixWord ++ tailWord_377026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377134 : List Nat := [4, 1, 3, 3, 1, 1, 7]
def baseStart_377134 : Nat := 118140960795 + 377134 * 2 ^ 59
def prefixEnd_377134 : Nat := 4983230072969 + 3 ^ 40 * 377134 * 2
def baseEnd_377134 : Nat := 19126025990403229154627

theorem tailTrace_377134 : CollatzResearch.WordTrace tailWord_377134 prefixEnd_377134 19126025990403229154627 := by
  unfold tailWord_377134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719400876964425275552307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9170138010476934802945637 1719400876964425275552307)
  ·
    refine ⟨2579101315446637913328461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719400876964425275552307 2579101315446637913328461)
    ·
      refine ⟨967162993292489217498173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2579101315446637913328461 967162993292489217498173)
      ·
        refine ⟨362686122484683456561815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 967162993292489217498173 362686122484683456561815)
        ·
          refine ⟨544029183727025184842723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362686122484683456561815 544029183727025184842723)
          ·
            refine ⟨816043775590537777264085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544029183727025184842723 816043775590537777264085)
            ·
              refine ⟨19126025990403229154627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 816043775590537777264085 19126025990403229154627)
              ·
                rfl

theorem cell20_377134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 7].length) (baseStart_377134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377134 prefixEnd_377134 := by exact prefixLift 377134
  have htrace : WordTrace (prefixWord ++ tailWord_377134) baseStart_377134 baseEnd_377134 := by
    simpa [prefixWord, tailWord_377134, baseEnd_377134] using wordTrace_append hprefix tailTrace_377134
  have hstable : (prefixWord ++ tailWord_377134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377134).length < 2 ^ (prefixWord ++ tailWord_377134).sum := by decide
  have hdescent : baseEnd_377134 < baseStart_377134 := by decide
  rcases family_descends (prefixWord ++ tailWord_377134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377148 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 2]
def baseStart_377148 : Nat := 118140960795 + 377148 * 2 ^ 59
def prefixEnd_377148 : Nat := 4983230072969 + 3 ^ 40 * 377148 * 2
def baseEnd_377148 : Nat := 172140623895107235924919

theorem tailTrace_377148 : CollatzResearch.WordTrace tailWord_377148 prefixEnd_377148 172140623895107235924919 := by
  unfold tailWord_377148
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877858818832341297714049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9170478425109788396952065 6877858818832341297714049)
  ·
    refine ⟨5158394114124255973285537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6877858818832341297714049 5158394114124255973285537)
    ·
      refine ⟨3868795585593191979964153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5158394114124255973285537 3868795585593191979964153)
      ·
        refine ⟨2901596689194893984973115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3868795585593191979964153 2901596689194893984973115)
        ·
          refine ⟨4352395033792340977459673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901596689194893984973115 4352395033792340977459673)
          ·
            refine ⟨3264296275344255733094755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4352395033792340977459673 3264296275344255733094755)
            ·
              refine ⟨4896444413016383599642133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3264296275344255733094755 4896444413016383599642133)
              ·
                refine ⟨229520831860142981233225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4896444413016383599642133 229520831860142981233225)
                ·
                  refine ⟨172140623895107235924919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229520831860142981233225 172140623895107235924919)
                  ·
                    rfl

theorem cell20_377148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_377148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377148 prefixEnd_377148 := by exact prefixLift 377148
  have htrace : WordTrace (prefixWord ++ tailWord_377148) baseStart_377148 baseEnd_377148 := by
    simpa [prefixWord, tailWord_377148, baseEnd_377148] using wordTrace_append hprefix tailTrace_377148
  have hstable : (prefixWord ++ tailWord_377148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377148).length < 2 ^ (prefixWord ++ tailWord_377148).sum := by decide
  have hdescent : baseEnd_377148 < baseStart_377148 := by decide
  rcases family_descends (prefixWord ++ tailWord_377148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377169 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_377169 : Nat := 118140960795 + 377169 * 2 ^ 59
def prefixEnd_377169 : Nat := 4983230072969 + 3 ^ 40 * 377169 * 2
def baseEnd_377169 : Nat := 172150208867324496224833

theorem tailTrace_377169 : CollatzResearch.WordTrace tailWord_377169 prefixEnd_377169 172150208867324496224833 := by
  unfold tailWord_377169
  simp only [CollatzResearch.WordTrace]
  refine ⟨13756483570588603181942561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9170989047059068787961707 13756483570588603181942561)
  ·
    refine ⟨10317362677941452386456921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13756483570588603181942561 10317362677941452386456921)
    ·
      refine ⟨7738022008456089289842691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10317362677941452386456921 7738022008456089289842691)
      ·
        refine ⟨11607033012684133934764037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738022008456089289842691 11607033012684133934764037)
        ·
          refine ⟨2176318689878275112768257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11607033012684133934764037 2176318689878275112768257)
          ·
            refine ⟨1632239017408706334576193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176318689878275112768257 1632239017408706334576193)
            ·
              refine ⟨1224179263056529750932145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632239017408706334576193 1224179263056529750932145)
              ·
                refine ⟨918134447292397313199109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224179263056529750932145 918134447292397313199109)
                ·
                  refine ⟨172150208867324496224833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 918134447292397313199109 172150208867324496224833)
                  ·
                    rfl

theorem cell20_377169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_377169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377169 prefixEnd_377169 := by exact prefixLift 377169
  have htrace : WordTrace (prefixWord ++ tailWord_377169) baseStart_377169 baseEnd_377169 := by
    simpa [prefixWord, tailWord_377169, baseEnd_377169] using wordTrace_append hprefix tailTrace_377169
  have hstable : (prefixWord ++ tailWord_377169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377169).length < 2 ^ (prefixWord ++ tailWord_377169).sum := by decide
  have hdescent : baseEnd_377169 < baseStart_377169 := by decide
  rcases family_descends (prefixWord ++ tailWord_377169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377172 : List Nat := [2, 4, 1, 1, 2, 4, 2, 4]
def baseStart_377172 : Nat := 118140960795 + 377172 * 2 ^ 59
def prefixEnd_377172 : Nat := 4983230072969 + 3 ^ 40 * 377172 * 2
def baseEnd_377172 : Nat := 57383859383023273041607

theorem tailTrace_377172 : CollatzResearch.WordTrace tailWord_377172 prefixEnd_377172 57383859383023273041607 := by
  unfold tailWord_377172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878296494788867347150885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9171061993051823129534513 6878296494788867347150885)
  ·
    refine ⟨1289680592772912627590791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6878296494788867347150885 1289680592772912627590791)
    ·
      refine ⟨1934520889159368941386187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289680592772912627590791 1934520889159368941386187)
      ·
        refine ⟨2901781333739053412079281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934520889159368941386187 2901781333739053412079281)
        ·
          refine ⟨2176336000304290059059461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2901781333739053412079281 2176336000304290059059461)
          ·
            refine ⟨408063000057054386073649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2176336000304290059059461 408063000057054386073649)
            ·
              refine ⟨306047250042790789555237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408063000057054386073649 306047250042790789555237)
              ·
                refine ⟨57383859383023273041607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306047250042790789555237 57383859383023273041607)
                ·
                  rfl

theorem cell20_377172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_377172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377172 prefixEnd_377172 := by exact prefixLift 377172
  have htrace : WordTrace (prefixWord ++ tailWord_377172) baseStart_377172 baseEnd_377172 := by
    simpa [prefixWord, tailWord_377172, baseEnd_377172] using wordTrace_append hprefix tailTrace_377172
  have hstable : (prefixWord ++ tailWord_377172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377172).length < 2 ^ (prefixWord ++ tailWord_377172).sum := by decide
  have hdescent : baseEnd_377172 < baseStart_377172 := by decide
  rcases family_descends (prefixWord ++ tailWord_377172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377183 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_377183 : Nat := 118140960795 + 377183 * 2 ^ 59
def prefixEnd_377183 : Nat := 4983230072969 + 3 ^ 40 * 377183 * 2
def baseEnd_377183 : Nat := 172156598848802669758109

theorem tailTrace_377183 : CollatzResearch.WordTrace tailWord_377183 prefixEnd_377183 172156598848802669758109 := by
  unfold tailWord_377183
  simp only [CollatzResearch.WordTrace]
  refine ⟨13756994192537883572952203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9171329461691922381968135 13756994192537883572952203)
  ·
    refine ⟨20635491288806825359428305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13756994192537883572952203 20635491288806825359428305)
    ·
      refine ⟨15476618466605119019571229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20635491288806825359428305 15476618466605119019571229)
      ·
        refine ⟨5803731924976919632339211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15476618466605119019571229 5803731924976919632339211)
        ·
          refine ⟨8705597887465379448508817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803731924976919632339211 8705597887465379448508817)
          ·
            refine ⟨6529198415599034586381613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8705597887465379448508817 6529198415599034586381613)
            ·
              refine ⟨2448449405849637969893105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6529198415599034586381613 2448449405849637969893105)
              ·
                refine ⟨1836337054387228477419829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448449405849637969893105 1836337054387228477419829)
                ·
                  refine ⟨172156598848802669758109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836337054387228477419829 172156598848802669758109)
                  ·
                    rfl

theorem cell20_377183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_377183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377183 prefixEnd_377183 := by exact prefixLift 377183
  have htrace : WordTrace (prefixWord ++ tailWord_377183) baseStart_377183 baseEnd_377183 := by
    simpa [prefixWord, tailWord_377183, baseEnd_377183] using wordTrace_append hprefix tailTrace_377183
  have hstable : (prefixWord ++ tailWord_377183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377183).length < 2 ^ (prefixWord ++ tailWord_377183).sum := by decide
  have hdescent : baseEnd_377183 < baseStart_377183 := by decide
  rcases family_descends (prefixWord ++ tailWord_377183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377217 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_377217 : Nat := 118140960795 + 377217 * 2 ^ 59
def prefixEnd_377217 : Nat := 4983230072969 + 3 ^ 40 * 377217 * 2
def baseEnd_377217 : Nat := 172172117375249662624637

theorem tailTrace_377217 : CollatzResearch.WordTrace tailWord_377217 prefixEnd_377217 172172117375249662624637 := by
  unfold tailWord_377217
  simp only [CollatzResearch.WordTrace]
  refine ⟨13758234274414707379689905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9172156182943138253126603 13758234274414707379689905)
  ·
    refine ⟨10318675705811030534767429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13758234274414707379689905 10318675705811030534767429)
    ·
      refine ⟨1934751694839568225268893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10318675705811030534767429 1934751694839568225268893)
      ·
        refine ⟨725531885564838084475835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1934751694839568225268893 725531885564838084475835)
        ·
          refine ⟨1088297828347257126713753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725531885564838084475835 1088297828347257126713753)
          ·
            refine ⟨816223371260442845035315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088297828347257126713753 816223371260442845035315)
            ·
              refine ⟨1224335056890664267552973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816223371260442845035315 1224335056890664267552973)
              ·
                refine ⟨459125646333999100332365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224335056890664267552973 459125646333999100332365)
                ·
                  refine ⟨172172117375249662624637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459125646333999100332365 172172117375249662624637)
                  ·
                    rfl

theorem cell20_377217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_377217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377217 prefixEnd_377217 := by exact prefixLift 377217
  have htrace : WordTrace (prefixWord ++ tailWord_377217) baseStart_377217 baseEnd_377217 := by
    simpa [prefixWord, tailWord_377217, baseEnd_377217] using wordTrace_append hprefix tailTrace_377217
  have hstable : (prefixWord ++ tailWord_377217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377217).length < 2 ^ (prefixWord ++ tailWord_377217).sum := by decide
  have hdescent : baseEnd_377217 < baseStart_377217 := by decide
  rcases family_descends (prefixWord ++ tailWord_377217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377255 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_377255 : Nat := 118140960795 + 377255 * 2 ^ 59
def prefixEnd_377255 : Nat := 4983230072969 + 3 ^ 40 * 377255 * 2
def baseEnd_377255 : Nat := 172189461610690419357815

theorem tailTrace_377255 : CollatzResearch.WordTrace tailWord_377255 prefixEnd_377255 172189461610690419357815 := by
  unfold tailWord_377255
  simp only [CollatzResearch.WordTrace]
  refine ⟨13759620248277039869573219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9173080165518026579715479 13759620248277039869573219)
  ·
    refine ⟨20639430372415559804359829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13759620248277039869573219 20639430372415559804359829)
    ·
      refine ⟨967473298706979365829367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20639430372415559804359829 967473298706979365829367)
      ·
        refine ⟨1451209948060469048744051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967473298706979365829367 1451209948060469048744051)
        ·
          refine ⟨2176814922090703573116077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451209948060469048744051 2176814922090703573116077)
          ·
            refine ⟨816305595784013839918529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2176814922090703573116077 816305595784013839918529)
            ·
              refine ⟨612229196838010379938897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816305595784013839918529 612229196838010379938897)
              ·
                refine ⟨459171897628507784954173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612229196838010379938897 459171897628507784954173)
                ·
                  refine ⟨172189461610690419357815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459171897628507784954173 172189461610690419357815)
                  ·
                    rfl

theorem cell20_377255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_377255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377255 prefixEnd_377255 := by exact prefixLift 377255
  have htrace : WordTrace (prefixWord ++ tailWord_377255) baseStart_377255 baseEnd_377255 := by
    simpa [prefixWord, tailWord_377255, baseEnd_377255] using wordTrace_append hprefix tailTrace_377255
  have hstable : (prefixWord ++ tailWord_377255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377255).length < 2 ^ (prefixWord ++ tailWord_377255).sum := by decide
  have hdescent : baseEnd_377255 < baseStart_377255 := by decide
  rcases family_descends (prefixWord ++ tailWord_377255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377304 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_377304 : Nat := 118140960795 + 377304 * 2 ^ 59
def prefixEnd_377304 : Nat := 4983230072969 + 3 ^ 40 * 377304 * 2
def baseEnd_377304 : Nat := 172211826545864026724281

theorem tailTrace_377304 : CollatzResearch.WordTrace tailWord_377304 prefixEnd_377304 172211826545864026724281 := by
  unfold tailWord_377304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880703712549760619053483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9174271616733014158737977 6880703712549760619053483)
  ·
    refine ⟨10321055568824640928580225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6880703712549760619053483 10321055568824640928580225)
    ·
      refine ⟨7740791676618480696435169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10321055568824640928580225 7740791676618480696435169)
      ·
        refine ⟨5805593757463860522326377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7740791676618480696435169 5805593757463860522326377)
        ·
          refine ⟨4354195318097895391744783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805593757463860522326377 4354195318097895391744783)
          ·
            refine ⟨6531292977146843087617175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354195318097895391744783 6531292977146843087617175)
            ·
              refine ⟨9796939465720264631425763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531292977146843087617175 9796939465720264631425763)
              ·
                refine ⟨14695409198580396947138645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796939465720264631425763 14695409198580396947138645)
                ·
                  refine ⟨172211826545864026724281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14695409198580396947138645 172211826545864026724281)
                  ·
                    rfl

theorem cell20_377304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_377304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377304 prefixEnd_377304 := by exact prefixLift 377304
  have htrace : WordTrace (prefixWord ++ tailWord_377304) baseStart_377304 baseEnd_377304 := by
    simpa [prefixWord, tailWord_377304, baseEnd_377304] using wordTrace_append hprefix tailTrace_377304
  have hstable : (prefixWord ++ tailWord_377304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377304).length < 2 ^ (prefixWord ++ tailWord_377304).sum := by decide
  have hdescent : baseEnd_377304 < baseStart_377304 := by decide
  rcases family_descends (prefixWord ++ tailWord_377304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377345 : List Nat := [1, 2, 4, 1, 3, 1, 4, 4]
def baseStart_377345 : Nat := 118140960795 + 377345 * 2 ^ 59
def prefixEnd_377345 : Nat := 4983230072969 + 3 ^ 40 * 377345 * 2
def baseEnd_377345 : Nat := 57410180021016702119149

theorem tailTrace_377345 : CollatzResearch.WordTrace tailWord_377345 prefixEnd_377345 57410180021016702119149 := by
  unfold tailWord_377345
  simp only [CollatzResearch.WordTrace]
  refine ⟨13762902817950985240349489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9175268545300656826899659 13762902817950985240349489)
  ·
    refine ⟨10322177113463238930262117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13762902817950985240349489 10322177113463238930262117)
    ·
      refine ⟨1935408208774357299424147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10322177113463238930262117 1935408208774357299424147)
      ·
        refine ⟨2903112313161535949136221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935408208774357299424147 2903112313161535949136221)
        ·
          refine ⟨1088667117435575980926083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2903112313161535949136221 1088667117435575980926083)
          ·
            refine ⟨1633000676153363971389125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088667117435575980926083 1633000676153363971389125)
            ·
              refine ⟨306187626778755744635461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1633000676153363971389125 306187626778755744635461)
              ·
                refine ⟨57410180021016702119149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306187626778755744635461 57410180021016702119149)
                ·
                  rfl

theorem cell20_377345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_377345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377345 prefixEnd_377345 := by exact prefixLift 377345
  have htrace : WordTrace (prefixWord ++ tailWord_377345) baseStart_377345 baseEnd_377345 := by
    simpa [prefixWord, tailWord_377345, baseEnd_377345] using wordTrace_append hprefix tailTrace_377345
  have hstable : (prefixWord ++ tailWord_377345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377345).length < 2 ^ (prefixWord ++ tailWord_377345).sum := by decide
  have hdescent : baseEnd_377345 < baseStart_377345 := by decide
  rcases family_descends (prefixWord ++ tailWord_377345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377355 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 2]
def baseStart_377355 : Nat := 118140960795 + 377355 * 2 ^ 59
def prefixEnd_377355 : Nat := 4983230072969 + 3 ^ 40 * 377355 * 2
def baseEnd_377355 : Nat := 172235104335534516024073

theorem tailTrace_377355 : CollatzResearch.WordTrace tailWord_377355 prefixEnd_377355 172235104335534516024073 := by
  unfold tailWord_377355
  simp only [CollatzResearch.WordTrace]
  refine ⟨13763267547914756948213519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9175511698609837965475679 13763267547914756948213519)
  ·
    refine ⟨20644901321872135422320279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13763267547914756948213519 20644901321872135422320279)
    ·
      refine ⟨30967351982808203133480419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20644901321872135422320279 30967351982808203133480419)
      ·
        refine ⟨46451027974212304700220629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30967351982808203133480419 46451027974212304700220629)
        ·
          refine ⟨1088695968145600891411421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 46451027974212304700220629 1088695968145600891411421)
          ·
            refine ⟨408260988054600334279283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1088695968145600891411421 408260988054600334279283)
            ·
              refine ⟨612391482081900501418925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408260988054600334279283 612391482081900501418925)
              ·
                refine ⟨229646805780712688032097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 612391482081900501418925 229646805780712688032097)
                ·
                  refine ⟨172235104335534516024073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229646805780712688032097 172235104335534516024073)
                  ·
                    rfl

theorem cell20_377355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 2].length) (baseStart_377355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377355 prefixEnd_377355 := by exact prefixLift 377355
  have htrace : WordTrace (prefixWord ++ tailWord_377355) baseStart_377355 baseEnd_377355 := by
    simpa [prefixWord, tailWord_377355, baseEnd_377355] using wordTrace_append hprefix tailTrace_377355
  have hstable : (prefixWord ++ tailWord_377355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377355).length < 2 ^ (prefixWord ++ tailWord_377355).sum := by decide
  have hdescent : baseEnd_377355 < baseStart_377355 := by decide
  rcases family_descends (prefixWord ++ tailWord_377355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377386 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_377386 : Nat := 118140960795 + 377386 * 2 ^ 59
def prefixEnd_377386 : Nat := 4983230072969 + 3 ^ 40 * 377386 * 2
def baseEnd_377386 : Nat := 172249253580236185990613

theorem tailTrace_377386 : CollatzResearch.WordTrace tailWord_377386 prefixEnd_377386 172249253580236185990613 := by
  unfold tailWord_377386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441099552700612310648003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9176265473868299495061341 3441099552700612310648003)
  ·
    refine ⟨5161649329050918465972005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3441099552700612310648003 5161649329050918465972005)
    ·
      refine ⟨967809249197047212369751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5161649329050918465972005 967809249197047212369751)
      ·
        refine ⟨1451713873795570818554627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967809249197047212369751 1451713873795570818554627)
        ·
          refine ⟨2177570810693356227831941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451713873795570818554627 2177570810693356227831941)
          ·
            refine ⟨408294527005004292718489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2177570810693356227831941 408294527005004292718489)
            ·
              refine ⟨306220895253753219538867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408294527005004292718489 306220895253753219538867)
              ·
                refine ⟨459331342880629829308301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306220895253753219538867 459331342880629829308301)
                ·
                  refine ⟨172249253580236185990613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459331342880629829308301 172249253580236185990613)
                  ·
                    rfl

theorem cell20_377386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_377386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377386 prefixEnd_377386 := by exact prefixLift 377386
  have htrace : WordTrace (prefixWord ++ tailWord_377386) baseStart_377386 baseEnd_377386 := by
    simpa [prefixWord, tailWord_377386, baseEnd_377386] using wordTrace_append hprefix tailTrace_377386
  have hstable : (prefixWord ++ tailWord_377386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377386).length < 2 ^ (prefixWord ++ tailWord_377386).sum := by decide
  have hdescent : baseEnd_377386 < baseStart_377386 := by decide
  rcases family_descends (prefixWord ++ tailWord_377386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377404 : List Nat := [2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_377404 : Nat := 118140960795 + 377404 * 2 ^ 59
def prefixEnd_377404 : Nat := 4983230072969 + 3 ^ 40 * 377404 * 2
def baseEnd_377404 : Nat := 57419156423569374463513

theorem tailTrace_377404 : CollatzResearch.WordTrace tailWord_377404 prefixEnd_377404 57419156423569374463513 := by
  unfold tailWord_377404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882527362368619158373633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9176703149824825544498177 6882527362368619158373633)
  ·
    refine ⟨5161895521776464368780225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6882527362368619158373633 5161895521776464368780225)
    ·
      refine ⟨3871421641332348276585169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5161895521776464368780225 3871421641332348276585169)
      ·
        refine ⟨2903566230999261207438877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3871421641332348276585169 2903566230999261207438877)
        ·
          refine ⟨1088837336624722952789579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2903566230999261207438877 1088837336624722952789579)
          ·
            refine ⟨1633256004937084429184369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088837336624722952789579 1633256004937084429184369)
            ·
              refine ⟨1224942003702813321888277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633256004937084429184369 1224942003702813321888277)
              ·
                refine ⟨57419156423569374463513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1224942003702813321888277 57419156423569374463513)
                ·
                  rfl

theorem cell20_377404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_377404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377404 prefixEnd_377404 := by exact prefixLift 377404
  have htrace : WordTrace (prefixWord ++ tailWord_377404) baseStart_377404 baseEnd_377404 := by
    simpa [prefixWord, tailWord_377404, baseEnd_377404] using wordTrace_append hprefix tailTrace_377404
  have hstable : (prefixWord ++ tailWord_377404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377404).length < 2 ^ (prefixWord ++ tailWord_377404).sum := by decide
  have hdescent : baseEnd_377404 < baseStart_377404 := by decide
  rcases family_descends (prefixWord ++ tailWord_377404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377425 : List Nat := [1, 2, 2, 1, 3, 11]
def baseStart_377425 : Nat := 118140960795 + 377425 * 2 ^ 59
def prefixEnd_377425 : Nat := 4983230072969 + 3 ^ 40 * 377425 * 2
def baseEnd_377425 : Nat := 6380261268256495692239

theorem tailTrace_377425 : CollatzResearch.WordTrace tailWord_377425 prefixEnd_377425 6380261268256495692239 := by
  unfold tailWord_377425
  simp only [CollatzResearch.WordTrace]
  refine ⟨13765820657661158903261729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9177213771774105935507819 13765820657661158903261729)
  ·
    refine ⟨10324365493245869177446297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13765820657661158903261729 10324365493245869177446297)
    ·
      refine ⟨7743274119934401883084723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10324365493245869177446297 7743274119934401883084723)
      ·
        refine ⟨11614911179901602824627085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7743274119934401883084723 11614911179901602824627085)
        ·
          refine ⟨4355591692463101059235157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11614911179901602824627085 4355591692463101059235157)
          ·
            refine ⟨6380261268256495692239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4355591692463101059235157 6380261268256495692239)
            ·
              rfl

theorem cell20_377425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 11].length) (baseStart_377425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377425 prefixEnd_377425 := by exact prefixLift 377425
  have htrace : WordTrace (prefixWord ++ tailWord_377425) baseStart_377425 baseEnd_377425 := by
    simpa [prefixWord, tailWord_377425, baseEnd_377425] using wordTrace_append hprefix tailTrace_377425
  have hstable : (prefixWord ++ tailWord_377425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377425).length < 2 ^ (prefixWord ++ tailWord_377425).sum := by decide
  have hdescent : baseEnd_377425 < baseStart_377425 := by decide
  rcases family_descends (prefixWord ++ tailWord_377425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377428 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_377428 : Nat := 118140960795 + 377428 * 2 ^ 59
def prefixEnd_377428 : Nat := 4983230072969 + 3 ^ 40 * 377428 * 2
def baseEnd_377428 : Nat := 172268423524670706590441

theorem tailTrace_377428 : CollatzResearch.WordTrace tailWord_377428 prefixEnd_377428 172268423524670706590441 := by
  unfold tailWord_377428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882965038325145207810469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9177286717766860277080625 6882965038325145207810469)
  ·
    refine ⟨1290555944685964726464463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6882965038325145207810469 1290555944685964726464463)
    ·
      refine ⟨1935833917028947089696695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290555944685964726464463 1935833917028947089696695)
      ·
        refine ⟨2903750875543420634545043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935833917028947089696695 2903750875543420634545043)
        ·
          refine ⟨4355626313315130951817565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2903750875543420634545043 4355626313315130951817565)
          ·
            refine ⟨1633359867493174106931587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4355626313315130951817565 1633359867493174106931587)
            ·
              refine ⟨2450039801239761160397381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633359867493174106931587 2450039801239761160397381)
              ·
                refine ⟨459382462732455217574509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2450039801239761160397381 459382462732455217574509)
                ·
                  refine ⟨172268423524670706590441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459382462732455217574509 172268423524670706590441)
                  ·
                    rfl

theorem cell20_377428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_377428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377428 prefixEnd_377428 := by exact prefixLift 377428
  have htrace : WordTrace (prefixWord ++ tailWord_377428) baseStart_377428 baseEnd_377428 := by
    simpa [prefixWord, tailWord_377428, baseEnd_377428] using wordTrace_append hprefix tailTrace_377428
  have hstable : (prefixWord ++ tailWord_377428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377428).length < 2 ^ (prefixWord ++ tailWord_377428).sum := by decide
  have hdescent : baseEnd_377428 < baseStart_377428 := by decide
  rcases family_descends (prefixWord ++ tailWord_377428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377463 : List Nat := [1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_377463 : Nat := 118140960795 + 377463 * 2 ^ 59
def prefixEnd_377463 : Nat := 4983230072969 + 3 ^ 40 * 377463 * 2
def baseEnd_377463 : Nat := 57428132826122046807877

theorem tailTrace_377463 : CollatzResearch.WordTrace tailWord_377463 prefixEnd_377463 57428132826122046807877 := by
  unfold tailWord_377463
  simp only [CollatzResearch.WordTrace]
  refine ⟨13767206631523491393145043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9178137754348994262096695 13767206631523491393145043)
  ·
    refine ⟨20650809947285237089717565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13767206631523491393145043 20650809947285237089717565)
    ·
      refine ⟨7744053730231963908644087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20650809947285237089717565 7744053730231963908644087)
      ·
        refine ⟨11616080595347945862966131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744053730231963908644087 11616080595347945862966131)
        ·
          refine ⟨17424120893021918794449197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11616080595347945862966131 17424120893021918794449197)
          ·
            refine ⟨6534045334883219547918449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17424120893021918794449197 6534045334883219547918449)
            ·
              refine ⟨4900534001162414660938837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6534045334883219547918449 4900534001162414660938837)
              ·
                refine ⟨57428132826122046807877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4900534001162414660938837 57428132826122046807877)
                ·
                  rfl

theorem cell20_377463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_377463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377463 prefixEnd_377463 := by exact prefixLift 377463
  have htrace : WordTrace (prefixWord ++ tailWord_377463) baseStart_377463 baseEnd_377463 := by
    simpa [prefixWord, tailWord_377463, baseEnd_377463] using wordTrace_append hprefix tailTrace_377463
  have hstable : (prefixWord ++ tailWord_377463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377463).length < 2 ^ (prefixWord ++ tailWord_377463).sum := by decide
  have hdescent : baseEnd_377463 < baseStart_377463 := by decide
  rcases family_descends (prefixWord ++ tailWord_377463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377469 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 2]
def baseStart_377469 : Nat := 118140960795 + 377469 * 2 ^ 59
def prefixEnd_377469 : Nat := 4983230072969 + 3 ^ 40 * 377469 * 2
def baseEnd_377469 : Nat := 172287137041856786223607

theorem tailTrace_377469 : CollatzResearch.WordTrace tailWord_377469 prefixEnd_377469 172287137041856786223607 := by
  unfold tailWord_377469
  simp only [CollatzResearch.WordTrace]
  refine ⟨13767425469501754417863461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9178283646334502945242307 13767425469501754417863461)
  ·
    refine ⟨2581392275531578953349399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13767425469501754417863461 2581392275531578953349399)
    ·
      refine ⟨3872088413297368430024099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581392275531578953349399 3872088413297368430024099)
      ·
        refine ⟨5808132619946052645036149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872088413297368430024099 5808132619946052645036149)
        ·
          refine ⟨544512433119942435472139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5808132619946052645036149 544512433119942435472139)
          ·
            refine ⟨816768649679913653208209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544512433119942435472139 816768649679913653208209)
            ·
              refine ⟨612576487259935239906157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816768649679913653208209 612576487259935239906157)
              ·
                refine ⟨229716182722475714964809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 612576487259935239906157 229716182722475714964809)
                ·
                  refine ⟨172287137041856786223607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229716182722475714964809 172287137041856786223607)
                  ·
                    rfl

theorem cell20_377469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_377469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377469 prefixEnd_377469 := by exact prefixLift 377469
  have htrace : WordTrace (prefixWord ++ tailWord_377469) baseStart_377469 baseEnd_377469 := by
    simpa [prefixWord, tailWord_377469, baseEnd_377469] using wordTrace_append hprefix tailTrace_377469
  have hstable : (prefixWord ++ tailWord_377469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377469).length < 2 ^ (prefixWord ++ tailWord_377469).sum := by decide
  have hdescent : baseEnd_377469 < baseStart_377469 := by decide
  rcases family_descends (prefixWord ++ tailWord_377469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377490 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_377490 : Nat := 118140960795 + 377490 * 2 ^ 59
def prefixEnd_377490 : Nat := 4983230072969 + 3 ^ 40 * 377490 * 2
def baseEnd_377490 : Nat := 172296722014074046523521

theorem tailTrace_377490 : CollatzResearch.WordTrace tailWord_377490 prefixEnd_377490 172296722014074046523521 := by
  unfold tailWord_377490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442047850606418751094481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9178794268283783336251949 3442047850606418751094481)
  ·
    refine ⟨2581535887954814063320861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3442047850606418751094481 2581535887954814063320861)
    ·
      refine ⟨968075957983055273745323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2581535887954814063320861 968075957983055273745323)
      ·
        refine ⟨1452113936974582910617985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968075957983055273745323 1452113936974582910617985)
        ·
          refine ⟨1089085452730937182963489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452113936974582910617985 1089085452730937182963489)
          ·
            refine ⟨816814089548202887222617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089085452730937182963489 816814089548202887222617)
            ·
              refine ⟨612610567161152165416963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816814089548202887222617 612610567161152165416963)
              ·
                refine ⟨918915850741728248125445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612610567161152165416963 918915850741728248125445)
                ·
                  refine ⟨172296722014074046523521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 918915850741728248125445 172296722014074046523521)
                  ·
                    rfl

theorem cell20_377490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_377490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377490 prefixEnd_377490 := by exact prefixLift 377490
  have htrace : WordTrace (prefixWord ++ tailWord_377490) baseStart_377490 baseEnd_377490 := by
    simpa [prefixWord, tailWord_377490, baseEnd_377490] using wordTrace_append hprefix tailTrace_377490
  have hstable : (prefixWord ++ tailWord_377490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377490).length < 2 ^ (prefixWord ++ tailWord_377490).sum := by decide
  have hdescent : baseEnd_377490 < baseStart_377490 := by decide
  rcases family_descends (prefixWord ++ tailWord_377490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377514 : List Nat := [3, 1, 5, 2, 1, 1, 1, 6]
def baseStart_377514 : Nat := 118140960795 + 377514 * 2 ^ 59
def prefixEnd_377514 : Nat := 4983230072969 + 3 ^ 40 * 377514 * 2
def baseEnd_377514 : Nat := 57435892089345543241141

theorem tailTrace_377514 : CollatzResearch.WordTrace tailWord_377514 prefixEnd_377514 57435892089345543241141 := by
  unfold tailWord_377514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442266688584681775812899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9179377836225818068834397 3442266688584681775812899)
  ·
    refine ⟨5163400032877022663719349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3442266688584681775812899 5163400032877022663719349)
    ·
      refine ⟨484068753082220874723689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5163400032877022663719349 484068753082220874723689)
      ·
        refine ⟨363051564811665656042767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484068753082220874723689 363051564811665656042767)
        ·
          refine ⟨544577347217498484064151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363051564811665656042767 544577347217498484064151)
          ·
            refine ⟨816866020826247726096227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544577347217498484064151 816866020826247726096227)
            ·
              refine ⟨1225299031239371589144341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816866020826247726096227 1225299031239371589144341)
              ·
                refine ⟨57435892089345543241141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1225299031239371589144341 57435892089345543241141)
                ·
                  rfl

theorem cell20_377514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_377514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377514 prefixEnd_377514 := by exact prefixLift 377514
  have htrace : WordTrace (prefixWord ++ tailWord_377514) baseStart_377514 baseEnd_377514 := by
    simpa [prefixWord, tailWord_377514, baseEnd_377514] using wordTrace_append hprefix tailTrace_377514
  have hstable : (prefixWord ++ tailWord_377514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377514).length < 2 ^ (prefixWord ++ tailWord_377514).sum := by decide
  have hdescent : baseEnd_377514 < baseStart_377514 := by decide
  rcases family_descends (prefixWord ++ tailWord_377514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377559 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 3]
def baseStart_377559 : Nat := 118140960795 + 377559 * 2 ^ 59
def prefixEnd_377559 : Nat := 4983230072969 + 3 ^ 40 * 377559 * 2
def baseEnd_377559 : Nat := 172328215494216473223239

theorem tailTrace_377559 : CollatzResearch.WordTrace tailWord_377559 prefixEnd_377559 172328215494216473223239 := by
  unfold tailWord_377559
  simp only [CollatzResearch.WordTrace]
  refine ⟨13770708039175699788639731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9180472026117133192426487 13770708039175699788639731)
  ·
    refine ⟨20656062058763549682959597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13770708039175699788639731 20656062058763549682959597)
    ·
      refine ⟨7746023272036331131109849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20656062058763549682959597 7746023272036331131109849)
      ·
        refine ⟨5809517454027248348332387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7746023272036331131109849 5809517454027248348332387)
        ·
          refine ⟨8714276181040872522498581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809517454027248348332387 8714276181040872522498581)
          ·
            refine ⟨408481695986290899492121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8714276181040872522498581 408481695986290899492121)
            ·
              refine ⟨306361271989718174619091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408481695986290899492121 306361271989718174619091)
              ·
                refine ⟨459541907984577261928637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306361271989718174619091 459541907984577261928637)
                ·
                  refine ⟨172328215494216473223239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459541907984577261928637 172328215494216473223239)
                  ·
                    rfl

theorem cell20_377559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_377559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377559 prefixEnd_377559 := by exact prefixLift 377559
  have htrace : WordTrace (prefixWord ++ tailWord_377559) baseStart_377559 baseEnd_377559 := by
    simpa [prefixWord, tailWord_377559, baseEnd_377559] using wordTrace_append hprefix tailTrace_377559
  have hstable : (prefixWord ++ tailWord_377559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377559).length < 2 ^ (prefixWord ++ tailWord_377559).sum := by decide
  have hdescent : baseEnd_377559 < baseStart_377559 := by decide
  rcases family_descends (prefixWord ++ tailWord_377559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377577 : List Nat := [1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_377577 : Nat := 118140960795 + 377577 * 2 ^ 59
def prefixEnd_377577 : Nat := 4983230072969 + 3 ^ 40 * 377577 * 2
def baseEnd_377577 : Nat := 57445477061562803541055

theorem tailTrace_377577 : CollatzResearch.WordTrace tailWord_377577 prefixEnd_377577 57445477061562803541055 := by
  unfold tailWord_377577
  simp only [CollatzResearch.WordTrace]
  refine ⟨13771364553110488862794985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9180909702073659241863323 13771364553110488862794985)
  ·
    refine ⟨10328523414832866647096239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13771364553110488862794985 10328523414832866647096239)
    ·
      refine ⟨15492785122249299970644359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10328523414832866647096239 15492785122249299970644359)
      ·
        refine ⟨23239177683373949955966539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15492785122249299970644359 23239177683373949955966539)
        ·
          refine ⟨34858766525060924933949809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23239177683373949955966539 34858766525060924933949809)
          ·
            refine ⟨26144074893795693700462357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34858766525060924933949809 26144074893795693700462357)
            ·
              refine ⟨1225503510646673142209173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26144074893795693700462357 1225503510646673142209173)
              ·
                refine ⟨57445477061562803541055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1225503510646673142209173 57445477061562803541055)
                ·
                  rfl

theorem cell20_377577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_377577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377577 prefixEnd_377577 := by exact prefixLift 377577
  have htrace : WordTrace (prefixWord ++ tailWord_377577) baseStart_377577 baseEnd_377577 := by
    simpa [prefixWord, tailWord_377577, baseEnd_377577] using wordTrace_append hprefix tailTrace_377577
  have hstable : (prefixWord ++ tailWord_377577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377577).length < 2 ^ (prefixWord ++ tailWord_377577).sum := by decide
  have hdescent : baseEnd_377577 < baseStart_377577 := by decide
  rcases family_descends (prefixWord ++ tailWord_377577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377587 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 2]
def baseStart_377587 : Nat := 118140960795 + 377587 * 2 ^ 59
def prefixEnd_377587 : Nat := 4983230072969 + 3 ^ 40 * 377587 * 2
def baseEnd_377587 : Nat := 172340995457172820289791

theorem tailTrace_377587 : CollatzResearch.WordTrace tailWord_377587 prefixEnd_377587 172340995457172820289791 := by
  unfold tailWord_377587
  simp only [CollatzResearch.WordTrace]
  refine ⟨13771729283074260570659015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9181152855382840380439343 13771729283074260570659015)
  ·
    refine ⟨20657593924611390855988523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13771729283074260570659015 20657593924611390855988523)
    ·
      refine ⟨30986390886917086283982785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20657593924611390855988523 30986390886917086283982785)
      ·
        refine ⟨23239793165187814712987089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30986390886917086283982785 23239793165187814712987089)
        ·
          refine ⟨17429844873890861034740317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23239793165187814712987089 17429844873890861034740317)
          ·
            refine ⟨6536191827709072888027619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17429844873890861034740317 6536191827709072888027619)
            ·
              refine ⟨9804287741563609332041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536191827709072888027619 9804287741563609332041429)
              ·
                refine ⟨229787993942897093719721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9804287741563609332041429 229787993942897093719721)
                ·
                  refine ⟨172340995457172820289791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229787993942897093719721 172340995457172820289791)
                  ·
                    rfl

theorem cell20_377587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 2].length) (baseStart_377587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377587 prefixEnd_377587 := by exact prefixLift 377587
  have htrace : WordTrace (prefixWord ++ tailWord_377587) baseStart_377587 baseEnd_377587 := by
    simpa [prefixWord, tailWord_377587, baseEnd_377587] using wordTrace_append hprefix tailTrace_377587
  have hstable : (prefixWord ++ tailWord_377587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377587).length < 2 ^ (prefixWord ++ tailWord_377587).sum := by decide
  have hdescent : baseEnd_377587 < baseStart_377587 := by decide
  rcases family_descends (prefixWord ++ tailWord_377587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377604 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 2]
def baseStart_377604 : Nat := 118140960795 + 377604 * 2 ^ 59
def prefixEnd_377604 : Nat := 4983230072969 + 3 ^ 40 * 377604 * 2
def baseEnd_377604 : Nat := 172348754720396316723055

theorem tailTrace_377604 : CollatzResearch.WordTrace tailWord_377604 prefixEnd_377604 172348754720396316723055 := by
  unfold tailWord_377604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6886174662006336237013933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9181566216008448316018577 6886174662006336237013933)
  ·
    refine ⟨2582315498252376088880225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6886174662006336237013933 2582315498252376088880225)
    ·
      refine ⟨1936736623689282066660169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2582315498252376088880225 1936736623689282066660169)
      ·
        refine ⟨1452552467766961549995127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1936736623689282066660169 1452552467766961549995127)
        ·
          refine ⟨2178828701650442324992691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452552467766961549995127 2178828701650442324992691)
          ·
            refine ⟨3268243052475663487489037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178828701650442324992691 3268243052475663487489037)
            ·
              refine ⟨1225591144678373807808389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3268243052475663487489037 1225591144678373807808389)
              ·
                refine ⟨229798339627195088964073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1225591144678373807808389 229798339627195088964073)
                ·
                  refine ⟨172348754720396316723055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229798339627195088964073 172348754720396316723055)
                  ·
                    rfl

theorem cell20_377604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_377604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377604 prefixEnd_377604 := by exact prefixLift 377604
  have htrace : WordTrace (prefixWord ++ tailWord_377604) baseStart_377604 baseEnd_377604 := by
    simpa [prefixWord, tailWord_377604, baseEnd_377604] using wordTrace_append hprefix tailTrace_377604
  have hstable : (prefixWord ++ tailWord_377604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377604).length < 2 ^ (prefixWord ++ tailWord_377604).sum := by decide
  have hdescent : baseEnd_377604 < baseStart_377604 := by decide
  rcases family_descends (prefixWord ++ tailWord_377604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377652 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_377652 : Nat := 118140960795 + 377652 * 2 ^ 59
def prefixEnd_377652 : Nat := 4983230072969 + 3 ^ 40 * 377652 * 2
def baseEnd_377652 : Nat := 172370663228321483122859

theorem tailTrace_377652 : CollatzResearch.WordTrace tailWord_377652 prefixEnd_377652 172370663228321483122859 := by
  unfold tailWord_377652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887050013919388335887605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9182733351892517781183473 6887050013919388335887605)
  ·
    refine ⟨645660938804942656489463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6887050013919388335887605 645660938804942656489463)
    ·
      refine ⟨968491408207413984734195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645660938804942656489463 968491408207413984734195)
      ·
        refine ⟨1452737112311120977101293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968491408207413984734195 1452737112311120977101293)
        ·
          refine ⟨544776417116670366412985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1452737112311120977101293 544776417116670366412985)
          ·
            refine ⟨408582312837502774809739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544776417116670366412985 408582312837502774809739)
            ·
              refine ⟨612873469256254162214609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408582312837502774809739 612873469256254162214609)
              ·
                refine ⟨459655101942190621660957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612873469256254162214609 459655101942190621660957)
                ·
                  refine ⟨172370663228321483122859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459655101942190621660957 172370663228321483122859)
                  ·
                    rfl

theorem cell20_377652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_377652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377652 prefixEnd_377652 := by exact prefixLift 377652
  have htrace : WordTrace (prefixWord ++ tailWord_377652) baseStart_377652 baseEnd_377652 := by
    simpa [prefixWord, tailWord_377652, baseEnd_377652] using wordTrace_append hprefix tailTrace_377652
  have hstable : (prefixWord ++ tailWord_377652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377652).length < 2 ^ (prefixWord ++ tailWord_377652).sum := by decide
  have hdescent : baseEnd_377652 < baseStart_377652 := by decide
  rcases family_descends (prefixWord ++ tailWord_377652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377663 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_377663 : Nat := 118140960795 + 377663 * 2 ^ 59
def prefixEnd_377663 : Nat := 4983230072969 + 3 ^ 40 * 377663 * 2
def baseEnd_377663 : Nat := 172375683928054333756147

theorem tailTrace_377663 : CollatzResearch.WordTrace tailWord_377663 prefixEnd_377663 172375683928054333756147 := by
  unfold tailWord_377663
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774501230798925550425643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9183000820532617033617095 13774501230798925550425643)
  ·
    refine ⟨20661751846198388325638465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13774501230798925550425643 20661751846198388325638465)
    ·
      refine ⟨15496313884648791244228849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20661751846198388325638465 15496313884648791244228849)
      ·
        refine ⟨11622235413486593433171637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15496313884648791244228849 11622235413486593433171637)
        ·
          refine ⟨1089584570014368134359841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11622235413486593433171637 1089584570014368134359841)
          ·
            refine ⟨817188427510776100769881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089584570014368134359841 817188427510776100769881)
            ·
              refine ⟨612891320633082075577411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817188427510776100769881 612891320633082075577411)
              ·
                refine ⟨919336980949623113366117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612891320633082075577411 919336980949623113366117)
                ·
                  refine ⟨172375683928054333756147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919336980949623113366117 172375683928054333756147)
                  ·
                    rfl

theorem cell20_377663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_377663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377663 prefixEnd_377663 := by exact prefixLift 377663
  have htrace : WordTrace (prefixWord ++ tailWord_377663) baseStart_377663 baseEnd_377663 := by
    simpa [prefixWord, tailWord_377663, baseEnd_377663] using wordTrace_append hprefix tailTrace_377663
  have hstable : (prefixWord ++ tailWord_377663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377663).length < 2 ^ (prefixWord ++ tailWord_377663).sum := by decide
  have hdescent : baseEnd_377663 < baseStart_377663 := by decide
  rcases family_descends (prefixWord ++ tailWord_377663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377687 : List Nat := [1, 1, 3, 2, 4, 3, 2, 4]
def baseStart_377687 : Nat := 118140960795 + 377687 * 2 ^ 59
def prefixEnd_377687 : Nat := 4983230072969 + 3 ^ 40 * 377687 * 2
def baseEnd_377687 : Nat := 57462212727338972318683

theorem tailTrace_377687 : CollatzResearch.WordTrace tailWord_377687 prefixEnd_377687 57462212727338972318683 := by
  unfold tailWord_377687
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775376582711977649299315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9183584388474651766199543 13775376582711977649299315)
  ·
    refine ⟨20663064874067966473948973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13775376582711977649299315 20663064874067966473948973)
    ·
      refine ⟨7748649327775487427730865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20663064874067966473948973 7748649327775487427730865)
      ·
        refine ⟨5811486995831615570798149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748649327775487427730865 5811486995831615570798149)
        ·
          refine ⟨1089653811718427919524653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5811486995831615570798149 1089653811718427919524653)
          ·
            refine ⟨408620179394410469821745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1089653811718427919524653 408620179394410469821745)
            ·
              refine ⟨306465134545807852366309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408620179394410469821745 306465134545807852366309)
              ·
                refine ⟨57462212727338972318683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306465134545807852366309 57462212727338972318683)
                ·
                  rfl

theorem cell20_377687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_377687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377687 prefixEnd_377687 := by exact prefixLift 377687
  have htrace : WordTrace (prefixWord ++ tailWord_377687) baseStart_377687 baseEnd_377687 := by
    simpa [prefixWord, tailWord_377687, baseEnd_377687] using wordTrace_append hprefix tailTrace_377687
  have hstable : (prefixWord ++ tailWord_377687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377687).length < 2 ^ (prefixWord ++ tailWord_377687).sum := by decide
  have hdescent : baseEnd_377687 < baseStart_377687 := by decide
  rcases family_descends (prefixWord ++ tailWord_377687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377718 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_377718 : Nat := 118140960795 + 377718 * 2 ^ 59
def prefixEnd_377718 : Nat := 4983230072969 + 3 ^ 40 * 377718 * 2
def baseEnd_377718 : Nat := 172400787426718586922589

theorem tailTrace_377718 : CollatzResearch.WordTrace tailWord_377718 prefixEnd_377718 172400787426718586922589 := by
  unfold tailWord_377718
  simp only [CollatzResearch.WordTrace]
  refine ⟨861031702849979371479863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9184338163733113295785205 861031702849979371479863)
  ·
    refine ⟨1291547554274969057219795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861031702849979371479863 1291547554274969057219795)
    ·
      refine ⟨1937321331412453585829693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291547554274969057219795 1937321331412453585829693)
      ·
        refine ⟨726495499279670094686135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1937321331412453585829693 726495499279670094686135)
        ·
          refine ⟨1089743248919505142029203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726495499279670094686135 1089743248919505142029203)
          ·
            refine ⟨1634614873379257713043805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089743248919505142029203 1634614873379257713043805)
            ·
              refine ⟨612980577517221642391427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634614873379257713043805 612980577517221642391427)
              ·
                refine ⟨919470866275832463587141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612980577517221642391427 919470866275832463587141)
                ·
                  refine ⟨172400787426718586922589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919470866275832463587141 172400787426718586922589)
                  ·
                    rfl

theorem cell20_377718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_377718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377718 prefixEnd_377718 := by exact prefixLift 377718
  have htrace : WordTrace (prefixWord ++ tailWord_377718) baseStart_377718 baseEnd_377718 := by
    simpa [prefixWord, tailWord_377718, baseEnd_377718] using wordTrace_append hprefix tailTrace_377718
  have hstable : (prefixWord ++ tailWord_377718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377718).length < 2 ^ (prefixWord ++ tailWord_377718).sum := by decide
  have hdescent : baseEnd_377718 < baseStart_377718 := by decide
  rcases family_descends (prefixWord ++ tailWord_377718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377767 : List Nat := [1, 1, 6, 1, 11]
def baseStart_377767 : Nat := 118140960795 + 377767 * 2 ^ 59
def prefixEnd_377767 : Nat := 4983230072969 + 3 ^ 40 * 377767 * 2
def baseEnd_377767 : Nat := 2128680893356693756655

theorem tailTrace_377767 : CollatzResearch.WordTrace tailWord_377767 prefixEnd_377767 2128680893356693756655 := by
  unfold tailWord_377767
  simp only [CollatzResearch.WordTrace]
  refine ⟨13778294422422151312211555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9185529614948100874807703 13778294422422151312211555)
  ·
    refine ⟨20667441633633226968317333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13778294422422151312211555 20667441633633226968317333)
    ·
      refine ⟨968786326576557514139875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20667441633633226968317333 968786326576557514139875)
      ·
        refine ⟨1453179489864836271209813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968786326576557514139875 1453179489864836271209813)
        ·
          refine ⟨2128680893356693756655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1453179489864836271209813 2128680893356693756655)
          ·
            rfl

theorem cell20_377767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 11].length) (baseStart_377767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377767 prefixEnd_377767 := by exact prefixLift 377767
  have htrace : WordTrace (prefixWord ++ tailWord_377767) baseStart_377767 baseEnd_377767 := by
    simpa [prefixWord, tailWord_377767, baseEnd_377767] using wordTrace_append hprefix tailTrace_377767
  have hstable : (prefixWord ++ tailWord_377767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377767).length < 2 ^ (prefixWord ++ tailWord_377767).sum := by decide
  have hdescent : baseEnd_377767 < baseStart_377767 := by decide
  rcases family_descends (prefixWord ++ tailWord_377767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377780 : List Nat := [2, 5, 2, 1, 1, 3, 1, 5]
def baseStart_377780 : Nat := 118140960795 + 377780 * 2 ^ 59
def prefixEnd_377780 : Nat := 4983230072969 + 3 ^ 40 * 377780 * 2
def baseEnd_377780 : Nat := 57476361972040642285223

theorem tailTrace_377780 : CollatzResearch.WordTrace tailWord_377780 prefixEnd_377780 57476361972040642285223 := by
  unfold tailWord_377780
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889384285687527266217397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9185845714250036354956529 6889384285687527266217397)
  ·
    refine ⟨645879776783205681207881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6889384285687527266217397 645879776783205681207881)
    ·
      refine ⟨484409832587404260905911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 645879776783205681207881 484409832587404260905911)
      ·
        refine ⟨726614748881106391358867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484409832587404260905911 726614748881106391358867)
        ·
          refine ⟨1089922123321659587038301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726614748881106391358867 1089922123321659587038301)
          ·
            refine ⟨408720796245622345139363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1089922123321659587038301 408720796245622345139363)
            ·
              refine ⟨613081194368433517709045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408720796245622345139363 613081194368433517709045)
              ·
                refine ⟨57476361972040642285223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613081194368433517709045 57476361972040642285223)
                ·
                  rfl

theorem cell20_377780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_377780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_377780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_377780 prefixEnd_377780 := by exact prefixLift 377780
  have htrace : WordTrace (prefixWord ++ tailWord_377780) baseStart_377780 baseEnd_377780 := by
    simpa [prefixWord, tailWord_377780, baseEnd_377780] using wordTrace_append hprefix tailTrace_377780
  have hstable : (prefixWord ++ tailWord_377780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377780).length < 2 ^ (prefixWord ++ tailWord_377780).sum := by decide
  have hdescent : baseEnd_377780 < baseStart_377780 := by decide
  rcases family_descends (prefixWord ++ tailWord_377780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
