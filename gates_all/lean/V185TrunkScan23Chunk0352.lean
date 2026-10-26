import V185TrunkScan23Chunk0351

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2082407 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_2082407 : Nat := 118140960795 + 2082407 * 2 ^ 59
def prefixEnd_2082407 : Nat := 4983230072969 + 3 ^ 40 * 2082407 * 2
def baseEnd_2082407 : Nat := 1069275709287339306735691

theorem tailTrace_2082407 : CollatzResearch.WordTrace tailWord_2082407 prefixEnd_2082407 1069275709287339306735691 := by
  unfold tailWord_2082407
  simp only [CollatzResearch.WordTrace]
  refine ⟨75951622966802560646221475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50634415311201707097480983 75951622966802560646221475)
  ·
    refine ⟨113927434450203840969332213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75951622966802560646221475 113927434450203840969332213)
    ·
      refine ⟨10680696979706610090874895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113927434450203840969332213 10680696979706610090874895)
      ·
        refine ⟨16021045469559915136312343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680696979706610090874895 16021045469559915136312343)
        ·
          refine ⟨24031568204339872704468515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16021045469559915136312343 24031568204339872704468515)
          ·
            refine ⟨36047352306509809056702773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24031568204339872704468515 36047352306509809056702773)
            ·
              refine ⟨3379439278735294599065885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36047352306509809056702773 3379439278735294599065885)
              ·
                refine ⟨1267289729525735474649707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3379439278735294599065885 1267289729525735474649707)
                ·
                  refine ⟨1900934594288603211974561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267289729525735474649707 1900934594288603211974561)
                  ·
                    refine ⟨1425700945716452408980921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1900934594288603211974561 1425700945716452408980921)
                    ·
                      refine ⟨1069275709287339306735691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425700945716452408980921 1069275709287339306735691)
                      ·
                        rfl

theorem cell23_2082407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_2082407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082407 prefixEnd_2082407 := by exact prefixLift 2082407
  have htrace : WordTrace (prefixWord ++ tailWord_2082407) baseStart_2082407 baseEnd_2082407 := by
    simpa [prefixWord, tailWord_2082407, baseEnd_2082407] using wordTrace_append hprefix tailTrace_2082407
  have hstable : (prefixWord ++ tailWord_2082407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082407).length < 2 ^ (prefixWord ++ tailWord_2082407).sum := by decide
  have hdescent : baseEnd_2082407 < baseStart_2082407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082413 : List Nat := [1, 5, 1, 1, 5, 1, 9]
def baseStart_2082413 : Nat := 118140960795 + 2082413 * 2 ^ 59
def prefixEnd_2082413 : Nat := 4983230072969 + 3 ^ 40 * 2082413 * 2
def baseEnd_2082413 : Nat := 13200972718163781274823

theorem tailTrace_2082413 : CollatzResearch.WordTrace tailWord_2082413 prefixEnd_2082413 13200972718163781274823 := by
  unfold tailWord_2082413
  simp only [CollatzResearch.WordTrace]
  refine ⟨75951841804780823670939893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50634561203187215780626595 75951841804780823670939893)
  ·
    refine ⟨7120485169198202219150615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75951841804780823670939893 7120485169198202219150615)
    ·
      refine ⟨10680727753797303328725923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120485169198202219150615 10680727753797303328725923)
      ·
        refine ⟨16021091630695954993088885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680727753797303328725923 16021091630695954993088885)
        ·
          refine ⟨1501977340377745780602083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16021091630695954993088885 1501977340377745780602083)
          ·
            refine ⟨2252966010566618670903125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501977340377745780602083 2252966010566618670903125)
            ·
              refine ⟨13200972718163781274823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2252966010566618670903125 13200972718163781274823)
              ·
                rfl

theorem cell23_2082413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 9].length) (baseStart_2082413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082413 prefixEnd_2082413 := by exact prefixLift 2082413
  have htrace : WordTrace (prefixWord ++ tailWord_2082413) baseStart_2082413 baseEnd_2082413 := by
    simpa [prefixWord, tailWord_2082413, baseEnd_2082413] using wordTrace_append hprefix tailTrace_2082413
  have hstable : (prefixWord ++ tailWord_2082413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082413).length < 2 ^ (prefixWord ++ tailWord_2082413).sum := by decide
  have hdescent : baseEnd_2082413 < baseStart_2082413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082423 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_2082423 : Nat := 118140960795 + 2082423 * 2 ^ 59
def prefixEnd_2082423 : Nat := 4983230072969 + 3 ^ 40 * 2082423 * 2
def baseEnd_2082423 : Nat := 1069283924977811244135617

theorem tailTrace_2082423 : CollatzResearch.WordTrace tailWord_2082423 prefixEnd_2082423 1069283924977811244135617 := by
  unfold tailWord_2082423
  simp only [CollatzResearch.WordTrace]
  refine ⟨75952206534744595378803923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50634804356496396919202615 75952206534744595378803923)
  ·
    refine ⟨113928309802116893068205885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75952206534744595378803923 113928309802116893068205885)
    ·
      refine ⟨42723116175793834900577207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113928309802116893068205885 42723116175793834900577207)
      ·
        refine ⟨64084674263690752350865811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42723116175793834900577207 64084674263690752350865811)
        ·
          refine ⟨96127011395536128526298717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64084674263690752350865811 96127011395536128526298717)
          ·
            refine ⟨36047629273326048197362019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96127011395536128526298717 36047629273326048197362019)
            ·
              refine ⟨54071443909989072296043029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36047629273326048197362019 54071443909989072296043029)
              ·
                refine ⟨2534598933280737763877017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54071443909989072296043029 2534598933280737763877017)
                ·
                  refine ⟨1900949199960553322907763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534598933280737763877017 1900949199960553322907763)
                  ·
                    refine ⟨2851423799940829984361645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900949199960553322907763 2851423799940829984361645)
                    ·
                      refine ⟨1069283924977811244135617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851423799940829984361645 1069283924977811244135617)
                      ·
                        rfl

theorem cell23_2082423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_2082423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082423 prefixEnd_2082423 := by exact prefixLift 2082423
  have htrace : WordTrace (prefixWord ++ tailWord_2082423) baseStart_2082423 baseEnd_2082423 := by
    simpa [prefixWord, tailWord_2082423, baseEnd_2082423] using wordTrace_append hprefix tailTrace_2082423
  have hstable : (prefixWord ++ tailWord_2082423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082423).length < 2 ^ (prefixWord ++ tailWord_2082423).sum := by decide
  have hdescent : baseEnd_2082423 < baseStart_2082423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082480 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 2, 2, 2]
def baseStart_2082480 : Nat := 118140960795 + 2082480 * 2 ^ 59
def prefixEnd_2082480 : Nat := 4983230072969 + 3 ^ 40 * 2082480 * 2
def baseEnd_2082480 : Nat := 1069313193375117521122855

theorem tailTrace_2082480 : CollatzResearch.WordTrace tailWord_2082480 prefixEnd_2082480 1069313193375117521122855 := by
  unfold tailWord_2082480
  simp only [CollatzResearch.WordTrace]
  refine ⟨37977142747769047056814447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50636190330358729409085929 37977142747769047056814447)
  ·
    refine ⟨56965714121653570585221671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37977142747769047056814447 56965714121653570585221671)
    ·
      refine ⟨85448571182480355877832507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56965714121653570585221671 85448571182480355877832507)
      ·
        refine ⟨128172856773720533816748761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85448571182480355877832507 128172856773720533816748761)
        ·
          refine ⟨96129642580290400362561571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128172856773720533816748761 96129642580290400362561571)
          ·
            refine ⟨144194463870435600543842357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96129642580290400362561571 144194463870435600543842357)
            ·
              refine ⟨13518230987853337550985221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144194463870435600543842357 13518230987853337550985221)
              ·
                refine ⟨2534668310222500790809729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13518230987853337550985221 2534668310222500790809729)
                ·
                  refine ⟨1901001232666875593107297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534668310222500790809729 1901001232666875593107297)
                  ·
                    refine ⟨1425750924500156694830473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1901001232666875593107297 1425750924500156694830473)
                    ·
                      refine ⟨1069313193375117521122855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425750924500156694830473 1069313193375117521122855)
                      ·
                        rfl

theorem cell23_2082480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 2, 2].length) (baseStart_2082480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082480 prefixEnd_2082480 := by exact prefixLift 2082480
  have htrace : WordTrace (prefixWord ++ tailWord_2082480) baseStart_2082480 baseEnd_2082480 := by
    simpa [prefixWord, tailWord_2082480, baseEnd_2082480] using wordTrace_append hprefix tailTrace_2082480
  have hstable : (prefixWord ++ tailWord_2082480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082480).length < 2 ^ (prefixWord ++ tailWord_2082480).sum := by decide
  have hdescent : baseEnd_2082480 < baseStart_2082480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082518 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2082518 : Nat := 118140960795 + 2082518 * 2 ^ 59
def prefixEnd_2082518 : Nat := 4983230072969 + 3 ^ 40 * 2082518 * 2
def baseEnd_2082518 : Nat := 1069332705639988372447681

theorem tailTrace_2082518 : CollatzResearch.WordTrace tailWord_2082518 prefixEnd_2082518 1069332705639988372447681 := by
  unfold tailWord_2082518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747229466837526662719513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50637114312933617735674805 4747229466837526662719513)
  ·
    refine ⟨3560422100128144997039635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4747229466837526662719513 3560422100128144997039635)
    ·
      refine ⟨5340633150192217495559453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560422100128144997039635 5340633150192217495559453)
      ·
        refine ⟨2002737431322081560834795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5340633150192217495559453 2002737431322081560834795)
        ·
          refine ⟨3004106146983122341252193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002737431322081560834795 3004106146983122341252193)
          ·
            refine ⟨2253079610237341755939145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004106146983122341252193 2253079610237341755939145)
            ·
              refine ⟨1689809707678006316954359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253079610237341755939145 1689809707678006316954359)
              ·
                refine ⟨2534714561517009475431539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689809707678006316954359 2534714561517009475431539)
                ·
                  refine ⟨3802071842275514213147309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534714561517009475431539 3802071842275514213147309)
                  ·
                    refine ⟨1425776940853317829930241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802071842275514213147309 1425776940853317829930241)
                    ·
                      refine ⟨1069332705639988372447681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425776940853317829930241 1069332705639988372447681)
                      ·
                        rfl

theorem cell23_2082518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2082518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082518 prefixEnd_2082518 := by exact prefixLift 2082518
  have htrace : WordTrace (prefixWord ++ tailWord_2082518) baseStart_2082518 baseEnd_2082518 := by
    simpa [prefixWord, tailWord_2082518, baseEnd_2082518] using wordTrace_append hprefix tailTrace_2082518
  have hstable : (prefixWord ++ tailWord_2082518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082518).length < 2 ^ (prefixWord ++ tailWord_2082518).sum := by decide
  have hdescent : baseEnd_2082518 < baseStart_2082518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082531 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2082531 : Nat := 118140960795 + 2082531 * 2 ^ 59
def prefixEnd_2082531 : Nat := 4983230072969 + 3 ^ 40 * 2082531 * 2
def baseEnd_2082531 : Nat := 1069339380888496821585121

theorem tailTrace_2082531 : CollatzResearch.WordTrace tailWord_2082531 prefixEnd_2082531 1069339380888496821585121 := by
  unfold tailWord_2082531
  simp only [CollatzResearch.WordTrace]
  refine ⟨75956145618353329823735447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50637430412235553215823631 75956145618353329823735447)
  ·
    refine ⟨113934218427529994735603171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75956145618353329823735447 113934218427529994735603171)
    ·
      refine ⟨170901327641294992103404757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113934218427529994735603171 170901327641294992103404757)
      ·
        refine ⟨4005499866592851377423549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 170901327641294992103404757 4005499866592851377423549)
        ·
          refine ⟨1502062449972319266533831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4005499866592851377423549 1502062449972319266533831)
          ·
            refine ⟨2253093674958478899800747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502062449972319266533831 2253093674958478899800747)
            ·
              refine ⟨3379640512437718349701121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253093674958478899800747 3379640512437718349701121)
              ·
                refine ⟨2534730384328288762275841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379640512437718349701121 2534730384328288762275841)
                ·
                  refine ⟨1901047788246216571706881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534730384328288762275841 1901047788246216571706881)
                  ·
                    refine ⟨1425785841184662428780161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1901047788246216571706881 1425785841184662428780161)
                    ·
                      refine ⟨1069339380888496821585121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425785841184662428780161 1069339380888496821585121)
                      ·
                        rfl

theorem cell23_2082531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2082531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082531 prefixEnd_2082531 := by exact prefixLift 2082531
  have htrace : WordTrace (prefixWord ++ tailWord_2082531) baseStart_2082531 baseEnd_2082531 := by
    simpa [prefixWord, tailWord_2082531, baseEnd_2082531] using wordTrace_append hprefix tailTrace_2082531
  have hstable : (prefixWord ++ tailWord_2082531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082531).length < 2 ^ (prefixWord ++ tailWord_2082531).sum := by decide
  have hdescent : baseEnd_2082531 < baseStart_2082531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082548 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2082548 : Nat := 118140960795 + 2082548 * 2 ^ 59
def prefixEnd_2082548 : Nat := 4983230072969 + 3 ^ 40 * 2082548 * 2
def baseEnd_2082548 : Nat := 1069348110059623255072543

theorem tailTrace_2082548 : CollatzResearch.WordTrace tailWord_2082548 prefixEnd_2082548 1069348110059623255072543 := by
  unfold tailWord_2082548
  simp only [CollatzResearch.WordTrace]
  refine ⟨37978382829645870863552149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50637843772861161151402865 37978382829645870863552149)
  ·
    refine ⟨1780236695139650196729007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37978382829645870863552149 1780236695139650196729007)
    ·
      refine ⟨2670355042709475295093511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780236695139650196729007 2670355042709475295093511)
      ·
        refine ⟨4005532564064212942640267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670355042709475295093511 4005532564064212942640267)
        ·
          refine ⟨6008298846096319413960401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005532564064212942640267 6008298846096319413960401)
          ·
            refine ⟨4506224134572239560470301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6008298846096319413960401 4506224134572239560470301)
            ·
              refine ⟨1689834050464589835176363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4506224134572239560470301 1689834050464589835176363)
              ·
                refine ⟨2534751075696884752764545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689834050464589835176363 2534751075696884752764545)
                ·
                  refine ⟨1901063306772663564573409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534751075696884752764545 1901063306772663564573409)
                  ·
                    refine ⟨1425797480079497673430057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1901063306772663564573409 1425797480079497673430057)
                    ·
                      refine ⟨1069348110059623255072543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425797480079497673430057 1069348110059623255072543)
                      ·
                        rfl

theorem cell23_2082548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2082548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082548 prefixEnd_2082548 := by exact prefixLift 2082548
  have htrace : WordTrace (prefixWord ++ tailWord_2082548) baseStart_2082548 baseEnd_2082548 := by
    simpa [prefixWord, tailWord_2082548, baseEnd_2082548] using wordTrace_append hprefix tailTrace_2082548
  have hstable : (prefixWord ++ tailWord_2082548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082548).length < 2 ^ (prefixWord ++ tailWord_2082548).sum := by decide
  have hdescent : baseEnd_2082548 < baseStart_2082548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082563 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 3, 4]
def baseStart_2082563 : Nat := 118140960795 + 2082563 * 2 ^ 59
def prefixEnd_2082563 : Nat := 4983230072969 + 3 ^ 40 * 2082563 * 2
def baseEnd_2082563 : Nat := 356451937423146898794991

theorem tailTrace_2082563 : CollatzResearch.WordTrace tailWord_2082563 prefixEnd_2082563 356451937423146898794991 := by
  unfold tailWord_2082563
  simp only [CollatzResearch.WordTrace]
  refine ⟨75957312754237399288900343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50638208502824932859266895 75957312754237399288900343)
  ·
    refine ⟨113935969131356098933350515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75957312754237399288900343 113935969131356098933350515)
    ·
      refine ⟨170903953697034148400025773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113935969131356098933350515 170903953697034148400025773)
      ·
        refine ⟨64088982636387805650009665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170903953697034148400025773 64088982636387805650009665)
        ·
          refine ⟨48066736977290854237507249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64088982636387805650009665 48066736977290854237507249)
          ·
            refine ⟨36050052732968140678130437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48066736977290854237507249 36050052732968140678130437)
            ·
              refine ⟨6759384887431526377149457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36050052732968140678130437 6759384887431526377149457)
              ·
                refine ⟨5069538665573644782862093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6759384887431526377149457 5069538665573644782862093)
                ·
                  refine ⟨1901076999590116793573285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5069538665573644782862093 1901076999590116793573285)
                  ·
                    refine ⟨356451937423146898794991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901076999590116793573285 356451937423146898794991)
                    ·
                      rfl

theorem cell23_2082563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 4].length) (baseStart_2082563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082563 prefixEnd_2082563 := by exact prefixLift 2082563
  have htrace : WordTrace (prefixWord ++ tailWord_2082563) baseStart_2082563 baseEnd_2082563 := by
    simpa [prefixWord, tailWord_2082563, baseEnd_2082563] using wordTrace_append hprefix tailTrace_2082563
  have hstable : (prefixWord ++ tailWord_2082563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082563).length < 2 ^ (prefixWord ++ tailWord_2082563).sum := by decide
  have hdescent : baseEnd_2082563 < baseStart_2082563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082610 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_2082610 : Nat := 118140960795 + 2082610 * 2 ^ 59
def prefixEnd_2082610 : Nat := 4983230072969 + 3 ^ 40 * 2082610 * 2
def baseEnd_2082610 : Nat := 118819993984466890277473

theorem tailTrace_2082610 : CollatzResearch.WordTrace tailWord_2082610 prefixEnd_2082610 118819993984466890277473 := by
  unfold tailWord_2082610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989756746266781578965321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50639351323378084210574189 18989756746266781578965321)
  ·
    refine ⟨14242317559700086184223991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18989756746266781578965321 14242317559700086184223991)
    ·
      refine ⟨21363476339550129276335987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242317559700086184223991 21363476339550129276335987)
      ·
        refine ⟨32045214509325193914503981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21363476339550129276335987 32045214509325193914503981)
        ·
          refine ⟨12016955440996947717938993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32045214509325193914503981 12016955440996947717938993)
          ·
            refine ⟨9012716580747710788454245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12016955440996947717938993 9012716580747710788454245)
            ·
              refine ⟨1689884358890195772835171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9012716580747710788454245 1689884358890195772835171)
              ·
                refine ⟨2534826538335293659252757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689884358890195772835171 2534826538335293659252757)
                ·
                  refine ⟨118819993984466890277473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2534826538335293659252757 118819993984466890277473)
                  ·
                    rfl

theorem cell23_2082610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_2082610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082610 prefixEnd_2082610 := by exact prefixLift 2082610
  have htrace : WordTrace (prefixWord ++ tailWord_2082610) baseStart_2082610 baseEnd_2082610 := by
    simpa [prefixWord, tailWord_2082610, baseEnd_2082610] using wordTrace_append hprefix tailTrace_2082610
  have hstable : (prefixWord ++ tailWord_2082610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082610).length < 2 ^ (prefixWord ++ tailWord_2082610).sum := by decide
  have hdescent : baseEnd_2082610 < baseStart_2082610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082620 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_2082620 : Nat := 118140960795 + 2082620 * 2 ^ 59
def prefixEnd_2082620 : Nat := 4983230072969 + 3 ^ 40 * 2082620 * 2
def baseEnd_2082620 : Nat := 1069385080666746973372211

theorem tailTrace_2082620 : CollatzResearch.WordTrace tailWord_2082620 prefixEnd_2082620 1069385080666746973372211 := by
  unfold tailWord_2082620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37979695857515449011862657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50639594476687265349150209 37979695857515449011862657)
  ·
    refine ⟨28484771893136586758896993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37979695857515449011862657 28484771893136586758896993)
    ·
      refine ⟨21363578919852440069172745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28484771893136586758896993 21363578919852440069172745)
      ·
        refine ⟨16022684189889330051879559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21363578919852440069172745 16022684189889330051879559)
        ·
          refine ⟨24034026284833995077819339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16022684189889330051879559 24034026284833995077819339)
          ·
            refine ⟨36051039427250992616729009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24034026284833995077819339 36051039427250992616729009)
            ·
              refine ⟨27038279570438244462546757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36051039427250992616729009 27038279570438244462546757)
              ·
                refine ⟨5069677419457170836727517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27038279570438244462546757 5069677419457170836727517)
                ·
                  refine ⟨1901129032296439063772819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5069677419457170836727517 1901129032296439063772819)
                  ·
                    refine ⟨2851693548444658595659229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1901129032296439063772819 2851693548444658595659229)
                    ·
                      refine ⟨1069385080666746973372211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851693548444658595659229 1069385080666746973372211)
                      ·
                        rfl

theorem cell23_2082620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_2082620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082620 prefixEnd_2082620 := by exact prefixLift 2082620
  have htrace : WordTrace (prefixWord ++ tailWord_2082620) baseStart_2082620 baseEnd_2082620 := by
    simpa [prefixWord, tailWord_2082620, baseEnd_2082620] using wordTrace_append hprefix tailTrace_2082620
  have hstable : (prefixWord ++ tailWord_2082620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082620).length < 2 ^ (prefixWord ++ tailWord_2082620).sum := by decide
  have hdescent : baseEnd_2082620 < baseStart_2082620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082663 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2082663 : Nat := 118140960795 + 2082663 * 2 ^ 59
def prefixEnd_2082663 : Nat := 4983230072969 + 3 ^ 40 * 2082663 * 2
def baseEnd_2082663 : Nat := 1069407160334890305134513

theorem tailTrace_2082663 : CollatzResearch.WordTrace tailWord_2082663 prefixEnd_2082663 1069407160334890305134513 := by
  unfold tailWord_2082663
  simp only [CollatzResearch.WordTrace]
  refine ⟨75960960053875116367540643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50640640035916744245027095 75960960053875116367540643)
  ·
    refine ⟨113941440080812674551310965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75960960053875116367540643 113941440080812674551310965)
    ·
      refine ⟨10682010007576188239185403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113941440080812674551310965 10682010007576188239185403)
      ·
        refine ⟨16023015011364282358778105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682010007576188239185403 16023015011364282358778105)
        ·
          refine ⟨12017261258523211769083579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16023015011364282358778105 12017261258523211769083579)
          ·
            refine ⟨18025891887784817653625369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12017261258523211769083579 18025891887784817653625369)
            ·
              refine ⟨13519418915838613240219027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18025891887784817653625369 13519418915838613240219027)
              ·
                refine ⟨20279128373757919860328541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13519418915838613240219027 20279128373757919860328541)
                ·
                  refine ⟨7604673140159219947623203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20279128373757919860328541 7604673140159219947623203)
                  ·
                    refine ⟨11407009710238829921434805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7604673140159219947623203 11407009710238829921434805)
                    ·
                      refine ⟨1069407160334890305134513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11407009710238829921434805 1069407160334890305134513)
                      ·
                        rfl

theorem cell23_2082663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2082663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082663 prefixEnd_2082663 := by exact prefixLift 2082663
  have htrace : WordTrace (prefixWord ++ tailWord_2082663) baseStart_2082663 baseEnd_2082663 := by
    simpa [prefixWord, tailWord_2082663, baseEnd_2082663] using wordTrace_append hprefix tailTrace_2082663
  have hstable : (prefixWord ++ tailWord_2082663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082663).length < 2 ^ (prefixWord ++ tailWord_2082663).sum := by decide
  have hdescent : baseEnd_2082663 < baseStart_2082663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082670 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2082670 : Nat := 118140960795 + 2082670 * 2 ^ 59
def prefixEnd_2082670 : Nat := 4983230072969 + 3 ^ 40 * 2082670 * 2
def baseEnd_2082670 : Nat := 356470251566490592582327

theorem tailTrace_2082670 : CollatzResearch.WordTrace tailWord_2082670 prefixEnd_2082670 356470251566490592582327 := by
  unfold tailWord_2082670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495151920606219570380683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50640810243233171042030309 9495151920606219570380683)
  ·
    refine ⟨14242727880909329355571025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495151920606219570380683 14242727880909329355571025)
    ·
      refine ⟨10682045910681997016678269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14242727880909329355571025 10682045910681997016678269)
      ·
        refine ⟨4005767216505748881254351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10682045910681997016678269 4005767216505748881254351)
        ·
          refine ⟨6008650824758623321881527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005767216505748881254351 6008650824758623321881527)
          ·
            refine ⟨9012976237137934982822291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008650824758623321881527 9012976237137934982822291)
            ·
              refine ⟨13519464355706902474233437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012976237137934982822291 13519464355706902474233437)
              ·
                refine ⟨5069799133390088427837539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13519464355706902474233437 5069799133390088427837539)
                ·
                  refine ⟨7604698700085132641756309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069799133390088427837539 7604698700085132641756309)
                  ·
                    refine ⟨356470251566490592582327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7604698700085132641756309 356470251566490592582327)
                    ·
                      rfl

theorem cell23_2082670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2082670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082670 prefixEnd_2082670 := by exact prefixLift 2082670
  have htrace : WordTrace (prefixWord ++ tailWord_2082670) baseStart_2082670 baseEnd_2082670 := by
    simpa [prefixWord, tailWord_2082670, baseEnd_2082670] using wordTrace_append hprefix tailTrace_2082670
  have hstable : (prefixWord ++ tailWord_2082670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082670).length < 2 ^ (prefixWord ++ tailWord_2082670).sum := by decide
  have hdescent : baseEnd_2082670 < baseStart_2082670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082727 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2082727 : Nat := 118140960795 + 2082727 * 2 ^ 59
def prefixEnd_2082727 : Nat := 4983230072969 + 3 ^ 40 * 2082727 * 2
def baseEnd_2082727 : Nat := 1069440023096778054734219

theorem tailTrace_2082727 : CollatzResearch.WordTrace tailWord_2082727 prefixEnd_2082727 1069440023096778054734219 := by
  unfold tailWord_2082727
  simp only [CollatzResearch.WordTrace]
  refine ⟨75963294325643255297870435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50642196217095503531913623 75963294325643255297870435)
  ·
    refine ⟨113944941488464882946805653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75963294325643255297870435 113944941488464882946805653)
    ·
      refine ⟨5341169132271791388131515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113944941488464882946805653 5341169132271791388131515)
      ·
        refine ⟨8011753698407687082197273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341169132271791388131515 8011753698407687082197273)
        ·
          refine ⟨6008815273805765311647955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8011753698407687082197273 6008815273805765311647955)
          ·
            refine ⟨9013222910708647967471933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008815273805765311647955 9013222910708647967471933)
            ·
              refine ⟨3379958591515742987801975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9013222910708647967471933 3379958591515742987801975)
              ·
                refine ⟨5069937887273614481702963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379958591515742987801975 5069937887273614481702963)
                ·
                  refine ⟨7604906830910421722554445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069937887273614481702963 7604906830910421722554445)
                  ·
                    refine ⟨2851840061591408145957917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7604906830910421722554445 2851840061591408145957917)
                    ·
                      refine ⟨1069440023096778054734219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851840061591408145957917 1069440023096778054734219)
                      ·
                        rfl

theorem cell23_2082727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2082727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082727 prefixEnd_2082727 := by exact prefixLift 2082727
  have htrace : WordTrace (prefixWord ++ tailWord_2082727) baseStart_2082727 baseEnd_2082727 := by
    simpa [prefixWord, tailWord_2082727, baseEnd_2082727] using wordTrace_append hprefix tailTrace_2082727
  have hstable : (prefixWord ++ tailWord_2082727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082727).length < 2 ^ (prefixWord ++ tailWord_2082727).sum := by decide
  have hdescent : baseEnd_2082727 < baseStart_2082727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082734 : List Nat := [4, 1, 5, 1, 1, 1, 1, 9]
def baseStart_2082734 : Nat := 118140960795 + 2082734 * 2 ^ 59
def prefixEnd_2082734 : Nat := 4983230072969 + 3 ^ 40 * 2082734 * 2
def baseEnd_2082734 : Nat := 39609022868939241753581

theorem tailTrace_2082734 : CollatzResearch.WordTrace tailWord_2082734 prefixEnd_2082734 39609022868939241753581 := by
  unfold tailWord_2082734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495443704577236936671907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50642366424411930328916837 9495443704577236936671907)
  ·
    refine ⟨14243165556865855405007861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495443704577236936671907 14243165556865855405007861)
    ·
      refine ⟨1335296770956173944219487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14243165556865855405007861 1335296770956173944219487)
      ·
        refine ⟨2002945156434260916329231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335296770956173944219487 2002945156434260916329231)
        ·
          refine ⟨3004417734651391374493847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002945156434260916329231 3004417734651391374493847)
          ·
            refine ⟨4506626601977087061740771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004417734651391374493847 4506626601977087061740771)
            ·
              refine ⟨6759939902965630592611157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506626601977087061740771 6759939902965630592611157)
              ·
                refine ⟨39609022868939241753581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6759939902965630592611157 39609022868939241753581)
                ·
                  rfl

theorem cell23_2082734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_2082734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082734 prefixEnd_2082734 := by exact prefixLift 2082734
  have htrace : WordTrace (prefixWord ++ tailWord_2082734) baseStart_2082734 baseEnd_2082734 := by
    simpa [prefixWord, tailWord_2082734, baseEnd_2082734] using wordTrace_append hprefix tailTrace_2082734
  have hstable : (prefixWord ++ tailWord_2082734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082734).length < 2 ^ (prefixWord ++ tailWord_2082734).sum := by decide
  have hdescent : baseEnd_2082734 < baseStart_2082734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082767 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 4, 2, 2]
def baseStart_2082767 : Nat := 118140960795 + 2082767 * 2 ^ 59
def prefixEnd_2082767 : Nat := 4983230072969 + 3 ^ 40 * 2082767 * 2
def baseEnd_2082767 : Nat := 1069460562322957898234035

theorem tailTrace_2082767 : CollatzResearch.WordTrace tailWord_2082767 prefixEnd_2082767 1069460562322957898234035 := by
  unfold tailWord_2082767
  simp only [CollatzResearch.WordTrace]
  refine ⟨75964753245498342129326555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50643168830332228086217703 75964753245498342129326555)
  ·
    refine ⟨113947129868247513193989833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75964753245498342129326555 113947129868247513193989833)
    ·
      refine ⟨85460347401185634895492375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113947129868247513193989833 85460347401185634895492375)
      ·
        refine ⟨128190521101778452343238563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85460347401185634895492375 128190521101778452343238563)
        ·
          refine ⟨192285781652667678514857845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128190521101778452343238563 192285781652667678514857845)
          ·
            refine ⟨18026792029937594860767923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192285781652667678514857845 18026792029937594860767923)
            ·
              refine ⟨27040188044906392291151885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18026792029937594860767923 27040188044906392291151885)
              ·
                refine ⟨10140070516839897109181957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27040188044906392291151885 10140070516839897109181957)
                ·
                  refine ⟨1901263221907480707971617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10140070516839897109181957 1901263221907480707971617)
                  ·
                    refine ⟨1425947416430610530978713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1901263221907480707971617 1425947416430610530978713)
                    ·
                      refine ⟨1069460562322957898234035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425947416430610530978713 1069460562322957898234035)
                      ·
                        rfl

theorem cell23_2082767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 2, 2].length) (baseStart_2082767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082767 prefixEnd_2082767 := by exact prefixLift 2082767
  have htrace : WordTrace (prefixWord ++ tailWord_2082767) baseStart_2082767 baseEnd_2082767 := by
    simpa [prefixWord, tailWord_2082767, baseEnd_2082767] using wordTrace_append hprefix tailTrace_2082767
  have hstable : (prefixWord ++ tailWord_2082767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082767).length < 2 ^ (prefixWord ++ tailWord_2082767).sum := by decide
  have hdescent : baseEnd_2082767 < baseStart_2082767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082778 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3]
def baseStart_2082778 : Nat := 118140960795 + 2082778 * 2 ^ 59
def prefixEnd_2082778 : Nat := 4983230072969 + 3 ^ 40 * 2082778 * 2
def baseEnd_2082778 : Nat := 1069466210610157355196485

theorem tailTrace_2082778 : CollatzResearch.WordTrace tailWord_2082778 prefixEnd_2082778 1069466210610157355196485 := by
  unfold tailWord_2082778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18991288612114622751994247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50643436298972327338651325 18991288612114622751994247)
  ·
    refine ⟨28486932918171934127991371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18991288612114622751994247 28486932918171934127991371)
    ·
      refine ⟨42730399377257901191987057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28486932918171934127991371 42730399377257901191987057)
      ·
        refine ⟨32047799532943425893990293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42730399377257901191987057 32047799532943425893990293)
        ·
          refine ⟨1502240603106723088780795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32047799532943425893990293 1502240603106723088780795)
          ·
            refine ⟨2253360904660084633171193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502240603106723088780795 2253360904660084633171193)
            ·
              refine ⟨1690020678495063474878395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253360904660084633171193 1690020678495063474878395)
              ·
                refine ⟨2535031017742595212317593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690020678495063474878395 2535031017742595212317593)
                ·
                  refine ⟨1901273263306946409238195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535031017742595212317593 1901273263306946409238195)
                  ·
                    refine ⟨2851909894960419613857293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1901273263306946409238195 2851909894960419613857293)
                    ·
                      refine ⟨1069466210610157355196485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851909894960419613857293 1069466210610157355196485)
                      ·
                        rfl

theorem cell23_2082778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_2082778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082778 prefixEnd_2082778 := by exact prefixLift 2082778
  have htrace : WordTrace (prefixWord ++ tailWord_2082778) baseStart_2082778 baseEnd_2082778 := by
    simpa [prefixWord, tailWord_2082778, baseEnd_2082778] using wordTrace_append hprefix tailTrace_2082778
  have hstable : (prefixWord ++ tailWord_2082778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082778).length < 2 ^ (prefixWord ++ tailWord_2082778).sum := by decide
  have hdescent : baseEnd_2082778 < baseStart_2082778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082803 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 1, 7]
def baseStart_2082803 : Nat := 118140960795 + 2082803 * 2 ^ 59
def prefixEnd_2082803 : Nat := 4983230072969 + 3 ^ 40 * 2082803 * 2
def baseEnd_2082803 : Nat := 356493015875506585794623

theorem tailTrace_2082803 : CollatzResearch.WordTrace tailWord_2082803 prefixEnd_2082803 356493015875506585794623 := by
  unfold tailWord_2082803
  simp only [CollatzResearch.WordTrace]
  refine ⟨75966066273367920277637063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50644044182245280185091375 75966066273367920277637063)
  ·
    refine ⟨113949099410051880416455595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75966066273367920277637063 113949099410051880416455595)
    ·
      refine ⟨170923649115077820624683393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113949099410051880416455595 170923649115077820624683393)
      ·
        refine ⟨128192736836308365468512545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170923649115077820624683393 128192736836308365468512545)
        ·
          refine ⟨96144552627231274101384409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128192736836308365468512545 96144552627231274101384409)
          ·
            refine ⟨72108414470423455576038307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96144552627231274101384409 72108414470423455576038307)
            ·
              refine ⟨108162621705635183364057461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72108414470423455576038307 108162621705635183364057461)
              ·
                refine ⟨10140245784903298440380387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108162621705635183364057461 10140245784903298440380387)
                ·
                  refine ⟨15210368677354947660570581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140245784903298440380387 15210368677354947660570581)
                  ·
                    refine ⟨356493015875506585794623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15210368677354947660570581 356493015875506585794623)
                    ·
                      rfl

theorem cell23_2082803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 7].length) (baseStart_2082803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082803 prefixEnd_2082803 := by exact prefixLift 2082803
  have htrace : WordTrace (prefixWord ++ tailWord_2082803) baseStart_2082803 baseEnd_2082803 := by
    simpa [prefixWord, tailWord_2082803, baseEnd_2082803] using wordTrace_append hprefix tailTrace_2082803
  have hstable : (prefixWord ++ tailWord_2082803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082803).length < 2 ^ (prefixWord ++ tailWord_2082803).sum := by decide
  have hdescent : baseEnd_2082803 < baseStart_2082803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082830 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2082830 : Nat := 118140960795 + 2082830 * 2 ^ 59
def prefixEnd_2082830 : Nat := 4983230072969 + 3 ^ 40 * 2082830 * 2
def baseEnd_2082830 : Nat := 1069492911604191151746245

theorem tailTrace_2082830 : CollatzResearch.WordTrace tailWord_2082830 prefixEnd_2082830 1069492911604191151746245 := by
  unfold tailWord_2082830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495881380533762986108743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50644700696180069259246629 9495881380533762986108743)
  ·
    refine ⟨14243822070800644479163115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495881380533762986108743 14243822070800644479163115)
    ·
      refine ⟨21365733106200966718744673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14243822070800644479163115 21365733106200966718744673)
      ·
        refine ⟨16024299829650725039058505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21365733106200966718744673 16024299829650725039058505)
        ·
          refine ⟨12018224872238043779293879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16024299829650725039058505 12018224872238043779293879)
          ·
            refine ⟨18027337308357065668940819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018224872238043779293879 18027337308357065668940819)
            ·
              refine ⟨27041005962535598503411229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18027337308357065668940819 27041005962535598503411229)
              ·
                refine ⟨10140377235950849438779211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27041005962535598503411229 10140377235950849438779211)
                ·
                  refine ⟨15210565853926274158168817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140377235950849438779211 15210565853926274158168817)
                  ·
                    refine ⟨11407924390444705618626613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15210565853926274158168817 11407924390444705618626613)
                    ·
                      refine ⟨1069492911604191151746245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11407924390444705618626613 1069492911604191151746245)
                      ·
                        rfl

theorem cell23_2082830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2082830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082830 prefixEnd_2082830 := by exact prefixLift 2082830
  have htrace : WordTrace (prefixWord ++ tailWord_2082830) baseStart_2082830 baseEnd_2082830 := by
    simpa [prefixWord, tailWord_2082830, baseEnd_2082830] using wordTrace_append hprefix tailTrace_2082830
  have hstable : (prefixWord ++ tailWord_2082830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082830).length < 2 ^ (prefixWord ++ tailWord_2082830).sum := by decide
  have hdescent : baseEnd_2082830 < baseStart_2082830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082833 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_2082833 : Nat := 118140960795 + 2082833 * 2 ^ 59
def prefixEnd_2082833 : Nat := 4983230072969 + 3 ^ 40 * 2082833 * 2
def baseEnd_2082833 : Nat := 356498150682051546669577

theorem tailTrace_2082833 : CollatzResearch.WordTrace tailWord_2082833 prefixEnd_2082833 356498150682051546669577 := by
  unfold tailWord_2082833
  simp only [CollatzResearch.WordTrace]
  refine ⟨75967160463259235401229153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50644773642172823600819435 75967160463259235401229153)
  ·
    refine ⟨56975370347444426550921865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75967160463259235401229153 56975370347444426550921865)
    ·
      refine ⟨42731527760583319913191399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56975370347444426550921865 42731527760583319913191399)
      ·
        refine ⟨64097291640874979869787099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42731527760583319913191399 64097291640874979869787099)
        ·
          refine ⟨96145937461312469804680649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64097291640874979869787099 96145937461312469804680649)
          ·
            refine ⟨72109453095984352353510487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96145937461312469804680649 72109453095984352353510487)
            ·
              refine ⟨108164179643976528530265731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72109453095984352353510487 108164179643976528530265731)
              ·
                refine ⟨162246269465964792795398597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108164179643976528530265731 162246269465964792795398597)
                ·
                  refine ⟨30421175524868398649137237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162246269465964792795398597 30421175524868398649137237)
                  ·
                    refine ⟨356498150682051546669577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30421175524868398649137237 356498150682051546669577)
                    ·
                      rfl

theorem cell23_2082833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_2082833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082833 prefixEnd_2082833 := by exact prefixLift 2082833
  have htrace : WordTrace (prefixWord ++ tailWord_2082833) baseStart_2082833 baseEnd_2082833 := by
    simpa [prefixWord, tailWord_2082833, baseEnd_2082833] using wordTrace_append hprefix tailTrace_2082833
  have hstable : (prefixWord ++ tailWord_2082833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082833).length < 2 ^ (prefixWord ++ tailWord_2082833).sum := by decide
  have hdescent : baseEnd_2082833 < baseStart_2082833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082840 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2082840 : Nat := 118140960795 + 2082840 * 2 ^ 59
def prefixEnd_2082840 : Nat := 4983230072969 + 3 ^ 40 * 2082840 * 2
def baseEnd_2082840 : Nat := 1069498046410736112621199

theorem tailTrace_2082840 : CollatzResearch.WordTrace tailWord_2082840 prefixEnd_2082840 1069498046410736112621199 := by
  unfold tailWord_2082840
  simp only [CollatzResearch.WordTrace]
  refine ⟨37983707887116937798366987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50644943849489250397822649 37983707887116937798366987)
  ·
    refine ⟨56975561830675406697550481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37983707887116937798366987 56975561830675406697550481)
    ·
      refine ⟨42731671373006555023162861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56975561830675406697550481 42731671373006555023162861)
      ·
        refine ⟨16024376764877458133686073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42731671373006555023162861 16024376764877458133686073)
        ·
          refine ⟨12018282573658093600264555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16024376764877458133686073 12018282573658093600264555)
          ·
            refine ⟨18027423860487140400396833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018282573658093600264555 18027423860487140400396833)
            ·
              refine ⟨13520567895365355300297625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18027423860487140400396833 13520567895365355300297625)
              ·
                refine ⟨10140425921524016475223219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13520567895365355300297625 10140425921524016475223219)
                ·
                  refine ⟨15210638882286024712834829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140425921524016475223219 15210638882286024712834829)
                  ·
                    refine ⟨5703989580857259267313061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15210638882286024712834829 5703989580857259267313061)
                    ·
                      refine ⟨1069498046410736112621199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5703989580857259267313061 1069498046410736112621199)
                      ·
                        rfl

theorem cell23_2082840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2082840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082840 prefixEnd_2082840 := by exact prefixLift 2082840
  have htrace : WordTrace (prefixWord ++ tailWord_2082840) baseStart_2082840 baseEnd_2082840 := by
    simpa [prefixWord, tailWord_2082840, baseEnd_2082840] using wordTrace_append hprefix tailTrace_2082840
  have hstable : (prefixWord ++ tailWord_2082840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082840).length < 2 ^ (prefixWord ++ tailWord_2082840).sum := by decide
  have hdescent : baseEnd_2082840 < baseStart_2082840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082877 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2082877 : Nat := 118140960795 + 2082877 * 2 ^ 59
def prefixEnd_2082877 : Nat := 4983230072969 + 3 ^ 40 * 2082877 * 2
def baseEnd_2082877 : Nat := 1069517045194952467858529

theorem tailTrace_2082877 : CollatzResearch.WordTrace tailWord_2082877 prefixEnd_2082877 1069517045194952467858529 := by
  unfold tailWord_2082877
  simp only [CollatzResearch.WordTrace]
  refine ⟨75968765275099830915830885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50645843516733220610553923 75968765275099830915830885)
  ·
    refine ⟨14244143489081218296718291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75968765275099830915830885 14244143489081218296718291)
    ·
      refine ⟨21366215233621827445077437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14244143489081218296718291 21366215233621827445077437)
      ·
        refine ⟨8012330712608185291904039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21366215233621827445077437 8012330712608185291904039)
        ·
          refine ⟨12018496068912277937856059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012330712608185291904039 12018496068912277937856059)
          ·
            refine ⟨18027744103368416906784089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018496068912277937856059 18027744103368416906784089)
            ·
              refine ⟨13520808077526312680088067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18027744103368416906784089 13520808077526312680088067)
              ·
                refine ⟨20281212116289469020132101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13520808077526312680088067 20281212116289469020132101)
                ·
                  refine ⟨3802727271804275441274769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20281212116289469020132101 3802727271804275441274769)
                  ·
                    refine ⟨2852045453853206580956077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3802727271804275441274769 2852045453853206580956077)
                    ·
                      refine ⟨1069517045194952467858529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852045453853206580956077 1069517045194952467858529)
                      ·
                        rfl

theorem cell23_2082877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2082877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082877 prefixEnd_2082877 := by exact prefixLift 2082877
  have htrace : WordTrace (prefixWord ++ tailWord_2082877) baseStart_2082877 baseEnd_2082877 := by
    simpa [prefixWord, tailWord_2082877, baseEnd_2082877] using wordTrace_append hprefix tailTrace_2082877
  have hstable : (prefixWord ++ tailWord_2082877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082877).length < 2 ^ (prefixWord ++ tailWord_2082877).sum := by decide
  have hdescent : baseEnd_2082877 < baseStart_2082877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082880 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 8]
def baseStart_2082880 : Nat := 118140960795 + 2082880 * 2 ^ 59
def prefixEnd_2082880 : Nat := 4983230072969 + 3 ^ 40 * 2082880 * 2
def baseEnd_2082880 : Nat := 118835398404101772902335

theorem tailTrace_2082880 : CollatzResearch.WordTrace tailWord_2082880 prefixEnd_2082880 118835398404101772902335 := by
  unfold tailWord_2082880
  simp only [CollatzResearch.WordTrace]
  refine ⟨37984437347044481214095047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50645916462725974952126729 37984437347044481214095047)
  ·
    refine ⟨56976656020566721821142571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37984437347044481214095047 56976656020566721821142571)
    ·
      refine ⟨85464984030850082731713857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56976656020566721821142571 85464984030850082731713857)
      ·
        refine ⟨64098738023137562048785393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85464984030850082731713857 64098738023137562048785393)
        ·
          refine ⟨48074053517353171536589045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64098738023137562048785393 48074053517353171536589045)
          ·
            refine ⟨4506942517251859831555223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48074053517353171536589045 4506942517251859831555223)
            ·
              refine ⟨6760413775877789747332835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506942517251859831555223 6760413775877789747332835)
              ·
                refine ⟨10140620663816684620999253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760413775877789747332835 10140620663816684620999253)
                ·
                  refine ⟨118835398404101772902335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10140620663816684620999253 118835398404101772902335)
                  ·
                    rfl

theorem cell23_2082880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_2082880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082880 prefixEnd_2082880 := by exact prefixLift 2082880
  have htrace : WordTrace (prefixWord ++ tailWord_2082880) baseStart_2082880 baseEnd_2082880 := by
    simpa [prefixWord, tailWord_2082880, baseEnd_2082880] using wordTrace_append hprefix tailTrace_2082880
  have hstable : (prefixWord ++ tailWord_2082880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082880).length < 2 ^ (prefixWord ++ tailWord_2082880).sum := by decide
  have hdescent : baseEnd_2082880 < baseStart_2082880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082900 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2082900 : Nat := 118140960795 + 2082900 * 2 ^ 59
def prefixEnd_2082900 : Nat := 4983230072969 + 3 ^ 40 * 2082900 * 2
def baseEnd_2082900 : Nat := 1069528855250005877870923

theorem tailTrace_2082900 : CollatzResearch.WordTrace tailWord_2082900 prefixEnd_2082900 1069528855250005877870923 := by
  unfold tailWord_2082900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37984802077008252921959077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50646402769344337229278769 37984802077008252921959077)
  ·
    refine ⟨7122150389439047422867327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37984802077008252921959077 7122150389439047422867327)
    ·
      refine ⟨10683225584158571134300991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122150389439047422867327 10683225584158571134300991)
      ·
        refine ⟨16024838376237856701451487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683225584158571134300991 16024838376237856701451487)
        ·
          refine ⟨24037257564356785052177231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16024838376237856701451487 24037257564356785052177231)
          ·
            refine ⟨36055886346535177578265847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24037257564356785052177231 36055886346535177578265847)
            ·
              refine ⟨54083829519802766367398771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36055886346535177578265847 54083829519802766367398771)
              ·
                refine ⟨81125744279704149551098157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54083829519802766367398771 81125744279704149551098157)
                ·
                  refine ⟨30422154104889056081661809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81125744279704149551098157 30422154104889056081661809)
                  ·
                    refine ⟨22816615578666792061246357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30422154104889056081661809 22816615578666792061246357)
                    ·
                      refine ⟨1069528855250005877870923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22816615578666792061246357 1069528855250005877870923)
                      ·
                        rfl

theorem cell23_2082900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2082900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082900 prefixEnd_2082900 := by exact prefixLift 2082900
  have htrace : WordTrace (prefixWord ++ tailWord_2082900) baseStart_2082900 baseEnd_2082900 := by
    simpa [prefixWord, tailWord_2082900, baseEnd_2082900] using wordTrace_append hprefix tailTrace_2082900
  have hstable : (prefixWord ++ tailWord_2082900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082900).length < 2 ^ (prefixWord ++ tailWord_2082900).sum := by decide
  have hdescent : baseEnd_2082900 < baseStart_2082900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082927 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 1, 5]
def baseStart_2082927 : Nat := 118140960795 + 2082927 * 2 ^ 59
def prefixEnd_2082927 : Nat := 4983230072969 + 3 ^ 40 * 2082927 * 2
def baseEnd_2082927 : Nat := 356514239742559090744433

theorem tailTrace_2082927 : CollatzResearch.WordTrace tailWord_2082927 prefixEnd_2082927 356514239742559090744433 := by
  unfold tailWord_2082927
  simp only [CollatzResearch.WordTrace]
  refine ⟨75970588924918689455151035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50647059283279126303434023 75970588924918689455151035)
  ·
    refine ⟨113955883387378034182726553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75970588924918689455151035 113955883387378034182726553)
    ·
      refine ⟨85466912540533525637044915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113955883387378034182726553 85466912540533525637044915)
      ·
        refine ⟨128200368810800288455567373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85466912540533525637044915 128200368810800288455567373)
        ·
          refine ⟨48075138304050108170837765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128200368810800288455567373 48075138304050108170837765)
          ·
            refine ⟨9014088432009395282032081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48075138304050108170837765 9014088432009395282032081)
            ·
              refine ⟨6760566324007046461524061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014088432009395282032081 6760566324007046461524061)
              ·
                refine ⟨2535212371502642423071523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6760566324007046461524061 2535212371502642423071523)
                ·
                  refine ⟨3802818557253963634607285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535212371502642423071523 3802818557253963634607285)
                  ·
                    refine ⟨356514239742559090744433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3802818557253963634607285 356514239742559090744433)
                    ·
                      rfl

theorem cell23_2082927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_2082927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082927 prefixEnd_2082927 := by exact prefixLift 2082927
  have htrace : WordTrace (prefixWord ++ tailWord_2082927) baseStart_2082927 baseEnd_2082927 := by
    simpa [prefixWord, tailWord_2082927, baseEnd_2082927] using wordTrace_append hprefix tailTrace_2082927
  have hstable : (prefixWord ++ tailWord_2082927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082927).length < 2 ^ (prefixWord ++ tailWord_2082927).sum := by decide
  have hdescent : baseEnd_2082927 < baseStart_2082927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082941 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_2082941 : Nat := 118140960795 + 2082941 * 2 ^ 59
def prefixEnd_2082941 : Nat := 4983230072969 + 3 ^ 40 * 2082941 * 2
def baseEnd_2082941 : Nat := 1069549907956840217458235

theorem tailTrace_2082941 : CollatzResearch.WordTrace tailWord_2082941 prefixEnd_2082941 1069549907956840217458235 := by
  unfold tailWord_2082941
  simp only [CollatzResearch.WordTrace]
  refine ⟨75971099546867969846160677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50647399697911979897440451 75971099546867969846160677)
  ·
    refine ⟨14244581165037744346155127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75971099546867969846160677 14244581165037744346155127)
    ·
      refine ⟨21366871747556616519232691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14244581165037744346155127 21366871747556616519232691)
      ·
        refine ⟨32050307621334924778849037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21366871747556616519232691 32050307621334924778849037)
        ·
          refine ⟨12018865358000596792068389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32050307621334924778849037 12018865358000596792068389)
          ·
            refine ⟨2253537254625111898512823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12018865358000596792068389 2253537254625111898512823)
            ·
              refine ⟨3380305881937667847769235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253537254625111898512823 3380305881937667847769235)
              ·
                refine ⟨5070458822906501771653853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380305881937667847769235 5070458822906501771653853)
                ·
                  refine ⟨1901422058589938164370195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5070458822906501771653853 1901422058589938164370195)
                  ·
                    refine ⟨2852133087884907246555293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1901422058589938164370195 2852133087884907246555293)
                    ·
                      refine ⟨1069549907956840217458235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852133087884907246555293 1069549907956840217458235)
                      ·
                        rfl

theorem cell23_2082941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_2082941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082941 prefixEnd_2082941 := by exact prefixLift 2082941
  have htrace : WordTrace (prefixWord ++ tailWord_2082941) baseStart_2082941 baseEnd_2082941 := by
    simpa [prefixWord, tailWord_2082941, baseEnd_2082941] using wordTrace_append hprefix tailTrace_2082941
  have hstable : (prefixWord ++ tailWord_2082941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082941).length < 2 ^ (prefixWord ++ tailWord_2082941).sum := by decide
  have hdescent : baseEnd_2082941 < baseStart_2082941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082960 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_2082960 : Nat := 118140960795 + 2082960 * 2 ^ 59
def prefixEnd_2082960 : Nat := 4983230072969 + 3 ^ 40 * 2082960 * 2
def baseEnd_2082960 : Nat := 1069559664089275643120647

theorem tailTrace_2082960 : CollatzResearch.WordTrace tailWord_2082960 prefixEnd_2082960 1069559664089275643120647 := by
  unfold tailWord_2082960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37985896266899568045551167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50647861689199424060734889 37985896266899568045551167)
  ·
    refine ⟨56978844400349352068326751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37985896266899568045551167 56978844400349352068326751)
    ·
      refine ⟨85468266600524028102490127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56978844400349352068326751 85468266600524028102490127)
      ·
        refine ⟨128202399900786042153735191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85468266600524028102490127 128202399900786042153735191)
        ·
          refine ⟨192303599851179063230602787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128202399900786042153735191 192303599851179063230602787)
          ·
            refine ⟨288455399776768594845904181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192303599851179063230602787 288455399776768594845904181)
            ·
              refine ⟨27042693729072055766803517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288455399776768594845904181 27042693729072055766803517)
              ·
                refine ⟨10141010148402020912551319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27042693729072055766803517 10141010148402020912551319)
                ·
                  refine ⟨15211515222603031368826979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141010148402020912551319 15211515222603031368826979)
                  ·
                    refine ⟨22817272833904547053240469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15211515222603031368826979 22817272833904547053240469)
                    ·
                      refine ⟨1069559664089275643120647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22817272833904547053240469 1069559664089275643120647)
                      ·
                        rfl

theorem cell23_2082960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_2082960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082960 prefixEnd_2082960 := by exact prefixLift 2082960
  have htrace : WordTrace (prefixWord ++ tailWord_2082960) baseStart_2082960 baseEnd_2082960 := by
    simpa [prefixWord, tailWord_2082960, baseEnd_2082960] using wordTrace_append hprefix tailTrace_2082960
  have hstable : (prefixWord ++ tailWord_2082960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082960).length < 2 ^ (prefixWord ++ tailWord_2082960).sum := by decide
  have hdescent : baseEnd_2082960 < baseStart_2082960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082977 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2082977 : Nat := 118140960795 + 2082977 * 2 ^ 59
def prefixEnd_2082977 : Nat := 4983230072969 + 3 ^ 40 * 2082977 * 2
def baseEnd_2082977 : Nat := 1069568393260402076608069

theorem tailTrace_2082977 : CollatzResearch.WordTrace tailWord_2082977 prefixEnd_2082977 1069568393260402076608069 := by
  unfold tailWord_2082977
  simp only [CollatzResearch.WordTrace]
  refine ⟨75972412574737547994471185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50648275049825031996314123 75972412574737547994471185)
  ·
    refine ⟨56979309431053160995853389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75972412574737547994471185 56979309431053160995853389)
    ·
      refine ⟨21367241036644935373445021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56979309431053160995853389 21367241036644935373445021)
      ·
        refine ⟨8012715388741850765041883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21367241036644935373445021 8012715388741850765041883)
        ·
          refine ⟨12019073083112776147562825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012715388741850765041883 12019073083112776147562825)
          ·
            refine ⟨9014304812334582110672119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12019073083112776147562825 9014304812334582110672119)
            ·
              refine ⟨13521457218501873166008179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014304812334582110672119 13521457218501873166008179)
              ·
                refine ⟨20282185827752809749012269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13521457218501873166008179 20282185827752809749012269)
                ·
                  refine ⟨7605819685407303655879601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20282185827752809749012269 7605819685407303655879601)
                  ·
                    refine ⟨5704364764055477741909701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605819685407303655879601 5704364764055477741909701)
                    ·
                      refine ⟨1069568393260402076608069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5704364764055477741909701 1069568393260402076608069)
                      ·
                        rfl

theorem cell23_2082977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2082977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082977 prefixEnd_2082977 := by exact prefixLift 2082977
  have htrace : WordTrace (prefixWord ++ tailWord_2082977) baseStart_2082977 baseEnd_2082977 := by
    simpa [prefixWord, tailWord_2082977, baseEnd_2082977] using wordTrace_append hprefix tailTrace_2082977
  have hstable : (prefixWord ++ tailWord_2082977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082977).length < 2 ^ (prefixWord ++ tailWord_2082977).sum := by decide
  have hdescent : baseEnd_2082977 < baseStart_2082977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083000 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_2083000 : Nat := 118140960795 + 2083000 * 2 ^ 59
def prefixEnd_2083000 : Nat := 4983230072969 + 3 ^ 40 * 2083000 * 2
def baseEnd_2083000 : Nat := 356526734438485162206821

theorem tailTrace_2083000 : CollatzResearch.WordTrace tailWord_2083000 prefixEnd_2083000 356526734438485162206821 := by
  unfold tailWord_2083000
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986625726827111461279227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50648834302436148615038969 37986625726827111461279227)
  ·
    refine ⟨56979938590240667191918841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37986625726827111461279227 56979938590240667191918841)
    ·
      refine ⟨42734953942680500393939131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56979938590240667191918841 42734953942680500393939131)
      ·
        refine ⟨64102430914020750590908697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42734953942680500393939131 64102430914020750590908697)
        ·
          refine ⟨48076823185515562943181523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64102430914020750590908697 48076823185515562943181523)
          ·
            refine ⟨72115234778273344414772285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48076823185515562943181523 72115234778273344414772285)
            ·
              refine ⟨27043213041852504155539607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72115234778273344414772285 27043213041852504155539607)
              ·
                refine ⟨40564819562778756233309411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27043213041852504155539607 40564819562778756233309411)
                ·
                  refine ⟨60847229344168134349964117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40564819562778756233309411 60847229344168134349964117)
                  ·
                    refine ⟨356526734438485162206821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60847229344168134349964117 356526734438485162206821)
                    ·
                      rfl

theorem cell23_2083000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_2083000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083000 prefixEnd_2083000 := by exact prefixLift 2083000
  have htrace : WordTrace (prefixWord ++ tailWord_2083000) baseStart_2083000 baseEnd_2083000 := by
    simpa [prefixWord, tailWord_2083000, baseEnd_2083000] using wordTrace_append hprefix tailTrace_2083000
  have hstable : (prefixWord ++ tailWord_2083000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083000).length < 2 ^ (prefixWord ++ tailWord_2083000).sum := by decide
  have hdescent : baseEnd_2083000 < baseStart_2083000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083004 : List Nat := [2, 2, 2, 3, 3, 2, 1, 8]
def baseStart_2083004 : Nat := 118140960795 + 2083004 * 2 ^ 59
def prefixEnd_2083004 : Nat := 4983230072969 + 3 ^ 40 * 2083004 * 2
def baseEnd_2083004 : Nat := 39614157675484202628535

theorem tailTrace_2083004 : CollatzResearch.WordTrace tailWord_2083004 prefixEnd_2083004 39614157675484202628535 := by
  unfold tailWord_2083004
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986698672819865802852033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50648931563759821070469377 37986698672819865802852033)
  ·
    refine ⟨28490024004614899352139025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37986698672819865802852033 28490024004614899352139025)
    ·
      refine ⟨21367518003461174514104269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28490024004614899352139025 21367518003461174514104269)
      ·
        refine ⟨8012819251297940442789101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21367518003461174514104269 8012819251297940442789101)
        ·
          refine ⟨3004807219236727666045913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8012819251297940442789101 3004807219236727666045913)
          ·
            refine ⟨2253605414427545749534435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004807219236727666045913 2253605414427545749534435)
            ·
              refine ⟨3380408121641318624301653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253605414427545749534435 3380408121641318624301653)
              ·
                refine ⟨39614157675484202628535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3380408121641318624301653 39614157675484202628535)
                ·
                  rfl

theorem cell23_2083004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 8].length) (baseStart_2083004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083004 prefixEnd_2083004 := by exact prefixLift 2083004
  have htrace : WordTrace (prefixWord ++ tailWord_2083004) baseStart_2083004 baseEnd_2083004 := by
    simpa [prefixWord, tailWord_2083004, baseEnd_2083004] using wordTrace_append hprefix tailTrace_2083004
  have hstable : (prefixWord ++ tailWord_2083004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083004).length < 2 ^ (prefixWord ++ tailWord_2083004).sum := by decide
  have hdescent : baseEnd_2083004 < baseStart_2083004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083041 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_2083041 : Nat := 118140960795 + 2083041 * 2 ^ 59
def prefixEnd_2083041 : Nat := 4983230072969 + 3 ^ 40 * 2083041 * 2
def baseEnd_2083041 : Nat := 1069601256022289826207775

theorem tailTrace_2083041 : CollatzResearch.WordTrace tailWord_2083041 prefixEnd_2083041 1069601256022289826207775 := by
  unfold tailWord_2083041
  simp only [CollatzResearch.WordTrace]
  refine ⟨75974746846505686924800977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50649831231003791283200651 75974746846505686924800977)
  ·
    refine ⟨56981060134879265193600733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75974746846505686924800977 56981060134879265193600733)
    ·
      refine ⟨21367897550579724447600275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56981060134879265193600733 21367897550579724447600275)
      ·
        refine ⟨32051846325869586671400413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21367897550579724447600275 32051846325869586671400413)
        ·
          refine ⟨12019442372201095001775155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32051846325869586671400413 12019442372201095001775155)
          ·
            refine ⟨18029163558301642502662733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12019442372201095001775155 18029163558301642502662733)
            ·
              refine ⟨6760936334363115938498525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18029163558301642502662733 6760936334363115938498525)
              ·
                refine ⟨2535351125386168476936947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6760936334363115938498525 2535351125386168476936947)
                ·
                  refine ⟨3803026688079252715405421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535351125386168476936947 3803026688079252715405421)
                  ·
                    refine ⟨1426135008029719768277033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803026688079252715405421 1426135008029719768277033)
                    ·
                      refine ⟨1069601256022289826207775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426135008029719768277033 1069601256022289826207775)
                      ·
                        rfl

theorem cell23_2083041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_2083041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083041 prefixEnd_2083041 := by exact prefixLift 2083041
  have htrace : WordTrace (prefixWord ++ tailWord_2083041) baseStart_2083041 baseEnd_2083041 := by
    simpa [prefixWord, tailWord_2083041, baseEnd_2083041] using wordTrace_append hprefix tailTrace_2083041
  have hstable : (prefixWord ++ tailWord_2083041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083041).length < 2 ^ (prefixWord ++ tailWord_2083041).sum := by decide
  have hdescent : baseEnd_2083041 < baseStart_2083041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083042 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2083042 : Nat := 118140960795 + 2083042 * 2 ^ 59
def prefixEnd_2083042 : Nat := 4983230072969 + 3 ^ 40 * 2083042 * 2
def baseEnd_2083042 : Nat := 356533923167648107431757

theorem tailTrace_2083042 : CollatzResearch.WordTrace tailWord_2083042 prefixEnd_2083042 356533923167648107431757 := by
  unfold tailWord_2083042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18993695829875516023896845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50649855546334709397058253 18993695829875516023896845)
  ·
    refine ⟨7122635936203318508961317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18993695829875516023896845 7122635936203318508961317)
    ·
      refine ⟨1335494238038122220430247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7122635936203318508961317 1335494238038122220430247)
      ·
        refine ⟨2003241357057183330645371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335494238038122220430247 2003241357057183330645371)
        ·
          refine ⟨3004862035585774995968057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003241357057183330645371 3004862035585774995968057)
          ·
            refine ⟨2253646526689331246976043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004862035585774995968057 2253646526689331246976043)
            ·
              refine ⟨3380469790033996870464065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253646526689331246976043 3380469790033996870464065)
              ·
                refine ⟨2535352342525497652848049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380469790033996870464065 2535352342525497652848049)
                ·
                  refine ⟨1901514256894123239636037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535352342525497652848049 1901514256894123239636037)
                  ·
                    refine ⟨356533923167648107431757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901514256894123239636037 356533923167648107431757)
                    ·
                      rfl

theorem cell23_2083042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2083042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083042 prefixEnd_2083042 := by exact prefixLift 2083042
  have htrace : WordTrace (prefixWord ++ tailWord_2083042) baseStart_2083042 baseEnd_2083042 := by
    simpa [prefixWord, tailWord_2083042, baseEnd_2083042] using wordTrace_append hprefix tailTrace_2083042
  have hstable : (prefixWord ++ tailWord_2083042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083042).length < 2 ^ (prefixWord ++ tailWord_2083042).sum := by decide
  have hdescent : baseEnd_2083042 < baseStart_2083042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083048 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2083048 : Nat := 118140960795 + 2083048 * 2 ^ 59
def prefixEnd_2083048 : Nat := 4983230072969 + 3 ^ 40 * 2083048 * 2
def baseEnd_2083048 : Nat := 1069604850386871298820243

theorem tailTrace_2083048 : CollatzResearch.WordTrace tailWord_2083048 prefixEnd_2083048 1069604850386871298820243 := by
  unfold tailWord_2083048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37987501078740163560152899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50650001438320218080203865 37987501078740163560152899)
  ·
    refine ⟨56981251618110245340229349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37987501078740163560152899 56981251618110245340229349)
    ·
      refine ⟨10683984678395671001293003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56981251618110245340229349 10683984678395671001293003)
      ·
        refine ⟨16025977017593506501939505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683984678395671001293003 16025977017593506501939505)
        ·
          refine ⟨12019482763195129876454629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16025977017593506501939505 12019482763195129876454629)
          ·
            refine ⟨2253653018099086851835243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12019482763195129876454629 2253653018099086851835243)
            ·
              refine ⟨3380479527148630277752865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253653018099086851835243 3380479527148630277752865)
              ·
                refine ⟨2535359645361472708314649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380479527148630277752865 2535359645361472708314649)
                ·
                  refine ⟨1901519734021104531235987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535359645361472708314649 1901519734021104531235987)
                  ·
                    refine ⟨2852279601031656796853981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1901519734021104531235987 2852279601031656796853981)
                    ·
                      refine ⟨1069604850386871298820243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852279601031656796853981 1069604850386871298820243)
                      ·
                        rfl

theorem cell23_2083048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2083048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083048 prefixEnd_2083048 := by exact prefixLift 2083048
  have htrace : WordTrace (prefixWord ++ tailWord_2083048) baseStart_2083048 baseEnd_2083048 := by
    simpa [prefixWord, tailWord_2083048, baseEnd_2083048] using wordTrace_append hprefix tailTrace_2083048
  have hstable : (prefixWord ++ tailWord_2083048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083048).length < 2 ^ (prefixWord ++ tailWord_2083048).sum := by decide
  have hdescent : baseEnd_2083048 < baseStart_2083048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083057 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_2083057 : Nat := 118140960795 + 2083057 * 2 ^ 59
def prefixEnd_2083057 : Nat := 4983230072969 + 3 ^ 40 * 2083057 * 2
def baseEnd_2083057 : Nat := 1069609471712761763607701

theorem tailTrace_2083057 : CollatzResearch.WordTrace tailWord_2083057 prefixEnd_2083057 1069609471712761763607701 := by
  unfold tailWord_2083057
  simp only [CollatzResearch.WordTrace]
  refine ⟨75975330414447721657383425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50650220276298481104922283 75975330414447721657383425)
  ·
    refine ⟨56981497810835791243037569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75975330414447721657383425 56981497810835791243037569)
    ·
      refine ⟨42736123358126843432278177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56981497810835791243037569 42736123358126843432278177)
      ·
        refine ⟨32052092518595132574208633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42736123358126843432278177 32052092518595132574208633)
        ·
          refine ⟨24039069388946349430656475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32052092518595132574208633 24039069388946349430656475)
          ·
            refine ⟨36058604083419524145984713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24039069388946349430656475 36058604083419524145984713)
            ·
              refine ⟨27043953062564643109488535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36058604083419524145984713 27043953062564643109488535)
              ·
                refine ⟨40565929593846964664232803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27043953062564643109488535 40565929593846964664232803)
                ·
                  refine ⟨60848894390770446996349205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40565929593846964664232803 60848894390770446996349205)
                  ·
                    refine ⟨2852291924567364702953869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60848894390770446996349205 2852291924567364702953869)
                    ·
                      refine ⟨1069609471712761763607701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852291924567364702953869 1069609471712761763607701)
                      ·
                        rfl

theorem cell23_2083057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_2083057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083057 prefixEnd_2083057 := by exact prefixLift 2083057
  have htrace : WordTrace (prefixWord ++ tailWord_2083057) baseStart_2083057 baseEnd_2083057 := by
    simpa [prefixWord, tailWord_2083057, baseEnd_2083057] using wordTrace_append hprefix tailTrace_2083057
  have hstable : (prefixWord ++ tailWord_2083057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083057).length < 2 ^ (prefixWord ++ tailWord_2083057).sum := by decide
  have hdescent : baseEnd_2083057 < baseStart_2083057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083087 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_2083087 : Nat := 118140960795 + 2083087 * 2 ^ 59
def prefixEnd_2083087 : Nat := 4983230072969 + 3 ^ 40 * 2083087 * 2
def baseEnd_2083087 : Nat := 1069624876132396646232563

theorem tailTrace_2083087 : CollatzResearch.WordTrace tailWord_2083087 prefixEnd_2083087 1069624876132396646232563 := by
  unfold tailWord_2083087
  simp only [CollatzResearch.WordTrace]
  refine ⟨75976424604339036780975515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50650949736226024520650343 75976424604339036780975515)
  ·
    refine ⟨113964636906508555171463273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75976424604339036780975515 113964636906508555171463273)
    ·
      refine ⟨85473477679881416378597455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113964636906508555171463273 85473477679881416378597455)
      ·
        refine ⟨128210216519822124567896183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85473477679881416378597455 128210216519822124567896183)
        ·
          refine ⟨192315324779733186851844275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128210216519822124567896183 192315324779733186851844275)
          ·
            refine ⟨288472987169599780277766413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192315324779733186851844275 288472987169599780277766413)
            ·
              refine ⟨108177370188599917604162405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288472987169599780277766413 108177370188599917604162405)
              ·
                refine ⟨20283256910362484550780451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108177370188599917604162405 20283256910362484550780451)
                ·
                  refine ⟨30424885365543726826170677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20283256910362484550780451 30424885365543726826170677)
                  ·
                    refine ⟨2852333003019724389953501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30424885365543726826170677 2852333003019724389953501)
                    ·
                      refine ⟨1069624876132396646232563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852333003019724389953501 1069624876132396646232563)
                      ·
                        rfl

theorem cell23_2083087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_2083087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083087 prefixEnd_2083087 := by exact prefixLift 2083087
  have htrace : WordTrace (prefixWord ++ tailWord_2083087) baseStart_2083087 baseEnd_2083087 := by
    simpa [prefixWord, tailWord_2083087, baseEnd_2083087] using wordTrace_append hprefix tailTrace_2083087
  have hstable : (prefixWord ++ tailWord_2083087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083087).length < 2 ^ (prefixWord ++ tailWord_2083087).sum := by decide
  have hdescent : baseEnd_2083087 < baseStart_2083087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083122 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_2083122 : Nat := 118140960795 + 2083122 * 2 ^ 59
def prefixEnd_2083122 : Nat := 4983230072969 + 3 ^ 40 * 2083122 * 2
def baseEnd_2083122 : Nat := 1069642847955304009294903

theorem tailTrace_2083122 : CollatzResearch.WordTrace tailWord_2083122 prefixEnd_2083122 1069642847955304009294903 := by
  unfold tailWord_2083122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18994425289803059439624905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50651800772808158505666413 18994425289803059439624905)
  ·
    refine ⟨14245818967352294579718679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18994425289803059439624905 14245818967352294579718679)
    ·
      refine ⟨21368728451028441869578019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14245818967352294579718679 21368728451028441869578019)
      ·
        refine ⟨32053092676542662804367029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21368728451028441869578019 32053092676542662804367029)
        ·
          refine ⟨3004977438425874637909409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32053092676542662804367029 3004977438425874637909409)
          ·
            refine ⟨2253733078819405978432057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004977438425874637909409 2253733078819405978432057)
            ·
              refine ⟨1690299809114554483824043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253733078819405978432057 1690299809114554483824043)
              ·
                refine ⟨2535449713671831725736065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690299809114554483824043 2535449713671831725736065)
                ·
                  refine ⟨1901587285253873794302049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535449713671831725736065 1901587285253873794302049)
                  ·
                    refine ⟨1426190463940405345726537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1901587285253873794302049 1426190463940405345726537)
                    ·
                      refine ⟨1069642847955304009294903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426190463940405345726537 1069642847955304009294903)
                      ·
                        rfl

theorem cell23_2083122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_2083122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083122 prefixEnd_2083122 := by exact prefixLift 2083122
  have htrace : WordTrace (prefixWord ++ tailWord_2083122) baseStart_2083122 baseEnd_2083122 := by
    simpa [prefixWord, tailWord_2083122, baseEnd_2083122] using wordTrace_append hprefix tailTrace_2083122
  have hstable : (prefixWord ++ tailWord_2083122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083122).length < 2 ^ (prefixWord ++ tailWord_2083122).sum := by decide
  have hdescent : baseEnd_2083122 < baseStart_2083122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083127 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_2083127 : Nat := 118140960795 + 2083127 * 2 ^ 59
def prefixEnd_2083127 : Nat := 4983230072969 + 3 ^ 40 * 2083127 * 2
def baseEnd_2083127 : Nat := 1069645415358576489732379

theorem tailTrace_2083127 : CollatzResearch.WordTrace tailWord_2083127 prefixEnd_2083127 1069645415358576489732379 := by
  unfold tailWord_2083127
  simp only [CollatzResearch.WordTrace]
  refine ⟨75977883524194123612431635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50651922349462749074954423 75977883524194123612431635)
  ·
    refine ⟨113966825286291185418647453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75977883524194123612431635 113966825286291185418647453)
    ·
      refine ⟨42737559482359194531992795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113966825286291185418647453 42737559482359194531992795)
      ·
        refine ⟨64106339223538791797989193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42737559482359194531992795 64106339223538791797989193)
        ·
          refine ⟨48079754417654093848491895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64106339223538791797989193 48079754417654093848491895)
          ·
            refine ⟨72119631626481140772737843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48079754417654093848491895 72119631626481140772737843)
            ·
              refine ⟨108179447439721711159106765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72119631626481140772737843 108179447439721711159106765)
              ·
                refine ⟨40567292789895641684665037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108179447439721711159106765 40567292789895641684665037)
                ·
                  refine ⟨15212734796210865631749389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40567292789895641684665037 15212734796210865631749389)
                  ·
                    refine ⟨5704775548579074611906021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15212734796210865631749389 5704775548579074611906021)
                    ·
                      refine ⟨1069645415358576489732379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5704775548579074611906021 1069645415358576489732379)
                      ·
                        rfl

theorem cell23_2083127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_2083127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083127 prefixEnd_2083127 := by exact prefixLift 2083127
  have htrace : WordTrace (prefixWord ++ tailWord_2083127) baseStart_2083127 baseEnd_2083127 := by
    simpa [prefixWord, tailWord_2083127, baseEnd_2083127] using wordTrace_append hprefix tailTrace_2083127
  have hstable : (prefixWord ++ tailWord_2083127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083127).length < 2 ^ (prefixWord ++ tailWord_2083127).sum := by decide
  have hdescent : baseEnd_2083127 < baseStart_2083127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083144 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_2083144 : Nat := 118140960795 + 2083144 * 2 ^ 59
def prefixEnd_2083144 : Nat := 4983230072969 + 3 ^ 40 * 2083144 * 2
def baseEnd_2083144 : Nat := 1069654144529702923219801

theorem tailTrace_2083144 : CollatzResearch.WordTrace tailWord_2083144 prefixEnd_2083144 1069654144529702923219801 := by
  unfold tailWord_2083144
  simp only [CollatzResearch.WordTrace]
  refine ⟨37989251782566267757900243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50652335710088357010533657 37989251782566267757900243)
  ·
    refine ⟨56983877673849401636850365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37989251782566267757900243 56983877673849401636850365)
    ·
      refine ⟨21368954127693525613818887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56983877673849401636850365 21368954127693525613818887)
      ·
        refine ⟨32053431191540288420728331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21368954127693525613818887 32053431191540288420728331)
        ·
          refine ⟨48080146787310432631092497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32053431191540288420728331 48080146787310432631092497)
          ·
            refine ⟨36060110090482824473319373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48080146787310432631092497 36060110090482824473319373)
            ·
              refine ⟨13522541283931059177494765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36060110090482824473319373 13522541283931059177494765)
              ·
                refine ⟨5070952981474147191560537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13522541283931059177494765 5070952981474147191560537)
                ·
                  refine ⟨3803214736105610393670403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070952981474147191560537 3803214736105610393670403)
                  ·
                    refine ⟨5704822104158415590505605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3803214736105610393670403 5704822104158415590505605)
                    ·
                      refine ⟨1069654144529702923219801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5704822104158415590505605 1069654144529702923219801)
                      ·
                        rfl

theorem cell23_2083144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_2083144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083144 prefixEnd_2083144 := by exact prefixLift 2083144
  have htrace : WordTrace (prefixWord ++ tailWord_2083144) baseStart_2083144 baseEnd_2083144 := by
    simpa [prefixWord, tailWord_2083144, baseEnd_2083144] using wordTrace_append hprefix tailTrace_2083144
  have hstable : (prefixWord ++ tailWord_2083144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083144).length < 2 ^ (prefixWord ++ tailWord_2083144).sum := by decide
  have hdescent : baseEnd_2083144 < baseStart_2083144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083167 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 8]
def baseStart_2083167 : Nat := 118140960795 + 2083167 * 2 ^ 59
def prefixEnd_2083167 : Nat := 4983230072969 + 3 ^ 40 * 2083167 * 2
def baseEnd_2083167 : Nat := 118851772731639592581355

theorem tailTrace_2083167 : CollatzResearch.WordTrace tailWord_2083167 prefixEnd_2083167 118851772731639592581355 := by
  unfold tailWord_2083167
  simp only [CollatzResearch.WordTrace]
  refine ⟨75979342444049210443887755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50652894962699473629258503 75979342444049210443887755)
  ·
    refine ⟨113969013666073815665831633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75979342444049210443887755 113969013666073815665831633)
    ·
      refine ⟨85476760249555361749373725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113969013666073815665831633 85476760249555361749373725)
      ·
        refine ⟨32053785093583260656015147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85476760249555361749373725 32053785093583260656015147)
        ·
          refine ⟨48080677640374890984022721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32053785093583260656015147 48080677640374890984022721)
          ·
            refine ⟨36060508230281168238017041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48080677640374890984022721 36060508230281168238017041)
            ·
              refine ⟨27045381172710876178512781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36060508230281168238017041 27045381172710876178512781)
              ·
                refine ⟨10142017939766578566942293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27045381172710876178512781 10142017939766578566942293)
                ·
                  refine ⟨118851772731639592581355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10142017939766578566942293 118851772731639592581355)
                  ·
                    rfl

theorem cell23_2083167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 8].length) (baseStart_2083167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083167 prefixEnd_2083167 := by exact prefixLift 2083167
  have htrace : WordTrace (prefixWord ++ tailWord_2083167) baseStart_2083167 baseEnd_2083167 := by
    simpa [prefixWord, tailWord_2083167, baseEnd_2083167] using wordTrace_append hprefix tailTrace_2083167
  have hstable : (prefixWord ++ tailWord_2083167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083167).length < 2 ^ (prefixWord ++ tailWord_2083167).sum := by decide
  have hdescent : baseEnd_2083167 < baseStart_2083167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083178 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2083178 : Nat := 118140960795 + 2083178 * 2 ^ 59
def prefixEnd_2083178 : Nat := 4983230072969 + 3 ^ 40 * 2083178 * 2
def baseEnd_2083178 : Nat := 1069671602871955790194645

theorem tailTrace_2083178 : CollatzResearch.WordTrace tailWord_2083178 prefixEnd_2083178 1069671602871955790194645 := by
  unfold tailWord_2083178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18994935911752339830634547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50653162431339572881692125 18994935911752339830634547)
  ·
    refine ⟨28492403867628509745951821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18994935911752339830634547 28492403867628509745951821)
    ·
      refine ⟨10684651450360691154731933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28492403867628509745951821 10684651450360691154731933)
      ·
        refine ⟨4006744293885259183024475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10684651450360691154731933 4006744293885259183024475)
        ·
          refine ⟨6010116440827888774536713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006744293885259183024475 6010116440827888774536713)
          ·
            refine ⟨4507587330620916580902535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010116440827888774536713 4507587330620916580902535)
            ·
              refine ⟨6761380995931374871353803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507587330620916580902535 6761380995931374871353803)
              ·
                refine ⟨10142071493897062307030705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761380995931374871353803 10142071493897062307030705)
                ·
                  refine ⟨7606553620422796730273029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142071493897062307030705 7606553620422796730273029)
                  ·
                    refine ⟨1426228803829274386926193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606553620422796730273029 1426228803829274386926193)
                    ·
                      refine ⟨1069671602871955790194645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426228803829274386926193 1069671602871955790194645)
                      ·
                        rfl

theorem cell23_2083178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2083178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083178 prefixEnd_2083178 := by exact prefixLift 2083178
  have htrace : WordTrace (prefixWord ++ tailWord_2083178) baseStart_2083178 baseEnd_2083178 := by
    simpa [prefixWord, tailWord_2083178, baseEnd_2083178] using wordTrace_append hprefix tailTrace_2083178
  have hstable : (prefixWord ++ tailWord_2083178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083178).length < 2 ^ (prefixWord ++ tailWord_2083178).sum := by decide
  have hdescent : baseEnd_2083178 < baseStart_2083178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083184 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 6]
def baseStart_2083184 : Nat := 118140960795 + 2083184 * 2 ^ 59
def prefixEnd_2083184 : Nat := 4983230072969 + 3 ^ 40 * 2083184 * 2
def baseEnd_2083184 : Nat := 118852742639542529635513

theorem tailTrace_2083184 : CollatzResearch.WordTrace tailWord_2083184 prefixEnd_2083184 118852742639542529635513 := by
  unfold tailWord_2083184
  simp only [CollatzResearch.WordTrace]
  refine ⟨37989981242493811173628303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50653308323325081564837737 37989981242493811173628303)
  ·
    refine ⟨56984971863740716760442455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37989981242493811173628303 56984971863740716760442455)
    ·
      refine ⟨85477457795611075140663683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56984971863740716760442455 85477457795611075140663683)
      ·
        refine ⟨128216186693416612710995525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85477457795611075140663683 128216186693416612710995525)
        ·
          refine ⟨24040535005015614883311661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128216186693416612710995525 24040535005015614883311661)
          ·
            refine ⟨9015200626880855581241873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24040535005015614883311661 9015200626880855581241873)
            ·
              refine ⟨6761400470160641685931405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9015200626880855581241873 6761400470160641685931405)
              ·
                refine ⟨2535525176310240632224277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6761400470160641685931405 2535525176310240632224277)
                ·
                  refine ⟨118852742639542529635513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2535525176310240632224277 118852742639542529635513)
                  ·
                    rfl

theorem cell23_2083184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_2083184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083184 prefixEnd_2083184 := by exact prefixLift 2083184
  have htrace : WordTrace (prefixWord ++ tailWord_2083184) baseStart_2083184 baseEnd_2083184 := by
    simpa [prefixWord, tailWord_2083184, baseEnd_2083184] using wordTrace_append hprefix tailTrace_2083184
  have hstable : (prefixWord ++ tailWord_2083184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083184).length < 2 ^ (prefixWord ++ tailWord_2083184).sum := by decide
  have hdescent : baseEnd_2083184 < baseStart_2083184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083187 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_2083187 : Nat := 118140960795 + 2083187 * 2 ^ 59
def prefixEnd_2083187 : Nat := 4983230072969 + 3 ^ 40 * 2083187 * 2
def baseEnd_2083187 : Nat := 1069676224197846254982103

theorem tailTrace_2083187 : CollatzResearch.WordTrace tailWord_2083187 prefixEnd_2083187 1069676224197846254982103 := by
  unfold tailWord_2083187
  simp only [CollatzResearch.WordTrace]
  refine ⟨75980071903976753859615815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50653381269317835906410543 75980071903976753859615815)
  ·
    refine ⟨113970107855965130789423723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75980071903976753859615815 113970107855965130789423723)
    ·
      refine ⟨170955161783947696184135585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113970107855965130789423723 170955161783947696184135585)
      ·
        refine ⟨128216371337960772138101689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170955161783947696184135585 128216371337960772138101689)
        ·
          refine ⟨96162278503470579103576267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128216371337960772138101689 96162278503470579103576267)
          ·
            refine ⟨144243417755205868655364401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96162278503470579103576267 144243417755205868655364401)
            ·
              refine ⟨108182563316404401491523301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144243417755205868655364401 108182563316404401491523301)
              ·
                refine ⟨20284230621825825279660619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108182563316404401491523301 20284230621825825279660619)
                ·
                  refine ⟨30426345932738737919490929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20284230621825825279660619 30426345932738737919490929)
                  ·
                    refine ⟨22819759449554053439618197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30426345932738737919490929 22819759449554053439618197)
                    ·
                      refine ⟨1069676224197846254982103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22819759449554053439618197 1069676224197846254982103)
                      ·
                        rfl

theorem cell23_2083187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_2083187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083187 prefixEnd_2083187 := by exact prefixLift 2083187
  have htrace : WordTrace (prefixWord ++ tailWord_2083187) baseStart_2083187 baseEnd_2083187 := by
    simpa [prefixWord, tailWord_2083187, baseEnd_2083187] using wordTrace_append hprefix tailTrace_2083187
  have hstable : (prefixWord ++ tailWord_2083187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083187).length < 2 ^ (prefixWord ++ tailWord_2083187).sum := by decide
  have hdescent : baseEnd_2083187 < baseStart_2083187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083221 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_2083221 : Nat := 118140960795 + 2083221 * 2 ^ 59
def prefixEnd_2083221 : Nat := 4983230072969 + 3 ^ 40 * 2083221 * 2
def baseEnd_2083221 : Nat := 1069693682540099121956947

theorem tailTrace_2083221 : CollatzResearch.WordTrace tailWord_2083221 prefixEnd_2083221 1069693682540099121956947 := by
  unfold tailWord_2083221
  simp only [CollatzResearch.WordTrace]
  refine ⟨75981311985853577666353517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50654207990569051777569011 75981311985853577666353517)
  ·
    refine ⟨28492991994695091624882569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75981311985853577666353517 28492991994695091624882569)
    ·
      refine ⟨21369743996021318718661927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28492991994695091624882569 21369743996021318718661927)
      ·
        refine ⟨32054615994031978077992891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21369743996021318718661927 32054615994031978077992891)
        ·
          refine ⟨48081923991047967116989337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32054615994031978077992891 48081923991047967116989337)
          ·
            refine ⟨36061442993285975337742003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48081923991047967116989337 36061442993285975337742003)
            ·
              refine ⟨54092164489928963006613005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36061442993285975337742003 54092164489928963006613005)
              ·
                refine ⟨20284561683723361127479877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54092164489928963006613005 20284561683723361127479877)
                ·
                  refine ⟨3803355315698130211402477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20284561683723361127479877 3803355315698130211402477)
                  ·
                    refine ⟨1426258243386798829275929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803355315698130211402477 1426258243386798829275929)
                    ·
                      refine ⟨1069693682540099121956947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426258243386798829275929 1069693682540099121956947)
                      ·
                        rfl

theorem cell23_2083221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_2083221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083221 prefixEnd_2083221 := by exact prefixLift 2083221
  have htrace : WordTrace (prefixWord ++ tailWord_2083221) baseStart_2083221 baseEnd_2083221 := by
    simpa [prefixWord, tailWord_2083221, baseEnd_2083221] using wordTrace_append hprefix tailTrace_2083221
  have hstable : (prefixWord ++ tailWord_2083221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083221).length < 2 ^ (prefixWord ++ tailWord_2083221).sum := by decide
  have hdescent : baseEnd_2083221 < baseStart_2083221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083261 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_2083261 : Nat := 118140960795 + 2083261 * 2 ^ 59
def prefixEnd_2083261 : Nat := 4983230072969 + 3 ^ 40 * 2083261 * 2
def baseEnd_2083261 : Nat := 356571407255426321818921

theorem tailTrace_2083261 : CollatzResearch.WordTrace tailWord_2083261 prefixEnd_2083261 356571407255426321818921 := by
  unfold tailWord_2083261
  simp only [CollatzResearch.WordTrace]
  refine ⟨75982770905708664497809637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50655180603805776331873091 75982770905708664497809637)
  ·
    refine ⟨14246769544820374593339307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75982770905708664497809637 14246769544820374593339307)
    ·
      refine ⟨21370154317230561890008961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14246769544820374593339307 21370154317230561890008961)
      ·
        refine ⟨16027615737922921417506721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21370154317230561890008961 16027615737922921417506721)
        ·
          refine ⟨12020711803442191063130041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16027615737922921417506721 12020711803442191063130041)
          ·
            refine ⟨9015533852581643297347531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12020711803442191063130041 9015533852581643297347531)
            ·
              refine ⟨13523300778872464946021297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015533852581643297347531 13523300778872464946021297)
              ·
                refine ⟨10142475584154348709515973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523300778872464946021297 10142475584154348709515973)
                ·
                  refine ⟨1901714172028940383034245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10142475584154348709515973 1901714172028940383034245)
                  ·
                    refine ⟨356571407255426321818921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901714172028940383034245 356571407255426321818921)
                    ·
                      rfl

theorem cell23_2083261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_2083261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083261 prefixEnd_2083261 := by exact prefixLift 2083261
  have htrace : WordTrace (prefixWord ++ tailWord_2083261) baseStart_2083261 baseEnd_2083261 := by
    simpa [prefixWord, tailWord_2083261, baseEnd_2083261] using wordTrace_append hprefix tailTrace_2083261
  have hstable : (prefixWord ++ tailWord_2083261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083261).length < 2 ^ (prefixWord ++ tailWord_2083261).sum := by decide
  have hdescent : baseEnd_2083261 < baseStart_2083261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083264 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_2083264 : Nat := 118140960795 + 2083264 * 2 ^ 59
def prefixEnd_2083264 : Nat := 4983230072969 + 3 ^ 40 * 2083264 * 2
def baseEnd_2083264 : Nat := 1069715762208242453719249

theorem tailTrace_2083264 : CollatzResearch.WordTrace tailWord_2083264 prefixEnd_2083264 1069715762208242453719249 := by
  unfold tailWord_2083264
  simp only [CollatzResearch.WordTrace]
  refine ⟨37991440162348898005084423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50655253549798530673445897 37991440162348898005084423)
  ·
    refine ⟨56987160243523347007626635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37991440162348898005084423 56987160243523347007626635)
    ·
      refine ⟨85480740365285020511439953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56987160243523347007626635 85480740365285020511439953)
      ·
        refine ⟨64110555273963765383579965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85480740365285020511439953 64110555273963765383579965)
        ·
          refine ⟨24041458227736412018842487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64110555273963765383579965 24041458227736412018842487)
          ·
            refine ⟨36062187341604618028263731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24041458227736412018842487 36062187341604618028263731)
            ·
              refine ⟨54093281012406927042395597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36062187341604618028263731 54093281012406927042395597)
              ·
                refine ⟨20284980379652597640898349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54093281012406927042395597 20284980379652597640898349)
                ·
                  refine ⟨7606867642369724115336881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20284980379652597640898349 7606867642369724115336881)
                  ·
                    refine ⟨5705150731777293086502661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606867642369724115336881 5705150731777293086502661)
                    ·
                      refine ⟨1069715762208242453719249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5705150731777293086502661 1069715762208242453719249)
                      ·
                        rfl

theorem cell23_2083264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_2083264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083264 prefixEnd_2083264 := by exact prefixLift 2083264
  have htrace : WordTrace (prefixWord ++ tailWord_2083264) baseStart_2083264 baseEnd_2083264 := by
    simpa [prefixWord, tailWord_2083264, baseEnd_2083264] using wordTrace_append hprefix tailTrace_2083264
  have hstable : (prefixWord ++ tailWord_2083264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083264).length < 2 ^ (prefixWord ++ tailWord_2083264).sum := by decide
  have hdescent : baseEnd_2083264 < baseStart_2083264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083271 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_2083271 : Nat := 118140960795 + 2083271 * 2 ^ 59
def prefixEnd_2083271 : Nat := 4983230072969 + 3 ^ 40 * 2083271 * 2
def baseEnd_2083271 : Nat := 1069719356572823926331717

theorem tailTrace_2083271 : CollatzResearch.WordTrace tailWord_2083271 prefixEnd_2083271 1069719356572823926331717 := by
  unfold tailWord_2083271
  simp only [CollatzResearch.WordTrace]
  refine ⟨75983135635672436205673667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50655423757114957470449111 75983135635672436205673667)
  ·
    refine ⟨113974703453508654308510501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75983135635672436205673667 113974703453508654308510501)
    ·
      refine ⟨21370256897532872682845719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113974703453508654308510501 21370256897532872682845719)
      ·
        refine ⟨32055385346299309024268579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21370256897532872682845719 32055385346299309024268579)
        ·
          refine ⟨48083078019448963536402869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32055385346299309024268579 48083078019448963536402869)
          ·
            refine ⟨4507788564323340331537769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48083078019448963536402869 4507788564323340331537769)
            ·
              refine ⟨3380841423242505248653327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507788564323340331537769 3380841423242505248653327)
              ·
                refine ⟨5071262134863757872979991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380841423242505248653327 5071262134863757872979991)
                ·
                  refine ⟨7606893202295636809469987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071262134863757872979991 7606893202295636809469987)
                  ·
                    refine ⟨11410339803443455214204981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7606893202295636809469987 11410339803443455214204981)
                    ·
                      refine ⟨1069719356572823926331717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11410339803443455214204981 1069719356572823926331717)
                      ·
                        rfl

theorem cell23_2083271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_2083271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083271 prefixEnd_2083271 := by exact prefixLift 2083271
  have htrace : WordTrace (prefixWord ++ tailWord_2083271) baseStart_2083271 baseEnd_2083271 := by
    simpa [prefixWord, tailWord_2083271, baseEnd_2083271] using wordTrace_append hprefix tailTrace_2083271
  have hstable : (prefixWord ++ tailWord_2083271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083271).length < 2 ^ (prefixWord ++ tailWord_2083271).sum := by decide
  have hdescent : baseEnd_2083271 < baseStart_2083271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083285 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2083285 : Nat := 118140960795 + 2083285 * 2 ^ 59
def prefixEnd_2083285 : Nat := 4983230072969 + 3 ^ 40 * 2083285 * 2
def baseEnd_2083285 : Nat := 1069726545301986871556653

theorem tailTrace_2083285 : CollatzResearch.WordTrace tailWord_2083285 prefixEnd_2083285 1069726545301986871556653 := by
  unfold tailWord_2083285
  simp only [CollatzResearch.WordTrace]
  refine ⟨75983646257621716596683309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50655764171747811064455539 75983646257621716596683309)
  ·
    refine ⟨28493867346608143723756241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75983646257621716596683309 28493867346608143723756241)
    ·
      refine ⟨21370400509956107792817181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28493867346608143723756241 21370400509956107792817181)
      ·
        refine ⟨8013900191233540422306443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21370400509956107792817181 8013900191233540422306443)
        ·
          refine ⟨12020850286850310633459665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8013900191233540422306443 12020850286850310633459665)
          ·
            refine ⟨9015637715137732975094749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12020850286850310633459665 9015637715137732975094749)
            ·
              refine ⟨3380864143176649865660531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9015637715137732975094749 3380864143176649865660531)
              ·
                refine ⟨5071296214764974798490797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380864143176649865660531 5071296214764974798490797)
                ·
                  refine ⟨1901736080536865549434049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5071296214764974798490797 1901736080536865549434049)
                  ·
                    refine ⟨1426302060402649162075537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1901736080536865549434049 1426302060402649162075537)
                    ·
                      refine ⟨1069726545301986871556653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426302060402649162075537 1069726545301986871556653)
                      ·
                        rfl

theorem cell23_2083285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2083285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083285 prefixEnd_2083285 := by exact prefixLift 2083285
  have htrace : WordTrace (prefixWord ++ tailWord_2083285) baseStart_2083285 baseEnd_2083285 := by
    simpa [prefixWord, tailWord_2083285, baseEnd_2083285] using wordTrace_append hprefix tailTrace_2083285
  have hstable : (prefixWord ++ tailWord_2083285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083285).length < 2 ^ (prefixWord ++ tailWord_2083285).sum := by decide
  have hdescent : baseEnd_2083285 < baseStart_2083285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083295 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 2, 4]
def baseStart_2083295 : Nat := 118140960795 + 2083295 * 2 ^ 59
def prefixEnd_2083295 : Nat := 4983230072969 + 3 ^ 40 * 2083295 * 2
def baseEnd_2083295 : Nat := 356577226702843944143869

theorem tailTrace_2083295 : CollatzResearch.WordTrace tailWord_2083295 prefixEnd_2083295 356577226702843944143869 := by
  unfold tailWord_2083295
  simp only [CollatzResearch.WordTrace]
  refine ⟨75984010987585488304547339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50656007325056992203031559 75984010987585488304547339)
  ·
    refine ⟨113976016481378232456821009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75984010987585488304547339 113976016481378232456821009)
    ·
      refine ⟨85482012361033674342615757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113976016481378232456821009 85482012361033674342615757)
      ·
        refine ⟨32055754635387627878480909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85482012361033674342615757 32055754635387627878480909)
        ·
          refine ⟨12020907988270360454430341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32055754635387627878480909 12020907988270360454430341)
          ·
            refine ⟨2253920247800692585205689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12020907988270360454430341 2253920247800692585205689)
            ·
              refine ⟨1690440185850519438904267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253920247800692585205689 1690440185850519438904267)
              ·
                refine ⟨2535660278775779158356401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690440185850519438904267 2535660278775779158356401)
                ·
                  refine ⟨1901745209081834368767301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535660278775779158356401 1901745209081834368767301)
                  ·
                    refine ⟨356577226702843944143869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901745209081834368767301 356577226702843944143869)
                    ·
                      rfl

theorem cell23_2083295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 4].length) (baseStart_2083295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083295 prefixEnd_2083295 := by exact prefixLift 2083295
  have htrace : WordTrace (prefixWord ++ tailWord_2083295) baseStart_2083295 baseEnd_2083295 := by
    simpa [prefixWord, tailWord_2083295, baseEnd_2083295] using wordTrace_append hprefix tailTrace_2083295
  have hstable : (prefixWord ++ tailWord_2083295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083295).length < 2 ^ (prefixWord ++ tailWord_2083295).sum := by decide
  have hdescent : baseEnd_2083295 < baseStart_2083295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083318 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_2083318 : Nat := 118140960795 + 2083318 * 2 ^ 59
def prefixEnd_2083318 : Nat := 4983230072969 + 3 ^ 40 * 2083318 * 2
def baseEnd_2083318 : Nat := 1069743490163585242444001

theorem tailTrace_2083318 : CollatzResearch.WordTrace tailWord_2083318 prefixEnd_2083318 1069743490163585242444001 := by
  unfold tailWord_2083318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749053116656385202039663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50656566577668108821756405 4749053116656385202039663)
  ·
    refine ⟨7123579674984577803059495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4749053116656385202039663 7123579674984577803059495)
    ·
      refine ⟨10685369512476866704589243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123579674984577803059495 10685369512476866704589243)
      ·
        refine ⟨16028054268715300056883865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685369512476866704589243 16028054268715300056883865)
        ·
          refine ⟨12021040701536475042662899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16028054268715300056883865 12021040701536475042662899)
          ·
            refine ⟨18031561052304712563994349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12021040701536475042662899 18031561052304712563994349)
            ·
              refine ⟨6761835394614267211497881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18031561052304712563994349 6761835394614267211497881)
              ·
                refine ⟨5071376545960700408623411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6761835394614267211497881 5071376545960700408623411)
                ·
                  refine ⟨7607064818941050612935117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071376545960700408623411 7607064818941050612935117)
                  ·
                    refine ⟨2852649307102893979850669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7607064818941050612935117 2852649307102893979850669)
                    ·
                      refine ⟨1069743490163585242444001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852649307102893979850669 1069743490163585242444001)
                      ·
                        rfl

theorem cell23_2083318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_2083318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083318 prefixEnd_2083318 := by exact prefixLift 2083318
  have htrace : WordTrace (prefixWord ++ tailWord_2083318) baseStart_2083318 baseEnd_2083318 := by
    simpa [prefixWord, tailWord_2083318, baseEnd_2083318] using wordTrace_append hprefix tailTrace_2083318
  have hstable : (prefixWord ++ tailWord_2083318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083318).length < 2 ^ (prefixWord ++ tailWord_2083318).sum := by decide
  have hdescent : baseEnd_2083318 < baseStart_2083318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083361 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2083361 : Nat := 118140960795 + 2083361 * 2 ^ 59
def prefixEnd_2083361 : Nat := 4983230072969 + 3 ^ 40 * 2083361 * 2
def baseEnd_2083361 : Nat := 1069765569831728574206303

theorem tailTrace_2083361 : CollatzResearch.WordTrace tailWord_2083361 prefixEnd_2083361 1069765569831728574206303 := by
  unfold tailWord_2083361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75986418205346381576449937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50657612136897587717633291 75986418205346381576449937)
  ·
    refine ⟨56989813654009786182337453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75986418205346381576449937 56989813654009786182337453)
    ·
      refine ⟨21371180120253669818376545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56989813654009786182337453 21371180120253669818376545)
      ·
        refine ⟨16028385090190252363782409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21371180120253669818376545 16028385090190252363782409)
        ·
          refine ⟨12021288817642689272836807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16028385090190252363782409 12021288817642689272836807)
          ·
            refine ⟨18031933226464033909255211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12021288817642689272836807 18031933226464033909255211)
            ·
              refine ⟨27047899839696050863882817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18031933226464033909255211 27047899839696050863882817)
              ·
                refine ⟨20285924879772038147912113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27047899839696050863882817 20285924879772038147912113)
                ·
                  refine ⟨15214443659829028610934085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20285924879772038147912113 15214443659829028610934085)
                  ·
                    refine ⟨2852708186217942864550141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15214443659829028610934085 2852708186217942864550141)
                    ·
                      refine ⟨1069765569831728574206303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852708186217942864550141 1069765569831728574206303)
                      ·
                        rfl

theorem cell23_2083361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2083361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083361 prefixEnd_2083361 := by exact prefixLift 2083361
  have htrace : WordTrace (prefixWord ++ tailWord_2083361) baseStart_2083361 baseEnd_2083361 := by
    simpa [prefixWord, tailWord_2083361, baseEnd_2083361] using wordTrace_append hprefix tailTrace_2083361
  have hstable : (prefixWord ++ tailWord_2083361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083361).length < 2 ^ (prefixWord ++ tailWord_2083361).sum := by decide
  have hdescent : baseEnd_2083361 < baseStart_2083361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083373 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2083373 : Nat := 118140960795 + 2083373 * 2 ^ 59
def prefixEnd_2083373 : Nat := 4983230072969 + 3 ^ 40 * 2083373 * 2
def baseEnd_2083373 : Nat := 1069771731599582527256249

theorem tailTrace_2083373 : CollatzResearch.WordTrace tailWord_2083373 prefixEnd_2083373 1069771731599582527256249 := by
  unfold tailWord_2083373
  simp only [CollatzResearch.WordTrace]
  refine ⟨75986855881302907625886773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50657903920868605083924515 75986855881302907625886773)
  ·
    refine ⟨7123767738872147589926885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75986855881302907625886773 7123767738872147589926885)
    ·
      refine ⟨1335706451038527673111291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7123767738872147589926885 1335706451038527673111291)
      ·
        refine ⟨2003559676557791509666937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335706451038527673111291 2003559676557791509666937)
        ·
          refine ⟨1502669757418343632250203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2003559676557791509666937 1502669757418343632250203)
          ·
            refine ⟨2254004636127515448375305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502669757418343632250203 2254004636127515448375305)
            ·
              refine ⟨1690503477095636586281479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2254004636127515448375305 1690503477095636586281479)
              ·
                refine ⟨2535755215643454879422219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690503477095636586281479 2535755215643454879422219)
                ·
                  refine ⟨3803632823465182319133329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535755215643454879422219 3803632823465182319133329)
                  ·
                    refine ⟨2852724617598886739349997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3803632823465182319133329 2852724617598886739349997)
                    ·
                      refine ⟨1069771731599582527256249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852724617598886739349997 1069771731599582527256249)
                      ·
                        rfl

theorem cell23_2083373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2083373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083373 prefixEnd_2083373 := by exact prefixLift 2083373
  have htrace : WordTrace (prefixWord ++ tailWord_2083373) baseStart_2083373 baseEnd_2083373 := by
    simpa [prefixWord, tailWord_2083373, baseEnd_2083373] using wordTrace_append hprefix tailTrace_2083373
  have hstable : (prefixWord ++ tailWord_2083373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083373).length < 2 ^ (prefixWord ++ tailWord_2083373).sum := by decide
  have hdescent : baseEnd_2083373 < baseStart_2083373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083391 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_2083391 : Nat := 118140960795 + 2083391 * 2 ^ 59
def prefixEnd_2083391 : Nat := 4983230072969 + 3 ^ 40 * 2083391 * 2
def baseEnd_2083391 : Nat := 1069780974251363456831165

theorem tailTrace_2083391 : CollatzResearch.WordTrace tailWord_2083391 prefixEnd_2083391 1069780974251363456831165 := by
  unfold tailWord_2083391
  simp only [CollatzResearch.WordTrace]
  refine ⟨75987512395237696700042027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50658341596825131133361351 75987512395237696700042027)
  ·
    refine ⟨113981268592856545050063041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75987512395237696700042027 113981268592856545050063041)
    ·
      refine ⟨85485951444642408787547281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113981268592856545050063041 85485951444642408787547281)
      ·
        refine ⟨64114463583481806590660461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85485951444642408787547281 64114463583481806590660461)
        ·
          refine ⟨24042923843805677471497673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64114463583481806590660461 24042923843805677471497673)
          ·
            refine ⟨18032192882854258103623255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24042923843805677471497673 18032192882854258103623255)
            ·
              refine ⟨27048289324281387155434883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18032192882854258103623255 27048289324281387155434883)
              ·
                refine ⟨40572433986422080733152325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27048289324281387155434883 40572433986422080733152325)
                ·
                  refine ⟨7607331372454140137466061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40572433986422080733152325 7607331372454140137466061)
                  ·
                    refine ⟨2852749264670302551549773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7607331372454140137466061 2852749264670302551549773)
                    ·
                      refine ⟨1069780974251363456831165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852749264670302551549773 1069780974251363456831165)
                      ·
                        rfl

theorem cell23_2083391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_2083391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083391 prefixEnd_2083391 := by exact prefixLift 2083391
  have htrace : WordTrace (prefixWord ++ tailWord_2083391) baseStart_2083391 baseEnd_2083391 := by
    simpa [prefixWord, tailWord_2083391, baseEnd_2083391] using wordTrace_append hprefix tailTrace_2083391
  have hstable : (prefixWord ++ tailWord_2083391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083391).length < 2 ^ (prefixWord ++ tailWord_2083391).sum := by decide
  have hdescent : baseEnd_2083391 < baseStart_2083391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083432 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 5]
def baseStart_2083432 : Nat := 118140960795 + 2083432 * 2 ^ 59
def prefixEnd_2083432 : Nat := 4983230072969 + 3 ^ 40 * 2083432 * 2
def baseEnd_2083432 : Nat := 118866891884244199602053

theorem tailTrace_2083432 : CollatzResearch.WordTrace tailWord_2083432 prefixEnd_2083432 118866891884244199602053 := by
  unfold tailWord_2083432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37994503894044580351142275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50659338525392773801523033 37994503894044580351142275)
  ·
    refine ⟨56991755841066870526713413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37994503894044580351142275 56991755841066870526713413)
    ·
      refine ⟨10685954220200038223758765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56991755841066870526713413 10685954220200038223758765)
      ·
        refine ⟨4007232832575014333909537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10685954220200038223758765 4007232832575014333909537)
        ·
          refine ⟨3005424624431260750432153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007232832575014333909537 3005424624431260750432153)
          ·
            refine ⟨2254068468323445562824115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3005424624431260750432153 2254068468323445562824115)
            ·
              refine ⟨3381102702485168344236173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254068468323445562824115 3381102702485168344236173)
              ·
                refine ⟨1267913513431938129088565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381102702485168344236173 1267913513431938129088565)
                ·
                  refine ⟨118866891884244199602053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1267913513431938129088565 118866891884244199602053)
                  ·
                    rfl

theorem cell23_2083432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 5].length) (baseStart_2083432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083432 prefixEnd_2083432 := by exact prefixLift 2083432
  have htrace : WordTrace (prefixWord ++ tailWord_2083432) baseStart_2083432 baseEnd_2083432 := by
    simpa [prefixWord, tailWord_2083432, baseEnd_2083432] using wordTrace_append hprefix tailTrace_2083432
  have hstable : (prefixWord ++ tailWord_2083432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083432).length < 2 ^ (prefixWord ++ tailWord_2083432).sum := by decide
  have hdescent : baseEnd_2083432 < baseStart_2083432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083445 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2083445 : Nat := 118140960795 + 2083445 * 2 ^ 59
def prefixEnd_2083445 : Nat := 4983230072969 + 3 ^ 40 * 2083445 * 2
def baseEnd_2083445 : Nat := 356602900735568748518639

theorem tailTrace_2083445 : CollatzResearch.WordTrace tailWord_2083445 prefixEnd_2083445 356602900735568748518639 := by
  unfold tailWord_2083445
  simp only [CollatzResearch.WordTrace]
  refine ⟨75989481937042063922507789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50659654624694709281671859 75989481937042063922507789)
  ·
    refine ⟨28496055726390773970940421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75989481937042063922507789 28496055726390773970940421)
    ·
      refine ⟨5343010448698270119551329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28496055726390773970940421 5343010448698270119551329)
      ·
        refine ⟨4007257836523702589663497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5343010448698270119551329 4007257836523702589663497)
        ·
          refine ⟨3005443377392776942247623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007257836523702589663497 3005443377392776942247623)
          ·
            refine ⟨4508165066089165413371435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005443377392776942247623 4508165066089165413371435)
            ·
              refine ⟨6762247599133748120057153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508165066089165413371435 6762247599133748120057153)
              ·
                refine ⟨5071685699350311090042865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762247599133748120057153 5071685699350311090042865)
                ·
                  refine ⟨3803764274512733317532149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071685699350311090042865 3803764274512733317532149)
                  ·
                    refine ⟨356602900735568748518639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3803764274512733317532149 356602900735568748518639)
                    ·
                      rfl

theorem cell23_2083445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2083445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083445 prefixEnd_2083445 := by exact prefixLift 2083445
  have htrace : WordTrace (prefixWord ++ tailWord_2083445) baseStart_2083445 baseEnd_2083445 := by
    simpa [prefixWord, tailWord_2083445, baseEnd_2083445] using wordTrace_append hprefix tailTrace_2083445
  have hstable : (prefixWord ++ tailWord_2083445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083445).length < 2 ^ (prefixWord ++ tailWord_2083445).sum := by decide
  have hdescent : baseEnd_2083445 < baseStart_2083445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083451 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 3]
def baseStart_2083451 : Nat := 118140960795 + 2083451 * 2 ^ 59
def prefixEnd_2083451 : Nat := 4983230072969 + 3 ^ 40 * 2083451 * 2
def baseEnd_2083451 : Nat := 1069811783090633222080889

theorem tailTrace_2083451 : CollatzResearch.WordTrace tailWord_2083451 prefixEnd_2083451 1069811783090633222080889 := by
  unfold tailWord_2083451
  simp only [CollatzResearch.WordTrace]
  refine ⟨75989700775020326947226207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50659800516680217964817471 75989700775020326947226207)
  ·
    refine ⟨113984551162530490420839311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75989700775020326947226207 113984551162530490420839311)
    ·
      refine ⟨170976826743795735631258967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113984551162530490420839311 170976826743795735631258967)
      ·
        refine ⟨256465240115693603446888451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170976826743795735631258967 256465240115693603446888451)
        ·
          refine ⟨384697860173540405170332677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256465240115693603446888451 384697860173540405170332677)
          ·
            refine ⟨72130848782538825969437377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384697860173540405170332677 72130848782538825969437377)
            ·
              refine ⟨54098136586904119477078033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72130848782538825969437377 54098136586904119477078033)
              ·
                refine ⟨40573602440178089607808525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54098136586904119477078033 40573602440178089607808525)
                ·
                  refine ⟨15215100915066783602928197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40573602440178089607808525 15215100915066783602928197)
                  ·
                    refine ⟨2852831421575021925549037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15215100915066783602928197 2852831421575021925549037)
                    ·
                      refine ⟨1069811783090633222080889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852831421575021925549037 1069811783090633222080889)
                      ·
                        rfl

theorem cell23_2083451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 3].length) (baseStart_2083451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083451 prefixEnd_2083451 := by exact prefixLift 2083451
  have htrace : WordTrace (prefixWord ++ tailWord_2083451) baseStart_2083451 baseEnd_2083451 := by
    simpa [prefixWord, tailWord_2083451, baseEnd_2083451] using wordTrace_append hprefix tailTrace_2083451
  have hstable : (prefixWord ++ tailWord_2083451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083451).length < 2 ^ (prefixWord ++ tailWord_2083451).sum := by decide
  have hdescent : baseEnd_2083451 < baseStart_2083451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083471 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 6]
def baseStart_2083471 : Nat := 118140960795 + 2083471 * 2 ^ 59
def prefixEnd_2083471 : Nat := 4983230072969 + 3 ^ 40 * 2083471 * 2
def baseEnd_2083471 : Nat := 118869116967080349314533

theorem tailTrace_2083471 : CollatzResearch.WordTrace tailWord_2083471 prefixEnd_2083471 118869116967080349314533 := by
  unfold tailWord_2083471
  simp only [CollatzResearch.WordTrace]
  refine ⟨75990430234947870362954267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50660286823298580241969511 75990430234947870362954267)
  ·
    refine ⟨113985645352421805544431401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75990430234947870362954267 113985645352421805544431401)
    ·
      refine ⟨85489234014316354158323551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113985645352421805544431401 85489234014316354158323551)
      ·
        refine ⟨128233851021474531237485327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85489234014316354158323551 128233851021474531237485327)
        ·
          refine ⟨192350776532211796856227991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128233851021474531237485327 192350776532211796856227991)
          ·
            refine ⟨288526164798317695284341987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192350776532211796856227991 288526164798317695284341987)
            ·
              refine ⟨432789247197476542926512981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288526164798317695284341987 432789247197476542926512981)
              ·
                refine ⟨2535874495297714118710037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 432789247197476542926512981 2535874495297714118710037)
                ·
                  refine ⟨118869116967080349314533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2535874495297714118710037 118869116967080349314533)
                  ·
                    rfl

theorem cell23_2083471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 6].length) (baseStart_2083471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083471 prefixEnd_2083471 := by exact prefixLift 2083471
  have htrace : WordTrace (prefixWord ++ tailWord_2083471) baseStart_2083471 baseEnd_2083471 := by
    simpa [prefixWord, tailWord_2083471, baseEnd_2083471] using wordTrace_append hprefix tailTrace_2083471
  have hstable : (prefixWord ++ tailWord_2083471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083471).length < 2 ^ (prefixWord ++ tailWord_2083471).sum := by decide
  have hdescent : baseEnd_2083471 < baseStart_2083471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083482 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2083482 : Nat := 118140960795 + 2083482 * 2 ^ 59
def prefixEnd_2083482 : Nat := 4983230072969 + 3 ^ 40 * 2083482 * 2
def baseEnd_2083482 : Nat := 1069827700990922600793247

theorem tailTrace_2083482 : CollatzResearch.WordTrace tailWord_2083482 prefixEnd_2083482 1069827700990922600793247 := by
  unfold tailWord_2083482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997707859477004810401175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50660554291938679494403133 18997707859477004810401175)
  ·
    refine ⟨28496561789215507215601763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18997707859477004810401175 28496561789215507215601763)
    ·
      refine ⟨42744842683823260823402645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28496561789215507215601763 42744842683823260823402645)
      ·
        refine ⟨2003664500804215351096999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42744842683823260823402645 2003664500804215351096999)
        ·
          refine ⟨3005496751206323026645499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003664500804215351096999 3005496751206323026645499)
          ·
            refine ⟨4508245126809484539968249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005496751206323026645499 4508245126809484539968249)
            ·
              refine ⟨3381183845107113404976187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508245126809484539968249 3381183845107113404976187)
              ·
                refine ⟨5071775767660670107464281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381183845107113404976187 5071775767660670107464281)
                ·
                  refine ⟨3803831825745502580598211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071775767660670107464281 3803831825745502580598211)
                  ·
                    refine ⟨5705747738618253870897317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3803831825745502580598211 5705747738618253870897317)
                    ·
                      refine ⟨1069827700990922600793247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5705747738618253870897317 1069827700990922600793247)
                      ·
                        rfl

theorem cell23_2083482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2083482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083482 prefixEnd_2083482 := by exact prefixLift 2083482
  have htrace : WordTrace (prefixWord ++ tailWord_2083482) baseStart_2083482 baseEnd_2083482 := by
    simpa [prefixWord, tailWord_2083482, baseEnd_2083482] using wordTrace_append hprefix tailTrace_2083482
  have hstable : (prefixWord ++ tailWord_2083482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083482).length < 2 ^ (prefixWord ++ tailWord_2083482).sum := by decide
  have hdescent : baseEnd_2083482 < baseStart_2083482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083502 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2083502 : Nat := 118140960795 + 2083502 * 2 ^ 59
def prefixEnd_2083502 : Nat := 4983230072969 + 3 ^ 40 * 2083502 * 2
def baseEnd_2083502 : Nat := 1069837970604012522543155

theorem tailTrace_2083502 : CollatzResearch.WordTrace tailWord_2083502 prefixEnd_2083502 1069837970604012522543155 := by
  unfold tailWord_2083502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498945112229445332166595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50661040598557041771555173 9498945112229445332166595)
  ·
    refine ⟨14248417668344167998249893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498945112229445332166595 14248417668344167998249893)
    ·
      refine ⟨2671578312814531499671855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14248417668344167998249893 2671578312814531499671855)
      ·
        refine ⟨4007367469221797249507783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671578312814531499671855 4007367469221797249507783)
        ·
          refine ⟨6011051203832695874261675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007367469221797249507783 6011051203832695874261675)
          ·
            refine ⟨9016576805749043811392513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011051203832695874261675 9016576805749043811392513)
            ·
              refine ⟨6762432604311782858544385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9016576805749043811392513 6762432604311782858544385)
              ·
                refine ⟨5071824453233837143908289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762432604311782858544385 5071824453233837143908289)
                ·
                  refine ⟨3803868339925377857931217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071824453233837143908289 3803868339925377857931217)
                  ·
                    refine ⟨2852901254944033393448413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3803868339925377857931217 2852901254944033393448413)
                    ·
                      refine ⟨1069837970604012522543155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852901254944033393448413 1069837970604012522543155)
                      ·
                        rfl

theorem cell23_2083502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2083502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083502 prefixEnd_2083502 := by exact prefixLift 2083502
  have htrace : WordTrace (prefixWord ++ tailWord_2083502) baseStart_2083502 baseEnd_2083502 := by
    simpa [prefixWord, tailWord_2083502, baseEnd_2083502] using wordTrace_append hprefix tailTrace_2083502
  have hstable : (prefixWord ++ tailWord_2083502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083502).length < 2 ^ (prefixWord ++ tailWord_2083502).sum := by decide
  have hdescent : baseEnd_2083502 < baseStart_2083502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083509 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2083509 : Nat := 118140960795 + 2083509 * 2 ^ 59
def prefixEnd_2083509 : Nat := 4983230072969 + 3 ^ 40 * 2083509 * 2
def baseEnd_2083509 : Nat := 356613854989531331718541

theorem tailTrace_2083509 : CollatzResearch.WordTrace tailWord_2083509 prefixEnd_2083509 356613854989531331718541 := by
  unfold tailWord_2083509
  simp only [CollatzResearch.WordTrace]
  refine ⟨75991816208810202852837581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50661210805873468568558387 75991816208810202852837581)
  ·
    refine ⟨28496931078303826069814093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75991816208810202852837581 28496931078303826069814093)
    ·
      refine ⟨10686349154363934776180285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28496931078303826069814093 10686349154363934776180285)
      ·
        refine ⟨4007380932886475541067607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10686349154363934776180285 4007380932886475541067607)
        ·
          refine ⟨6011071399329713311601411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007380932886475541067607 6011071399329713311601411)
          ·
            refine ⟨9016607098994569967402117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011071399329713311601411 9016607098994569967402117)
            ·
              refine ⟨1690613831061481868887897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9016607098994569967402117 1690613831061481868887897)
              ·
                refine ⟨1267960373296111401665923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690613831061481868887897 1267960373296111401665923)
                ·
                  refine ⟨1901940559944167102498885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267960373296111401665923 1901940559944167102498885)
                  ·
                    refine ⟨356613854989531331718541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901940559944167102498885 356613854989531331718541)
                    ·
                      rfl

theorem cell23_2083509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2083509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083509 prefixEnd_2083509 := by exact prefixLift 2083509
  have htrace : WordTrace (prefixWord ++ tailWord_2083509) baseStart_2083509 baseEnd_2083509 := by
    simpa [prefixWord, tailWord_2083509, baseEnd_2083509] using wordTrace_append hprefix tailTrace_2083509
  have hstable : (prefixWord ++ tailWord_2083509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083509).length < 2 ^ (prefixWord ++ tailWord_2083509).sum := by decide
  have hdescent : baseEnd_2083509 < baseStart_2083509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083518 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2083518 : Nat := 118140960795 + 2083518 * 2 ^ 59
def prefixEnd_2083518 : Nat := 4983230072969 + 3 ^ 40 * 2083518 * 2
def baseEnd_2083518 : Nat := 356615395431494819981027

theorem tailTrace_2083518 : CollatzResearch.WordTrace tailWord_2083518 prefixEnd_2083518 356615395431494819981027 := by
  unfold tailWord_2083518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499018058222199673739401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50661429643851731593276805 9499018058222199673739401)
  ·
    refine ⟨7124263543666649755304551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9499018058222199673739401 7124263543666649755304551)
    ·
      refine ⟨10686395315499974632956827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124263543666649755304551 10686395315499974632956827)
      ·
        refine ⟨16029592973249961949435241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686395315499974632956827 16029592973249961949435241)
        ·
          refine ⟨12022194729937471462076431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16029592973249961949435241 12022194729937471462076431)
          ·
            refine ⟨18033292094906207193114647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022194729937471462076431 18033292094906207193114647)
            ·
              refine ⟨27049938142359310789671971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18033292094906207193114647 27049938142359310789671971)
              ·
                refine ⟨40574907213538966184507957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27049938142359310789671971 40574907213538966184507957)
                ·
                  refine ⟨3803897551269278079797621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40574907213538966184507957 3803897551269278079797621)
                  ·
                    refine ⟨356615395431494819981027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3803897551269278079797621 356615395431494819981027)
                    ·
                      rfl

theorem cell23_2083518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2083518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083518 prefixEnd_2083518 := by exact prefixLift 2083518
  have htrace : WordTrace (prefixWord ++ tailWord_2083518) baseStart_2083518 baseEnd_2083518 := by
    simpa [prefixWord, tailWord_2083518, baseEnd_2083518] using wordTrace_append hprefix tailTrace_2083518
  have hstable : (prefixWord ++ tailWord_2083518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083518).length < 2 ^ (prefixWord ++ tailWord_2083518).sum := by decide
  have hdescent : baseEnd_2083518 < baseStart_2083518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083532 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2083532 : Nat := 118140960795 + 2083532 * 2 ^ 59
def prefixEnd_2083532 : Nat := 4983230072969 + 3 ^ 40 * 2083532 * 2
def baseEnd_2083532 : Nat := 1069853375023647405168017

theorem tailTrace_2083532 : CollatzResearch.WordTrace tailWord_2083532 prefixEnd_2083532 1069853375023647405168017 := by
  unfold tailWord_2083532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37996327543863438890462425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50661770058484585187283233 37996327543863438890462425)
  ·
    refine ⟨28497245657897579167846819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37996327543863438890462425 28497245657897579167846819)
    ·
      refine ⟨42745868486846368751770229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28497245657897579167846819 42745868486846368751770229)
      ·
        refine ⟨4007425170641847070478459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42745868486846368751770229 4007425170641847070478459)
        ·
          refine ⟨6011137755962770605717689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007425170641847070478459 6011137755962770605717689)
          ·
            refine ⟨4508353316972077954288267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011137755962770605717689 4508353316972077954288267)
            ·
              refine ⟨6762529975458116931432401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508353316972077954288267 6762529975458116931432401)
              ·
                refine ⟨5071897481593587698574301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762529975458116931432401 5071897481593587698574301)
                ·
                  refine ⟨1901961555597595386965363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5071897481593587698574301 1901961555597595386965363)
                  ·
                    refine ⟨2852942333396393080448045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1901961555597595386965363 2852942333396393080448045)
                    ·
                      refine ⟨1069853375023647405168017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2852942333396393080448045 1069853375023647405168017)
                      ·
                        rfl

theorem cell23_2083532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2083532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083532 prefixEnd_2083532 := by exact prefixLift 2083532
  have htrace : WordTrace (prefixWord ++ tailWord_2083532) baseStart_2083532 baseEnd_2083532 := by
    simpa [prefixWord, tailWord_2083532, baseEnd_2083532] using wordTrace_append hprefix tailTrace_2083532
  have hstable : (prefixWord ++ tailWord_2083532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083532).length < 2 ^ (prefixWord ++ tailWord_2083532).sum := by decide
  have hdescent : baseEnd_2083532 < baseStart_2083532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083565 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2083565 : Nat := 118140960795 + 2083565 * 2 ^ 59
def prefixEnd_2083565 : Nat := 4983230072969 + 3 ^ 40 * 2083565 * 2
def baseEnd_2083565 : Nat := 356623439961748592018455

theorem tailTrace_2083565 : CollatzResearch.WordTrace tailWord_2083565 prefixEnd_2083565 356623439961748592018455 := by
  unfold tailWord_2083565
  simp only [CollatzResearch.WordTrace]
  refine ⟨75993858696607324416876149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50662572464404882944584099 75993858696607324416876149)
  ·
    refine ⟨7124424252806936664082139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75993858696607324416876149 7124424252806936664082139)
    ·
      refine ⟨10686636379210404996123209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124424252806936664082139 10686636379210404996123209)
      ·
        refine ⟨8014977284407803747092407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10686636379210404996123209 8014977284407803747092407)
        ·
          refine ⟨12022465926611705620638611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8014977284407803747092407 12022465926611705620638611)
          ·
            refine ⟨18033698889917558430957917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022465926611705620638611 18033698889917558430957917)
            ·
              refine ⟨6762637083719084411609219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18033698889917558430957917 6762637083719084411609219)
              ·
                refine ⟨10143955625578626617413829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762637083719084411609219 10143955625578626617413829)
                ·
                  refine ⟨1901991679795992490765093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10143955625578626617413829 1901991679795992490765093)
                  ·
                    refine ⟨356623439961748592018455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901991679795992490765093 356623439961748592018455)
                    ·
                      rfl

theorem cell23_2083565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2083565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083565 prefixEnd_2083565 := by exact prefixLift 2083565
  have htrace : WordTrace (prefixWord ++ tailWord_2083565) baseStart_2083565 baseEnd_2083565 := by
    simpa [prefixWord, tailWord_2083565, baseEnd_2083565] using wordTrace_append hprefix tailTrace_2083565
  have hstable : (prefixWord ++ tailWord_2083565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083565).length < 2 ^ (prefixWord ++ tailWord_2083565).sum := by decide
  have hdescent : baseEnd_2083565 < baseStart_2083565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083571 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_2083571 : Nat := 118140960795 + 2083571 * 2 ^ 59
def prefixEnd_2083571 : Nat := 4983230072969 + 3 ^ 40 * 2083571 * 2
def baseEnd_2083571 : Nat := 1069873400769172752580337

theorem tailTrace_2083571 : CollatzResearch.WordTrace tailWord_2083571 prefixEnd_2083571 1069873400769172752580337 := by
  unfold tailWord_2083571
  simp only [CollatzResearch.WordTrace]
  refine ⟨75994077534585587441594567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50662718356390391627729711 75994077534585587441594567)
  ·
    refine ⟨113991116301878381162391851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75994077534585587441594567 113991116301878381162391851)
    ·
      refine ⟨170986674452817571743587777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113991116301878381162391851 170986674452817571743587777)
      ·
        refine ⟨128240005839613178807690833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170986674452817571743587777 128240005839613178807690833)
        ·
          refine ⟨96180004379709884105768125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128240005839613178807690833 96180004379709884105768125)
          ·
            refine ⟨36067501642391206539663047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96180004379709884105768125 36067501642391206539663047)
            ·
              refine ⟨54101252463586809809494571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36067501642391206539663047 54101252463586809809494571)
              ·
                refine ⟨81151878695380214714241857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54101252463586809809494571 81151878695380214714241857)
                ·
                  refine ⟨60863909021535161035681393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81151878695380214714241857 60863909021535161035681393)
                  ·
                    refine ⟨45647931766151370776761045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60863909021535161035681393 45647931766151370776761045)
                    ·
                      refine ⟨1069873400769172752580337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45647931766151370776761045 1069873400769172752580337)
                      ·
                        rfl

theorem cell23_2083571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_2083571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083571 prefixEnd_2083571 := by exact prefixLift 2083571
  have htrace : WordTrace (prefixWord ++ tailWord_2083571) baseStart_2083571 baseEnd_2083571 := by
    simpa [prefixWord, tailWord_2083571, baseEnd_2083571] using wordTrace_append hprefix tailTrace_2083571
  have hstable : (prefixWord ++ tailWord_2083571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083571).length < 2 ^ (prefixWord ++ tailWord_2083571).sum := by decide
  have hdescent : baseEnd_2083571 < baseStart_2083571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083582 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2083582 : Nat := 118140960795 + 2083582 * 2 ^ 59
def prefixEnd_2083582 : Nat := 4983230072969 + 3 ^ 40 * 2083582 * 2
def baseEnd_2083582 : Nat := 356626349685457403180929

theorem tailTrace_2083582 : CollatzResearch.WordTrace tailWord_2083582 prefixEnd_2083582 356626349685457403180929 := by
  unfold tailWord_2083582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499309842193217040030625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50662985825030490880163333 9499309842193217040030625)
  ·
    refine ⟨7124482381644912780022969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9499309842193217040030625 7124482381644912780022969)
    ·
      refine ⟨5343361786233684585017227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7124482381644912780022969 5343361786233684585017227)
      ·
        refine ⟨8015042679350526877525841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343361786233684585017227 8015042679350526877525841)
        ·
          refine ⟨6011282009512895158144381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8015042679350526877525841 6011282009512895158144381)
          ·
            refine ⟨2254230753567335684304143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6011282009512895158144381 2254230753567335684304143)
            ·
              refine ⟨3381346130351003526456215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254230753567335684304143 3381346130351003526456215)
              ·
                refine ⟨5072019195526505289684323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381346130351003526456215 5072019195526505289684323)
                ·
                  refine ⟨7608028793289757934526485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072019195526505289684323 7608028793289757934526485)
                  ·
                    refine ⟨356626349685457403180929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7608028793289757934526485 356626349685457403180929)
                    ·
                      rfl

theorem cell23_2083582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2083582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083582 prefixEnd_2083582 := by exact prefixLift 2083582
  have htrace : WordTrace (prefixWord ++ tailWord_2083582) baseStart_2083582 baseEnd_2083582 := by
    simpa [prefixWord, tailWord_2083582, baseEnd_2083582] using wordTrace_append hprefix tailTrace_2083582
  have hstable : (prefixWord ++ tailWord_2083582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083582).length < 2 ^ (prefixWord ++ tailWord_2083582).sum := by decide
  have hdescent : baseEnd_2083582 < baseStart_2083582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083592 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_2083592 : Nat := 118140960795 + 2083592 * 2 ^ 59
def prefixEnd_2083592 : Nat := 4983230072969 + 3 ^ 40 * 2083592 * 2
def baseEnd_2083592 : Nat := 1069884183862917170417741

theorem tailTrace_2083592 : CollatzResearch.WordTrace tailWord_2083592 prefixEnd_2083592 1069884183862917170417741 := by
  unfold tailWord_2083592
  simp only [CollatzResearch.WordTrace]
  refine ⟨37997421733754754014054515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50663228978339672018739353 37997421733754754014054515)
  ·
    refine ⟨56996132600632131021081773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37997421733754754014054515 56996132600632131021081773)
    ·
      refine ⟨21373549725237049132905665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56996132600632131021081773 21373549725237049132905665)
      ·
        refine ⟨16030162293927786849679249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21373549725237049132905665 16030162293927786849679249)
        ·
          refine ⟨12022621720445840137259437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16030162293927786849679249 12022621720445840137259437)
          ·
            refine ⟨4508483145167190051472289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12022621720445840137259437 4508483145167190051472289)
            ·
              refine ⟨3381362358875392538604217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508483145167190051472289 3381362358875392538604217)
              ·
                refine ⟨2536021769156544403953163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381362358875392538604217 2536021769156544403953163)
                ·
                  refine ⟨3804032653734816605929745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536021769156544403953163 3804032653734816605929745)
                  ·
                    refine ⟨2853024490301112454447309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804032653734816605929745 2853024490301112454447309)
                    ·
                      refine ⟨1069884183862917170417741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2853024490301112454447309 1069884183862917170417741)
                      ·
                        rfl

theorem cell23_2083592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_2083592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083592 prefixEnd_2083592 := by exact prefixLift 2083592
  have htrace : WordTrace (prefixWord ++ tailWord_2083592) baseStart_2083592 baseEnd_2083592 := by
    simpa [prefixWord, tailWord_2083592, baseEnd_2083592] using wordTrace_append hprefix tailTrace_2083592
  have hstable : (prefixWord ++ tailWord_2083592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083592).length < 2 ^ (prefixWord ++ tailWord_2083592).sum := by decide
  have hdescent : baseEnd_2083592 < baseStart_2083592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083605 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_2083605 : Nat := 118140960795 + 2083605 * 2 ^ 59
def prefixEnd_2083605 : Nat := 4983230072969 + 3 ^ 40 * 2083605 * 2
def baseEnd_2083605 : Nat := 1069890859111425619555181

theorem tailTrace_2083605 : CollatzResearch.WordTrace tailWord_2083605 prefixEnd_2083605 1069890859111425619555181 := by
  unfold tailWord_2083605
  simp only [CollatzResearch.WordTrace]
  refine ⟨75995317616462411248332269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50663545077641607498888179 75995317616462411248332269)
  ·
    refine ⟨28498244106173404218124601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75995317616462411248332269 28498244106173404218124601)
    ·
      refine ⟨21373683079630053163593451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28498244106173404218124601 21373683079630053163593451)
      ·
        refine ⟨32060524619445079745390177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21373683079630053163593451 32060524619445079745390177)
        ·
          refine ⟨24045393464583809809042633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32060524619445079745390177 24045393464583809809042633)
          ·
            refine ⟨18034045098437857356781975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24045393464583809809042633 18034045098437857356781975)
            ·
              refine ⟨27051067647656786035172963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18034045098437857356781975 27051067647656786035172963)
              ·
                refine ⟨40576601471485179052759445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27051067647656786035172963 40576601471485179052759445)
                ·
                  refine ⟨1902028193975867768098099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40576601471485179052759445 1902028193975867768098099)
                  ·
                    refine ⟨2853042290963801652147149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1902028193975867768098099 2853042290963801652147149)
                    ·
                      refine ⟨1069890859111425619555181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2853042290963801652147149 1069890859111425619555181)
                      ·
                        rfl

theorem cell23_2083605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_2083605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083605 prefixEnd_2083605 := by exact prefixLift 2083605
  have htrace : WordTrace (prefixWord ++ tailWord_2083605) baseStart_2083605 baseEnd_2083605 := by
    simpa [prefixWord, tailWord_2083605, baseEnd_2083605] using wordTrace_append hprefix tailTrace_2083605
  have hstable : (prefixWord ++ tailWord_2083605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083605).length < 2 ^ (prefixWord ++ tailWord_2083605).sum := by decide
  have hdescent : baseEnd_2083605 < baseStart_2083605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083628 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_2083628 : Nat := 118140960795 + 2083628 * 2 ^ 59
def prefixEnd_2083628 : Nat := 4983230072969 + 3 ^ 40 * 2083628 * 2
def baseEnd_2083628 : Nat := 1069902669166479029567575

theorem tailTrace_2083628 : CollatzResearch.WordTrace tailWord_2083628 prefixEnd_2083628 1069902669166479029567575 := by
  unfold tailWord_2083628
  simp only [CollatzResearch.WordTrace]
  refine ⟨37998078247689543088209769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50664104330252724117613025 37998078247689543088209769)
  ·
    refine ⟨28498558685767157316157327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37998078247689543088209769 28498558685767157316157327)
    ·
      refine ⟨42747838028650735974235991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28498558685767157316157327 42747838028650735974235991)
      ·
        refine ⟨64121757042976103961353987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42747838028650735974235991 64121757042976103961353987)
        ·
          refine ⟨96182635564464155942030981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64121757042976103961353987 96182635564464155942030981)
          ·
            refine ⟨18034244168337029239130809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96182635564464155942030981 18034244168337029239130809)
            ·
              refine ⟨13525683126252771929348107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18034244168337029239130809 13525683126252771929348107)
              ·
                refine ⟨20288524689379157894022161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13525683126252771929348107 20288524689379157894022161)
                ·
                  refine ⟨15216393517034368420516621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20288524689379157894022161 15216393517034368420516621)
                  ·
                    refine ⟨5706147568887888157693733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15216393517034368420516621 5706147568887888157693733)
                    ·
                      refine ⟨1069902669166479029567575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5706147568887888157693733 1069902669166479029567575)
                      ·
                        rfl

theorem cell23_2083628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_2083628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083628 prefixEnd_2083628 := by exact prefixLift 2083628
  have htrace : WordTrace (prefixWord ++ tailWord_2083628) baseStart_2083628 baseEnd_2083628 := by
    simpa [prefixWord, tailWord_2083628, baseEnd_2083628] using wordTrace_append hprefix tailTrace_2083628
  have hstable : (prefixWord ++ tailWord_2083628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083628).length < 2 ^ (prefixWord ++ tailWord_2083628).sum := by decide
  have hdescent : baseEnd_2083628 < baseStart_2083628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083658 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2083658 : Nat := 118140960795 + 2083658 * 2 ^ 59
def prefixEnd_2083658 : Nat := 4983230072969 + 3 ^ 40 * 2083658 * 2
def baseEnd_2083658 : Nat := 1069918073586113912192437

theorem tailTrace_2083658 : CollatzResearch.WordTrace tailWord_2083658 prefixEnd_2083658 1069918073586113912192437 := by
  unfold tailWord_2083658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999312671317600325002907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50664833790180267533341085 18999312671317600325002907)
  ·
    refine ⟨28498969006976400487504361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18999312671317600325002907 28498969006976400487504361)
    ·
      refine ⟨21374226755232300365628271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28498969006976400487504361 21374226755232300365628271)
      ·
        refine ⟨32061340132848450548442407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374226755232300365628271 32061340132848450548442407)
        ·
          refine ⟨48092010199272675822663611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32061340132848450548442407 48092010199272675822663611)
          ·
            refine ⟨72138015298909013733995417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48092010199272675822663611 72138015298909013733995417)
            ·
              refine ⟨54103511474181760300496563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72138015298909013733995417 54103511474181760300496563)
              ·
                refine ⟨81155267211272640450744845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54103511474181760300496563 81155267211272640450744845)
                ·
                  refine ⟨30433225204227240169029317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81155267211272640450744845 30433225204227240169029317)
                  ·
                    refine ⟨5706229725792607531692997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30433225204227240169029317 5706229725792607531692997)
                    ·
                      refine ⟨1069918073586113912192437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5706229725792607531692997 1069918073586113912192437)
                      ·
                        rfl

theorem cell23_2083658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2083658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083658 prefixEnd_2083658 := by exact prefixLift 2083658
  have htrace : WordTrace (prefixWord ++ tailWord_2083658) baseStart_2083658 baseEnd_2083658 := by
    simpa [prefixWord, tailWord_2083658, baseEnd_2083658] using wordTrace_append hprefix tailTrace_2083658
  have hstable : (prefixWord ++ tailWord_2083658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083658).length < 2 ^ (prefixWord ++ tailWord_2083658).sum := by decide
  have hdescent : baseEnd_2083658 < baseStart_2083658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083662 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_2083662 : Nat := 118140960795 + 2083662 * 2 ^ 59
def prefixEnd_2083662 : Nat := 4983230072969 + 3 ^ 40 * 2083662 * 2
def baseEnd_2083662 : Nat := 1069920127508731896542419

theorem tailTrace_2083662 : CollatzResearch.WordTrace tailWord_2083662 prefixEnd_2083662 1069920127508731896542419 := by
  unfold tailWord_2083662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499674572156988747894655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50664931051503939988771493 9499674572156988747894655)
  ·
    refine ⟨14249511858235483121841983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9499674572156988747894655 14249511858235483121841983)
    ·
      refine ⟨21374267787353224682762975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249511858235483121841983 21374267787353224682762975)
      ·
        refine ⟨32061401681029837024144463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374267787353224682762975 32061401681029837024144463)
        ·
          refine ⟨48092102521544755536216695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32061401681029837024144463 48092102521544755536216695)
          ·
            refine ⟨72138153782317133304325043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48092102521544755536216695 72138153782317133304325043)
            ·
              refine ⟨108207230673475699956487565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72138153782317133304325043 108207230673475699956487565)
              ·
                refine ⟨40577711502553387483682837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108207230673475699956487565 40577711502553387483682837)
                ·
                  refine ⟨1902080226682190038297633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40577711502553387483682837 1902080226682190038297633)
                  ·
                    refine ⟨1426560170011642528723225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902080226682190038297633 1426560170011642528723225)
                    ·
                      refine ⟨1069920127508731896542419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426560170011642528723225 1069920127508731896542419)
                      ·
                        rfl

theorem cell23_2083662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_2083662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083662 prefixEnd_2083662 := by exact prefixLift 2083662
  have htrace : WordTrace (prefixWord ++ tailWord_2083662) baseStart_2083662 baseEnd_2083662 := by
    simpa [prefixWord, tailWord_2083662, baseEnd_2083662] using wordTrace_append hprefix tailTrace_2083662
  have hstable : (prefixWord ++ tailWord_2083662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083662).length < 2 ^ (prefixWord ++ tailWord_2083662).sum := by decide
  have hdescent : baseEnd_2083662 < baseStart_2083662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083679 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 2, 2, 2]
def baseStart_2083679 : Nat := 118140960795 + 2083679 * 2 ^ 59
def prefixEnd_2083679 : Nat := 4983230072969 + 3 ^ 40 * 2083679 * 2
def baseEnd_2083679 : Nat := 1069928856679858330029841

theorem tailTrace_2083679 : CollatzResearch.WordTrace tailWord_2083679 prefixEnd_2083679 1069928856679858330029841 := by
  unfold tailWord_2083679
  simp only [CollatzResearch.WordTrace]
  refine ⟨75998016618194321886526091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50665344412129547924350727 75998016618194321886526091)
  ·
    refine ⟨113997024927291482829789137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75998016618194321886526091 113997024927291482829789137)
    ·
      refine ⟨85497768695468612122341853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113997024927291482829789137 85497768695468612122341853)
      ·
        refine ⟨32061663260800729545878195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85497768695468612122341853 32061663260800729545878195)
        ·
          refine ⟨48092494891201094318817293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32061663260800729545878195 48092494891201094318817293)
          ·
            refine ⟨18034685584200410369556485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48092494891201094318817293 18034685584200410369556485)
            ·
              refine ⟨3381503547037576944291841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18034685584200410369556485 3381503547037576944291841)
              ·
                refine ⟨2536127660278182708218881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381503547037576944291841 2536127660278182708218881)
                ·
                  refine ⟨1902095745208637031164161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2536127660278182708218881 1902095745208637031164161)
                  ·
                    refine ⟨1426571808906477773373121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902095745208637031164161 1426571808906477773373121)
                    ·
                      refine ⟨1069928856679858330029841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426571808906477773373121 1069928856679858330029841)
                      ·
                        rfl

theorem cell23_2083679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_2083679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083679 prefixEnd_2083679 := by exact prefixLift 2083679
  have htrace : WordTrace (prefixWord ++ tailWord_2083679) baseStart_2083679 baseEnd_2083679 := by
    simpa [prefixWord, tailWord_2083679, baseEnd_2083679] using wordTrace_append hprefix tailTrace_2083679
  have hstable : (prefixWord ++ tailWord_2083679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083679).length < 2 ^ (prefixWord ++ tailWord_2083679).sum := by decide
  have hdescent : baseEnd_2083679 < baseStart_2083679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083702 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2083702 : Nat := 118140960795 + 2083702 * 2 ^ 59
def prefixEnd_2083702 : Nat := 4983230072969 + 3 ^ 40 * 2083702 * 2
def baseEnd_2083702 : Nat := 118882296303879082226915

theorem tailTrace_2083702 : CollatzResearch.WordTrace tailWord_2083702 prefixEnd_2083702 118882296303879082226915 := by
  unfold tailWord_2083702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749928468569437300913335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50665903664740664543075573 4749928468569437300913335)
  ·
    refine ⟨7124892702854155951370003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4749928468569437300913335 7124892702854155951370003)
    ·
      refine ⟨10687339054281233927055005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124892702854155951370003 10687339054281233927055005)
      ·
        refine ⟨4007752145355462722645627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10687339054281233927055005 4007752145355462722645627)
        ·
          refine ⟨6011628218033194083968441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007752145355462722645627 6011628218033194083968441)
          ·
            refine ⟨4508721163524895562976331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011628218033194083968441 4508721163524895562976331)
            ·
              refine ⟨6763081745287343344464497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508721163524895562976331 6763081745287343344464497)
              ·
                refine ⟨5072311308965507508348373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6763081745287343344464497 5072311308965507508348373)
                ·
                  refine ⟨118882296303879082226915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5072311308965507508348373 118882296303879082226915)
                  ·
                    rfl

theorem cell23_2083702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2083702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083702 prefixEnd_2083702 := by exact prefixLift 2083702
  have htrace : WordTrace (prefixWord ++ tailWord_2083702) baseStart_2083702 baseEnd_2083702 := by
    simpa [prefixWord, tailWord_2083702, baseEnd_2083702] using wordTrace_append hprefix tailTrace_2083702
  have hstable : (prefixWord ++ tailWord_2083702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083702).length < 2 ^ (prefixWord ++ tailWord_2083702).sum := by decide
  have hdescent : baseEnd_2083702 < baseStart_2083702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083708 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2083708 : Nat := 118140960795 + 2083708 * 2 ^ 59
def prefixEnd_2083708 : Nat := 4983230072969 + 3 ^ 40 * 2083708 * 2
def baseEnd_2083708 : Nat := 1069943747618838716567207

theorem tailTrace_2083708 : CollatzResearch.WordTrace tailWord_2083708 prefixEnd_2083708 1069943747618838716567207 := by
  unfold tailWord_2083708
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999537167544629919665889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50666049556726173226221185 37999537167544629919665889)
  ·
    refine ⟨28499652875658472439749417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37999537167544629919665889 28499652875658472439749417)
    ·
      refine ⟨21374739656743854329812063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28499652875658472439749417 21374739656743854329812063)
      ·
        refine ⟨32062109485115781494718095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374739656743854329812063 32062109485115781494718095)
        ·
          refine ⟨48093164227673672242077143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32062109485115781494718095 48093164227673672242077143)
          ·
            refine ⟨72139746341510508363115715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48093164227673672242077143 72139746341510508363115715)
            ·
              refine ⟨108209619512265762544673573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72139746341510508363115715 108209619512265762544673573)
              ·
                refine ⟨20289303658549830477126295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108209619512265762544673573 20289303658549830477126295)
                ·
                  refine ⟨30433955487824745715689443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20289303658549830477126295 30433955487824745715689443)
                  ·
                    refine ⟨45650933231737118573534165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30433955487824745715689443 45650933231737118573534165)
                    ·
                      refine ⟨1069943747618838716567207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45650933231737118573534165 1069943747618838716567207)
                      ·
                        rfl

theorem cell23_2083708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2083708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083708 prefixEnd_2083708 := by exact prefixLift 2083708
  have htrace : WordTrace (prefixWord ++ tailWord_2083708) baseStart_2083708 baseEnd_2083708 := by
    simpa [prefixWord, tailWord_2083708, baseEnd_2083708] using wordTrace_append hprefix tailTrace_2083708
  have hstable : (prefixWord ++ tailWord_2083708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083708).length < 2 ^ (prefixWord ++ tailWord_2083708).sum := by decide
  have hdescent : baseEnd_2083708 < baseStart_2083708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083730 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2083730 : Nat := 118140960795 + 2083730 * 2 ^ 59
def prefixEnd_2083730 : Nat := 4983230072969 + 3 ^ 40 * 2083730 * 2
def baseEnd_2083730 : Nat := 1069955044193237630492107

theorem tailTrace_2083730 : CollatzResearch.WordTrace tailWord_2083730 prefixEnd_2083730 1069955044193237630492107 := by
  unfold tailWord_2083730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999969185252389399158161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50666584494006371731088429 18999969185252389399158161)
  ·
    refine ⟨14249976888939292049368621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18999969185252389399158161 14249976888939292049368621)
    ·
      refine ⟨5343741333352234518513233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14249976888939292049368621 5343741333352234518513233)
      ·
        refine ⟨4007806000014175888884925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5343741333352234518513233 4007806000014175888884925)
        ·
          refine ⟨1502927250005315958331847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4007806000014175888884925 1502927250005315958331847)
          ·
            refine ⟨2254390875007973937497771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502927250005315958331847 2254390875007973937497771)
            ·
              refine ⟨3381586312511960906246657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254390875007973937497771 3381586312511960906246657)
              ·
                refine ⟨2536189734383970679684993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381586312511960906246657 2536189734383970679684993)
                ·
                  refine ⟨1902142300787978009763745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2536189734383970679684993 1902142300787978009763745)
                  ·
                    refine ⟨1426606725590983507322809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902142300787978009763745 1426606725590983507322809)
                    ·
                      refine ⟨1069955044193237630492107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426606725590983507322809 1069955044193237630492107)
                      ·
                        rfl

theorem cell23_2083730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2083730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083730 prefixEnd_2083730 := by exact prefixLift 2083730
  have htrace : WordTrace (prefixWord ++ tailWord_2083730) baseStart_2083730 baseEnd_2083730 := by
    simpa [prefixWord, tailWord_2083730, baseEnd_2083730] using wordTrace_append hprefix tailTrace_2083730
  have hstable : (prefixWord ++ tailWord_2083730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083730).length < 2 ^ (prefixWord ++ tailWord_2083730).sum := by decide
  have hdescent : baseEnd_2083730 < baseStart_2083730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083735 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2083735 : Nat := 118140960795 + 2083735 * 2 ^ 59
def prefixEnd_2083735 : Nat := 4983230072969 + 3 ^ 40 * 2083735 * 2
def baseEnd_2083735 : Nat := 1069957611596510110929583

theorem tailTrace_2083735 : CollatzResearch.WordTrace tailWord_2083735 prefixEnd_2083735 1069957611596510110929583 := by
  unfold tailWord_2083735
  simp only [CollatzResearch.WordTrace]
  refine ⟨76000059105991443450564659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50666706070660962300376439 76000059105991443450564659)
  ·
    refine ⟨114000088658987165175846989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76000059105991443450564659 114000088658987165175846989)
    ·
      refine ⟨42750033247120186940942621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114000088658987165175846989 42750033247120186940942621)
      ·
        refine ⟨16031262467670070102853483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42750033247120186940942621 16031262467670070102853483)
        ·
          refine ⟨24046893701505105154280225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16031262467670070102853483 24046893701505105154280225)
          ·
            refine ⟨18035170276128828865710169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24046893701505105154280225 18035170276128828865710169)
            ·
              refine ⟨13526377707096621649282627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18035170276128828865710169 13526377707096621649282627)
              ·
                refine ⟨20289566560644932473923941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13526377707096621649282627 20289566560644932473923941)
                ·
                  refine ⟨3804293730120924838860739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20289566560644932473923941 3804293730120924838860739)
                  ·
                    refine ⟨5706440595181387258291109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3804293730120924838860739 5706440595181387258291109)
                    ·
                      refine ⟨1069957611596510110929583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5706440595181387258291109 1069957611596510110929583)
                      ·
                        rfl

theorem cell23_2083735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2083735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083735 prefixEnd_2083735 := by exact prefixLift 2083735
  have htrace : WordTrace (prefixWord ++ tailWord_2083735) baseStart_2083735 baseEnd_2083735 := by
    simpa [prefixWord, tailWord_2083735, baseEnd_2083735] using wordTrace_append hprefix tailTrace_2083735
  have hstable : (prefixWord ++ tailWord_2083735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083735).length < 2 ^ (prefixWord ++ tailWord_2083735).sum := by decide
  have hdescent : baseEnd_2083735 < baseStart_2083735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083755 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 3]
def baseStart_2083755 : Nat := 118140960795 + 2083755 * 2 ^ 59
def prefixEnd_2083755 : Nat := 4983230072969 + 3 ^ 40 * 2083755 * 2
def baseEnd_2083755 : Nat := 1069967881209600032679491

theorem tailTrace_2083755 : CollatzResearch.WordTrace tailWord_2083755 prefixEnd_2083755 1069967881209600032679491 := by
  unfold tailWord_2083755
  simp only [CollatzResearch.WordTrace]
  refine ⟨76000788565918986866292719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50667192377279324577528479 76000788565918986866292719)
  ·
    refine ⟨114001182848878480299439079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76000788565918986866292719 114001182848878480299439079)
    ·
      refine ⟨171001774273317720449158619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114001182848878480299439079 171001774273317720449158619)
      ·
        refine ⟨256502661409976580673737929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171001774273317720449158619 256502661409976580673737929)
        ·
          refine ⟨192376996057482435505303447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256502661409976580673737929 192376996057482435505303447)
          ·
            refine ⟨288565494086223653257955171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192376996057482435505303447 288565494086223653257955171)
            ·
              refine ⟨432848241129335479886932757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288565494086223653257955171 432848241129335479886932757)
              ·
                refine ⟨20289761302937600619699973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432848241129335479886932757 20289761302937600619699973)
                ·
                  refine ⟨3804330244300800116193745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20289761302937600619699973 3804330244300800116193745)
                  ·
                    refine ⟨2853247683225600087145309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804330244300800116193745 2853247683225600087145309)
                    ·
                      refine ⟨1069967881209600032679491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2853247683225600087145309 1069967881209600032679491)
                      ·
                        rfl

theorem cell23_2083755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 3].length) (baseStart_2083755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083755 prefixEnd_2083755 := by exact prefixLift 2083755
  have htrace : WordTrace (prefixWord ++ tailWord_2083755) baseStart_2083755 baseEnd_2083755 := by
    simpa [prefixWord, tailWord_2083755, baseEnd_2083755] using wordTrace_append hprefix tailTrace_2083755
  have hstable : (prefixWord ++ tailWord_2083755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083755).length < 2 ^ (prefixWord ++ tailWord_2083755).sum := by decide
  have hdescent : baseEnd_2083755 < baseStart_2083755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083765 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2083765 : Nat := 118140960795 + 2083765 * 2 ^ 59
def prefixEnd_2083765 : Nat := 4983230072969 + 3 ^ 40 * 2083765 * 2
def baseEnd_2083765 : Nat := 1069973016016144993554445

theorem tailTrace_2083765 : CollatzResearch.WordTrace tailWord_2083765 prefixEnd_2083765 1069973016016144993554445 := by
  unfold tailWord_2083765
  simp only [CollatzResearch.WordTrace]
  refine ⟨76001153295882758574156749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50667435530588505716104499 76001153295882758574156749)
  ·
    refine ⟨28500432485956034465308781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76001153295882758574156749 28500432485956034465308781)
    ·
      refine ⟨10687662182233512924490793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28500432485956034465308781 10687662182233512924490793)
      ·
        refine ⟨8015746636675134693368095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10687662182233512924490793 8015746636675134693368095)
        ·
          refine ⟨12023619955012702040052143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8015746636675134693368095 12023619955012702040052143)
          ·
            refine ⟨18035429932519053060078215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12023619955012702040052143 18035429932519053060078215)
            ·
              refine ⟨27053144898778579590117323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18035429932519053060078215 27053144898778579590117323)
              ·
                refine ⟨40579717348167869385175985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27053144898778579590117323 40579717348167869385175985)
                ·
                  refine ⟨30434788011125902038881989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40579717348167869385175985 30434788011125902038881989)
                  ·
                    refine ⟨5706522752086106632290373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30434788011125902038881989 5706522752086106632290373)
                    ·
                      refine ⟨1069973016016144993554445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5706522752086106632290373 1069973016016144993554445)
                      ·
                        rfl

theorem cell23_2083765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2083765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083765 prefixEnd_2083765 := by exact prefixLift 2083765
  have htrace : WordTrace (prefixWord ++ tailWord_2083765) baseStart_2083765 baseEnd_2083765 := by
    simpa [prefixWord, tailWord_2083765, baseEnd_2083765] using wordTrace_append hprefix tailTrace_2083765
  have hstable : (prefixWord ++ tailWord_2083765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083765).length < 2 ^ (prefixWord ++ tailWord_2083765).sum := by decide
  have hdescent : baseEnd_2083765 < baseStart_2083765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083812 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_2083812 : Nat := 118140960795 + 2083812 * 2 ^ 59
def prefixEnd_2083812 : Nat := 4983230072969 + 3 ^ 40 * 2083812 * 2
def baseEnd_2083812 : Nat := 1069997149606906309666729

theorem tailTrace_2083812 : CollatzResearch.WordTrace tailWord_2083812 prefixEnd_2083812 1069997149606906309666729 := by
  unfold tailWord_2083812
  simp only [CollatzResearch.WordTrace]
  refine ⟨38001433763356242800558845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50668578351141657067411793 38001433763356242800558845)
  ·
    refine ⟨14250537661258591050209567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38001433763356242800558845 14250537661258591050209567)
    ·
      refine ⟨21375806491887886575314351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14250537661258591050209567 21375806491887886575314351)
      ·
        refine ⟨32063709737831829862971527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21375806491887886575314351 32063709737831829862971527)
        ·
          refine ⟨48095564606747744794457291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32063709737831829862971527 48095564606747744794457291)
          ·
            refine ⟨72143346910121617191685937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48095564606747744794457291 72143346910121617191685937)
            ·
              refine ⟨54107510182591212893764453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72143346910121617191685937 54107510182591212893764453)
              ·
                refine ⟨10145158159235852417580835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54107510182591212893764453 10145158159235852417580835)
                ·
                  refine ⟨15217737238853778626371253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10145158159235852417580835 15217737238853778626371253)
                  ·
                    refine ⟨1426662866142541746222305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15217737238853778626371253 1426662866142541746222305)
                    ·
                      refine ⟨1069997149606906309666729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426662866142541746222305 1069997149606906309666729)
                      ·
                        rfl

theorem cell23_2083812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_2083812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083812 prefixEnd_2083812 := by exact prefixLift 2083812
  have htrace : WordTrace (prefixWord ++ tailWord_2083812) baseStart_2083812 baseEnd_2083812 := by
    simpa [prefixWord, tailWord_2083812, baseEnd_2083812] using wordTrace_append hprefix tailTrace_2083812
  have hstable : (prefixWord ++ tailWord_2083812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083812).length < 2 ^ (prefixWord ++ tailWord_2083812).sum := by decide
  have hdescent : baseEnd_2083812 < baseStart_2083812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083859 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 3, 2, 2]
def baseStart_2083859 : Nat := 118140960795 + 2083859 * 2 ^ 59
def prefixEnd_2083859 : Nat := 4983230072969 + 3 ^ 40 * 2083859 * 2
def baseEnd_2083859 : Nat := 1070021283197667625779013

theorem tailTrace_2083859 : CollatzResearch.WordTrace tailWord_2083859 prefixEnd_2083859 1070021283197667625779013 := by
  unfold tailWord_2083859
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004581757542212628078631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50669721171694808418719087 76004581757542212628078631)
  ·
    refine ⟨114006872636313318942117947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76004581757542212628078631 114006872636313318942117947)
    ·
      refine ⟨171010308954469978413176921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114006872636313318942117947 171010308954469978413176921)
      ·
        refine ⟨128257731715852483809882691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171010308954469978413176921 128257731715852483809882691)
        ·
          refine ⟨192386597573778725714824037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128257731715852483809882691 192386597573778725714824037)
          ·
            refine ⟨36072487045083511071529507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192386597573778725714824037 36072487045083511071529507)
            ·
              refine ⟨54108730567625266607294261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36072487045083511071529507 54108730567625266607294261)
              ·
                refine ⟨5072693490714868744433837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54108730567625266607294261 5072693490714868744433837)
                ·
                  refine ⟨1902260059018075779162689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5072693490714868744433837 1902260059018075779162689)
                  ·
                    refine ⟨1426695044263556834372017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902260059018075779162689 1426695044263556834372017)
                    ·
                      refine ⟨1070021283197667625779013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426695044263556834372017 1070021283197667625779013)
                      ·
                        rfl

theorem cell23_2083859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 2, 2].length) (baseStart_2083859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083859 prefixEnd_2083859 := by exact prefixLift 2083859
  have htrace : WordTrace (prefixWord ++ tailWord_2083859) baseStart_2083859 baseEnd_2083859 := by
    simpa [prefixWord, tailWord_2083859, baseEnd_2083859] using wordTrace_append hprefix tailTrace_2083859
  have hstable : (prefixWord ++ tailWord_2083859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083859).length < 2 ^ (prefixWord ++ tailWord_2083859).sum := by decide
  have hdescent : baseEnd_2083859 < baseStart_2083859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083865 : List Nat := [1, 2, 1, 2, 1, 1, 7, 8]
def baseStart_2083865 : Nat := 118140960795 + 2083865 * 2 ^ 59
def prefixEnd_2083865 : Nat := 4983230072969 + 3 ^ 40 * 2083865 * 2
def baseEnd_2083865 : Nat := 39630532003022022307555

theorem tailTrace_2083865 : CollatzResearch.WordTrace tailWord_2083865 prefixEnd_2083865 39630532003022022307555 := by
  unfold tailWord_2083865
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004800595520475652797049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50669867063680317101864699 76004800595520475652797049)
  ·
    refine ⟨57003600446640356739597787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76004800595520475652797049 57003600446640356739597787)
    ·
      refine ⟨85505400669960535109396681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57003600446640356739597787 85505400669960535109396681)
      ·
        refine ⟨64129050502470401332047511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85505400669960535109396681 64129050502470401332047511)
        ·
          refine ⟨96193575753705601998071267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64129050502470401332047511 96193575753705601998071267)
          ·
            refine ⟨144290363630558402997106901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96193575753705601998071267 144290363630558402997106901)
            ·
              refine ⟨3381805397591212570244693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144290363630558402997106901 3381805397591212570244693)
              ·
                refine ⟨39630532003022022307555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3381805397591212570244693 39630532003022022307555)
                ·
                  rfl

theorem cell23_2083865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 8].length) (baseStart_2083865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083865 prefixEnd_2083865 := by exact prefixLift 2083865
  have htrace : WordTrace (prefixWord ++ tailWord_2083865) baseStart_2083865 baseEnd_2083865 := by
    simpa [prefixWord, tailWord_2083865, baseEnd_2083865] using wordTrace_append hprefix tailTrace_2083865
  have hstable : (prefixWord ++ tailWord_2083865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083865).length < 2 ^ (prefixWord ++ tailWord_2083865).sum := by decide
  have hdescent : baseEnd_2083865 < baseStart_2083865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083869 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2083869 : Nat := 118140960795 + 2083869 * 2 ^ 59
def prefixEnd_2083869 : Nat := 4983230072969 + 3 ^ 40 * 2083869 * 2
def baseEnd_2083869 : Nat := 356675472668070862217989

theorem tailTrace_2083869 : CollatzResearch.WordTrace tailWord_2083869 prefixEnd_2083869 356675472668070862217989 := by
  unfold tailWord_2083869
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004946487505984335942661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50669964325003989557295107 76004946487505984335942661)
  ·
    refine ⟨14250927466407372062989249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76004946487505984335942661 14250927466407372062989249)
    ·
      refine ⟨10688195599805529047241937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14250927466407372062989249 10688195599805529047241937)
      ·
        refine ⟨8016146699854146785431453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10688195599805529047241937 8016146699854146785431453)
        ·
          refine ⟨3006055012445305044536795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8016146699854146785431453 3006055012445305044536795)
          ·
            refine ⟨4509082518667957566805193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006055012445305044536795 4509082518667957566805193)
            ·
              refine ⟨3381811889000968175103895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509082518667957566805193 3381811889000968175103895)
              ·
                refine ⟨5072717833501452262655843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381811889000968175103895 5072717833501452262655843)
                ·
                  refine ⟨7609076750252178393983765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072717833501452262655843 7609076750252178393983765)
                  ·
                    refine ⟨356675472668070862217989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7609076750252178393983765 356675472668070862217989)
                    ·
                      rfl

theorem cell23_2083869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2083869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083869 prefixEnd_2083869 := by exact prefixLift 2083869
  have htrace : WordTrace (prefixWord ++ tailWord_2083869) baseStart_2083869 baseEnd_2083869 := by
    simpa [prefixWord, tailWord_2083869, baseEnd_2083869] using wordTrace_append hprefix tailTrace_2083869
  have hstable : (prefixWord ++ tailWord_2083869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083869).length < 2 ^ (prefixWord ++ tailWord_2083869).sum := by decide
  have hdescent : baseEnd_2083869 < baseStart_2083869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083876 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2083876 : Nat := 118140960795 + 2083876 * 2 ^ 59
def prefixEnd_2083876 : Nat := 4983230072969 + 3 ^ 40 * 2083876 * 2
def baseEnd_2083876 : Nat := 1070030012368794059266435

theorem tailTrace_2083876 : CollatzResearch.WordTrace tailWord_2083876 prefixEnd_2083876 1070030012368794059266435 := by
  unfold tailWord_2083876
  simp only [CollatzResearch.WordTrace]
  refine ⟨38002600899240312265723741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50670134532320416354298321 38002600899240312265723741)
  ·
    refine ⟨14250975337215117099646403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38002600899240312265723741 14250975337215117099646403)
    ·
      refine ⟨21376463005822675649469605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14250975337215117099646403 21376463005822675649469605)
      ·
        refine ⟨4008086813591751684275551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21376463005822675649469605 4008086813591751684275551)
        ·
          refine ⟨6012130220387627526413327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008086813591751684275551 6012130220387627526413327)
          ·
            refine ⟨9018195330581441289619991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012130220387627526413327 9018195330581441289619991)
            ·
              refine ⟨13527292995872161934429987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9018195330581441289619991 13527292995872161934429987)
              ·
                refine ⟨20290939493808242901644981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13527292995872161934429987 20290939493808242901644981)
                ·
                  refine ⟨1902275577544522772029217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20290939493808242901644981 1902275577544522772029217)
                  ·
                    refine ⟨1426706683158392079021913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902275577544522772029217 1426706683158392079021913)
                    ·
                      refine ⟨1070030012368794059266435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426706683158392079021913 1070030012368794059266435)
                      ·
                        rfl

theorem cell23_2083876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2083876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083876 prefixEnd_2083876 := by exact prefixLift 2083876
  have htrace : WordTrace (prefixWord ++ tailWord_2083876) baseStart_2083876 baseEnd_2083876 := by
    simpa [prefixWord, tailWord_2083876, baseEnd_2083876] using wordTrace_append hprefix tailTrace_2083876
  have hstable : (prefixWord ++ tailWord_2083876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083876).length < 2 ^ (prefixWord ++ tailWord_2083876).sum := by decide
  have hdescent : baseEnd_2083876 < baseStart_2083876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083896 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 1, 2, 3]
def baseStart_2083896 : Nat := 118140960795 + 2083896 * 2 ^ 59
def prefixEnd_2083896 : Nat := 4983230072969 + 3 ^ 40 * 2083896 * 2
def baseEnd_2083896 : Nat := 1070040281981883981016343

theorem tailTrace_2083896 : CollatzResearch.WordTrace tailWord_2083896 prefixEnd_2083896 1070040281981883981016343 := by
  unfold tailWord_2083896
  simp only [CollatzResearch.WordTrace]
  refine ⟨38002965629204083973587771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50670620838938778631450361 38002965629204083973587771)
  ·
    refine ⟨57004448443806125960381657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38002965629204083973587771 57004448443806125960381657)
    ·
      refine ⟨42753336332854594470286243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57004448443806125960381657 42753336332854594470286243)
      ·
        refine ⟨64130004499281891705429365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42753336332854594470286243 64130004499281891705429365)
        ·
          refine ⟨6012187921807677347384003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64130004499281891705429365 6012187921807677347384003)
          ·
            refine ⟨9018281882711516021076005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012187921807677347384003 9018281882711516021076005)
            ·
              refine ⟨1690927853008409253951751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9018281882711516021076005 1690927853008409253951751)
              ·
                refine ⟨2536391779512613880927627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690927853008409253951751 2536391779512613880927627)
                ·
                  refine ⟨3804587669268920821391441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536391779512613880927627 3804587669268920821391441)
                  ·
                    refine ⟨2853440751951690616043581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804587669268920821391441 2853440751951690616043581)
                    ·
                      refine ⟨1070040281981883981016343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2853440751951690616043581 1070040281981883981016343)
                      ·
                        rfl

theorem cell23_2083896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_2083896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083896 prefixEnd_2083896 := by exact prefixLift 2083896
  have htrace : WordTrace (prefixWord ++ tailWord_2083896) baseStart_2083896 baseEnd_2083896 := by
    simpa [prefixWord, tailWord_2083896, baseEnd_2083896] using wordTrace_append hprefix tailTrace_2083896
  have hstable : (prefixWord ++ tailWord_2083896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083896).length < 2 ^ (prefixWord ++ tailWord_2083896).sum := by decide
  have hdescent : baseEnd_2083896 < baseStart_2083896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083910 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2083910 : Nat := 118140960795 + 2083910 * 2 ^ 59
def prefixEnd_2083910 : Nat := 4983230072969 + 3 ^ 40 * 2083910 * 2
def baseEnd_2083910 : Nat := 1070047470711046926241279

theorem tailTrace_2083910 : CollatzResearch.WordTrace tailWord_2083910 prefixEnd_2083910 1070047470711046926241279 := by
  unfold tailWord_2083910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375201308761170260568287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50670961253571632225456789 2375201308761170260568287)
  ·
    refine ⟨3562801963141755390852431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2375201308761170260568287 3562801963141755390852431)
    ·
      refine ⟨5344202944712633086278647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3562801963141755390852431 5344202944712633086278647)
      ·
        refine ⟨8016304417068949629417971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5344202944712633086278647 8016304417068949629417971)
        ·
          refine ⟨12024456625603424444126957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016304417068949629417971 12024456625603424444126957)
          ·
            refine ⟨4509171234601284166547609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12024456625603424444126957 4509171234601284166547609)
            ·
              refine ⟨3381878425950963124910707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509171234601284166547609 3381878425950963124910707)
              ·
                refine ⟨5072817638926444687366061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381878425950963124910707 5072817638926444687366061)
                ·
                  refine ⟨1902306614597416757762273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5072817638926444687366061 1902306614597416757762273)
                  ·
                    refine ⟨1426729960948062568321705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902306614597416757762273 1426729960948062568321705)
                    ·
                      refine ⟨1070047470711046926241279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426729960948062568321705 1070047470711046926241279)
                      ·
                        rfl

theorem cell23_2083910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2083910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083910 prefixEnd_2083910 := by exact prefixLift 2083910
  have htrace : WordTrace (prefixWord ++ tailWord_2083910) baseStart_2083910 baseEnd_2083910 := by
    simpa [prefixWord, tailWord_2083910, baseEnd_2083910] using wordTrace_append hprefix tailTrace_2083910
  have hstable : (prefixWord ++ tailWord_2083910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083910).length < 2 ^ (prefixWord ++ tailWord_2083910).sum := by decide
  have hdescent : baseEnd_2083910 < baseStart_2083910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083933 : List Nat := [1, 4, 4, 1, 3, 1, 2, 7]
def baseStart_2083933 : Nat := 118140960795 + 2083933 * 2 ^ 59
def prefixEnd_2083933 : Nat := 4983230072969 + 3 ^ 40 * 2083933 * 2
def baseEnd_2083933 : Nat := 39631825213559271713099

theorem tailTrace_2083933 : CollatzResearch.WordTrace tailWord_2083933 prefixEnd_2083933 39631825213559271713099 := by
  unfold tailWord_2083933
  simp only [CollatzResearch.WordTrace]
  refine ⟨76007280759274123266272453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50671520506182748844181635 76007280759274123266272453)
  ·
    refine ⟨14251365142363898112426085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76007280759274123266272453 14251365142363898112426085)
    ·
      refine ⟨2672130964193230896079891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14251365142363898112426085 2672130964193230896079891)
      ·
        refine ⟨4008196446289846344119837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672130964193230896079891 4008196446289846344119837)
        ·
          refine ⟨1503073667358692379044939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4008196446289846344119837 1503073667358692379044939)
          ·
            refine ⟨2254610501038038568567409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503073667358692379044939 2254610501038038568567409)
            ·
              refine ⟨1690957875778528926425557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2254610501038038568567409 1690957875778528926425557)
              ·
                refine ⟨39631825213559271713099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1690957875778528926425557 39631825213559271713099)
                ·
                  rfl

theorem cell23_2083933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 7].length) (baseStart_2083933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083933 prefixEnd_2083933 := by exact prefixLift 2083933
  have htrace : WordTrace (prefixWord ++ tailWord_2083933) baseStart_2083933 baseEnd_2083933 := by
    simpa [prefixWord, tailWord_2083933, baseEnd_2083933] using wordTrace_append hprefix tailTrace_2083933
  have hstable : (prefixWord ++ tailWord_2083933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083933).length < 2 ^ (prefixWord ++ tailWord_2083933).sum := by decide
  have hdescent : baseEnd_2083933 < baseStart_2083933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083936 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 1, 3, 2]
def baseStart_2083936 : Nat := 118140960795 + 2083936 * 2 ^ 59
def prefixEnd_2083936 : Nat := 4983230072969 + 3 ^ 40 * 2083936 * 2
def baseEnd_2083936 : Nat := 1070060821208063824516159

theorem tailTrace_2083936 : CollatzResearch.WordTrace tailWord_2083936 prefixEnd_2083936 1070060821208063824516159 := by
  unfold tailWord_2083936
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003695089131627389315831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50671593452175503185754441 38003695089131627389315831)
  ·
    refine ⟨57005542633697441083973747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38003695089131627389315831 57005542633697441083973747)
    ·
      refine ⟨85508313950546161625960621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57005542633697441083973747 85508313950546161625960621)
      ·
        refine ⟨32065617731454810609735233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85508313950546161625960621 32065617731454810609735233)
        ·
          refine ⟨24049213298591107957301425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32065617731454810609735233 24049213298591107957301425)
          ·
            refine ⟨18036909973943330967976069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24049213298591107957301425 18036909973943330967976069)
            ·
              refine ⟨3381920620114374556495513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18036909973943330967976069 3381920620114374556495513)
              ·
                refine ⟨2536440465085780917371635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381920620114374556495513 2536440465085780917371635)
                ·
                  refine ⟨3804660697628671376057453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536440465085780917371635 3804660697628671376057453)
                  ·
                    refine ⟨1426747761610751766021545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804660697628671376057453 1426747761610751766021545)
                    ·
                      refine ⟨1070060821208063824516159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426747761610751766021545 1070060821208063824516159)
                      ·
                        rfl

theorem cell23_2083936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_2083936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083936 prefixEnd_2083936 := by exact prefixLift 2083936
  have htrace : WordTrace (prefixWord ++ tailWord_2083936) baseStart_2083936 baseEnd_2083936 := by
    simpa [prefixWord, tailWord_2083936, baseEnd_2083936] using wordTrace_append hprefix tailTrace_2083936
  have hstable : (prefixWord ++ tailWord_2083936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083936).length < 2 ^ (prefixWord ++ tailWord_2083936).sum := by decide
  have hdescent : baseEnd_2083936 < baseStart_2083936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083944 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2083944 : Nat := 118140960795 + 2083944 * 2 ^ 59
def prefixEnd_2083944 : Nat := 4983230072969 + 3 ^ 40 * 2083944 * 2
def baseEnd_2083944 : Nat := 1070064929053299793216123

theorem tailTrace_2083944 : CollatzResearch.WordTrace tailWord_2083944 prefixEnd_2083944 1070064929053299793216123 := by
  unfold tailWord_2083944
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003840981117136072461443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50671787974822848096615257 38003840981117136072461443)
  ·
    refine ⟨57005761471675704108692165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38003840981117136072461443 57005761471675704108692165)
    ·
      refine ⟨10688580275939194520379781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57005761471675704108692165 10688580275939194520379781)
      ·
        refine ⟨2004108801738598972571209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10688580275939194520379781 2004108801738598972571209)
        ·
          refine ⟨1503081601303949229428407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004108801738598972571209 1503081601303949229428407)
          ·
            refine ⟨2254622401955923844142611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503081601303949229428407 2254622401955923844142611)
            ·
              refine ⟨3381933602933885766213917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254622401955923844142611 3381933602933885766213917)
              ·
                refine ⟨1268225101100207162330219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381933602933885766213917 1268225101100207162330219)
                ·
                  refine ⟨1902337651650310743495329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268225101100207162330219 1902337651650310743495329)
                  ·
                    refine ⟨1426753238737733057621497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902337651650310743495329 1426753238737733057621497)
                    ·
                      refine ⟨1070064929053299793216123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426753238737733057621497 1070064929053299793216123)
                      ·
                        rfl

theorem cell23_2083944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2083944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083944 prefixEnd_2083944 := by exact prefixLift 2083944
  have htrace : WordTrace (prefixWord ++ tailWord_2083944) baseStart_2083944 baseEnd_2083944 := by
    simpa [prefixWord, tailWord_2083944, baseEnd_2083944] using wordTrace_append hprefix tailTrace_2083944
  have hstable : (prefixWord ++ tailWord_2083944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083944).length < 2 ^ (prefixWord ++ tailWord_2083944).sum := by decide
  have hdescent : baseEnd_2083944 < baseStart_2083944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083952 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_2083952 : Nat := 118140960795 + 2083952 * 2 ^ 59
def prefixEnd_2083952 : Nat := 4983230072969 + 3 ^ 40 * 2083952 * 2
def baseEnd_2083952 : Nat := 1070069036898535761916085

theorem tailTrace_2083952 : CollatzResearch.WordTrace tailWord_2083952 prefixEnd_2083952 1070069036898535761916085 := by
  unfold tailWord_2083952
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003986873102644755607055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50671982497470193007476073 38003986873102644755607055)
  ·
    refine ⟨57005980309653967133410583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38003986873102644755607055 57005980309653967133410583)
    ·
      refine ⟨85508970464480950700115875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57005980309653967133410583 85508970464480950700115875)
      ·
        refine ⟨128263455696721426050173813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85508970464480950700115875 128263455696721426050173813)
        ·
          refine ⟨12024698971567633692203795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128263455696721426050173813 12024698971567633692203795)
          ·
            refine ⟨18037048457351450538305693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024698971567633692203795 18037048457351450538305693)
            ·
              refine ⟨6763893171506793951864635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18037048457351450538305693 6763893171506793951864635)
              ·
                refine ⟨10145839757260190927796953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763893171506793951864635 10145839757260190927796953)
                ·
                  refine ⟨7609379817945143195847715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10145839757260190927796953 7609379817945143195847715)
                  ·
                    refine ⟨11414069726917714793771573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7609379817945143195847715 11414069726917714793771573)
                    ·
                      refine ⟨1070069036898535761916085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11414069726917714793771573 1070069036898535761916085)
                      ·
                        rfl

theorem cell23_2083952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_2083952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2083952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2083952 prefixEnd_2083952 := by exact prefixLift 2083952
  have htrace : WordTrace (prefixWord ++ tailWord_2083952) baseStart_2083952 baseEnd_2083952 := by
    simpa [prefixWord, tailWord_2083952, baseEnd_2083952] using wordTrace_append hprefix tailTrace_2083952
  have hstable : (prefixWord ++ tailWord_2083952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083952).length < 2 ^ (prefixWord ++ tailWord_2083952).sum := by decide
  have hdescent : baseEnd_2083952 < baseStart_2083952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084079 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 8]
def baseStart_2084079 : Nat := 118140960795 + 2084079 * 2 ^ 59
def prefixEnd_2084079 : Nat := 4983230072969 + 3 ^ 40 * 2084079 * 2
def baseEnd_2084079 : Nat := 118903805437961862780889

theorem tailTrace_2084079 : CollatzResearch.WordTrace tailWord_2084079 prefixEnd_2084079 118903805437961862780889 := by
  unfold tailWord_2084079
  simp only [CollatzResearch.WordTrace]
  refine ⟨76012605816745190201087291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50675070544496793467391527 76012605816745190201087291)
  ·
    refine ⟨114018908725117785301630937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76012605816745190201087291 114018908725117785301630937)
    ·
      refine ⟨85514181543838338976223203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114018908725117785301630937 85514181543838338976223203)
      ·
        refine ⟨128271272315757508464334805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85514181543838338976223203 128271272315757508464334805)
        ·
          refine ⟨3006357944900566604632847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 128271272315757508464334805 3006357944900566604632847)
          ·
            refine ⟨4509536917350849906949271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006357944900566604632847 4509536917350849906949271)
            ·
              refine ⟨6764305376026274860423907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509536917350849906949271 6764305376026274860423907)
              ·
                refine ⟨10146458064039412290635861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764305376026274860423907 10146458064039412290635861)
                ·
                  refine ⟨118903805437961862780889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10146458064039412290635861 118903805437961862780889)
                  ·
                    rfl

theorem cell23_2084079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 8].length) (baseStart_2084079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084079 prefixEnd_2084079 := by exact prefixLift 2084079
  have htrace : WordTrace (prefixWord ++ tailWord_2084079) baseStart_2084079 baseEnd_2084079 := by
    simpa [prefixWord, tailWord_2084079, baseEnd_2084079] using wordTrace_append hprefix tailTrace_2084079
  have hstable : (prefixWord ++ tailWord_2084079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084079).length < 2 ^ (prefixWord ++ tailWord_2084079).sum := by decide
  have hdescent : baseEnd_2084079 < baseStart_2084079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084129 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2084129 : Nat := 118140960795 + 2084129 * 2 ^ 59
def prefixEnd_2084129 : Nat := 4983230072969 + 3 ^ 40 * 2084129 * 2
def baseEnd_2084129 : Nat := 1070159922974381569402771

theorem tailTrace_2084129 : CollatzResearch.WordTrace tailWord_2084129 prefixEnd_2084129 1070159922974381569402771 := by
  unfold tailWord_2084129
  simp only [CollatzResearch.WordTrace]
  refine ⟨76014429466564048740407441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50676286311042699160271627 76014429466564048740407441)
  ·
    refine ⟨57010822099923036555305581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76014429466564048740407441 57010822099923036555305581)
    ·
      refine ⟨21379058287471138708239593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57010822099923036555305581 21379058287471138708239593)
      ·
        refine ⟨16034293715603354031179695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21379058287471138708239593 16034293715603354031179695)
        ·
          refine ⟨24051440573405031046769543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16034293715603354031179695 24051440573405031046769543)
          ·
            refine ⟨36077160860107546570154315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24051440573405031046769543 36077160860107546570154315)
            ·
              refine ⟨54115741290161319855231473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36077160860107546570154315 54115741290161319855231473)
              ·
                refine ⟨40586805967620989891423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54115741290161319855231473 40586805967620989891423605)
                ·
                  refine ⟨3805013059464467802320963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40586805967620989891423605 3805013059464467802320963)
                  ·
                    refine ⟨5707519589196701703481445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805013059464467802320963 5707519589196701703481445)
                    ·
                      refine ⟨1070159922974381569402771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5707519589196701703481445 1070159922974381569402771)
                      ·
                        rfl

theorem cell23_2084129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2084129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084129 prefixEnd_2084129 := by exact prefixLift 2084129
  have htrace : WordTrace (prefixWord ++ tailWord_2084129) baseStart_2084129 baseEnd_2084129 := by
    simpa [prefixWord, tailWord_2084129, baseEnd_2084129] using wordTrace_append hprefix tailTrace_2084129
  have hstable : (prefixWord ++ tailWord_2084129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084129).length < 2 ^ (prefixWord ++ tailWord_2084129).sum := by decide
  have hdescent : baseEnd_2084129 < baseStart_2084129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084133 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 2, 3, 2]
def baseStart_2084133 : Nat := 118140960795 + 2084133 * 2 ^ 59
def prefixEnd_2084133 : Nat := 4983230072969 + 3 ^ 40 * 2084133 * 2
def baseEnd_2084133 : Nat := 1070161976896999553752753

theorem tailTrace_2084133 : CollatzResearch.WordTrace tailWord_2084133 prefixEnd_2084133 1070161976896999553752753 := by
  unfold tailWord_2084133
  simp only [CollatzResearch.WordTrace]
  refine ⟨76014575358549557423553053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50676383572366371615702035 76014575358549557423553053)
  ·
    refine ⟨28505465759456084033832395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76014575358549557423553053 28505465759456084033832395)
    ·
      refine ⟨42758198639184126050748593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28505465759456084033832395 42758198639184126050748593)
      ·
        refine ⟨32068648979388094538061445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42758198639184126050748593 32068648979388094538061445)
        ·
          refine ⟨6012871683635267725886521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32068648979388094538061445 6012871683635267725886521)
          ·
            refine ⟨4509653762726450794414891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012871683635267725886521 4509653762726450794414891)
            ·
              refine ⟨6764480644089676191622337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509653762726450794414891 6764480644089676191622337)
              ·
                refine ⟨5073360483067257143716753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6764480644089676191622337 5073360483067257143716753)
                ·
                  refine ⟨3805020362300442857787565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5073360483067257143716753 3805020362300442857787565)
                  ·
                    refine ⟨1426882635862666071670337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805020362300442857787565 1426882635862666071670337)
                    ·
                      refine ⟨1070161976896999553752753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1426882635862666071670337 1070161976896999553752753)
                      ·
                        rfl

theorem cell23_2084133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_2084133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084133 prefixEnd_2084133 := by exact prefixLift 2084133
  have htrace : WordTrace (prefixWord ++ tailWord_2084133) baseStart_2084133 baseEnd_2084133 := by
    simpa [prefixWord, tailWord_2084133, baseEnd_2084133] using wordTrace_append hprefix tailTrace_2084133
  have hstable : (prefixWord ++ tailWord_2084133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084133).length < 2 ^ (prefixWord ++ tailWord_2084133).sum := by decide
  have hdescent : baseEnd_2084133 < baseStart_2084133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084159 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_2084159 : Nat := 118140960795 + 2084159 * 2 ^ 59
def prefixEnd_2084159 : Nat := 4983230072969 + 3 ^ 40 * 2084159 * 2
def baseEnd_2084159 : Nat := 1070175327394016452027633

theorem tailTrace_2084159 : CollatzResearch.WordTrace tailWord_2084159 prefixEnd_2084159 1070175327394016452027633 := by
  unfold tailWord_2084159
  simp only [CollatzResearch.WordTrace]
  refine ⟨76015523656455363863999531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50677015770970242575999687 76015523656455363863999531)
  ·
    refine ⟨114023285484683045795999297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76015523656455363863999531 114023285484683045795999297)
    ·
      refine ⟨85517464113512284346999473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114023285484683045795999297 85517464113512284346999473)
      ·
        refine ⟨64138098085134213260249605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85517464113512284346999473 64138098085134213260249605)
        ·
          refine ⟨12025893390962664986296801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64138098085134213260249605 12025893390962664986296801)
          ·
            refine ⟨9019420043221998739722601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12025893390962664986296801 9019420043221998739722601)
            ·
              refine ⟨6764565032416499054791951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9019420043221998739722601 6764565032416499054791951)
              ·
                refine ⟨10146847548624748582187927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764565032416499054791951 10146847548624748582187927)
                ·
                  refine ⟨15220271322937122873281891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146847548624748582187927 15220271322937122873281891)
                  ·
                    refine ⟨22830406984405684309922837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15220271322937122873281891 22830406984405684309922837)
                    ·
                      refine ⟨1070175327394016452027633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22830406984405684309922837 1070175327394016452027633)
                      ·
                        rfl

theorem cell23_2084159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_2084159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084159 prefixEnd_2084159 := by exact prefixLift 2084159
  have htrace : WordTrace (prefixWord ++ tailWord_2084159) baseStart_2084159 baseEnd_2084159 := by
    simpa [prefixWord, tailWord_2084159, baseEnd_2084159] using wordTrace_append hprefix tailTrace_2084159
  have hstable : (prefixWord ++ tailWord_2084159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084159).length < 2 ^ (prefixWord ++ tailWord_2084159).sum := by decide
  have hdescent : baseEnd_2084159 < baseStart_2084159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084219 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4]
def baseStart_2084219 : Nat := 118140960795 + 2084219 * 2 ^ 59
def prefixEnd_2084219 : Nat := 4983230072969 + 3 ^ 40 * 2084219 * 2
def baseEnd_2084219 : Nat := 1070206136233286217277357

theorem tailTrace_2084219 : CollatzResearch.WordTrace tailWord_2084219 prefixEnd_2084219 1070206136233286217277357 := by
  unfold tailWord_2084219
  simp only [CollatzResearch.WordTrace]
  refine ⟨76017712036237994111183711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50678474690825329407455807 76017712036237994111183711)
  ·
    refine ⟨114026568054356991166775567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76017712036237994111183711 114026568054356991166775567)
    ·
      refine ⟨171039852081535486750163351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114026568054356991166775567 171039852081535486750163351)
      ·
        refine ⟨256559778122303230125245027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171039852081535486750163351 256559778122303230125245027)
        ·
          refine ⟨384839667183454845187867541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256559778122303230125245027 384839667183454845187867541)
          ·
            refine ⟨18039359399224445868181291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 384839667183454845187867541 18039359399224445868181291)
            ·
              refine ⟨27059039098836668802271937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18039359399224445868181291 27059039098836668802271937)
              ·
                refine ⟨20294279324127501601703953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27059039098836668802271937 20294279324127501601703953)
                ·
                  refine ⟨15220709493095626201277965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20294279324127501601703953 15220709493095626201277965)
                  ·
                    refine ⟨5707766059910859825479237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15220709493095626201277965 5707766059910859825479237)
                    ·
                      refine ⟨1070206136233286217277357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5707766059910859825479237 1070206136233286217277357)
                      ·
                        rfl

theorem cell23_2084219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_2084219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084219 prefixEnd_2084219 := by exact prefixLift 2084219
  have htrace : WordTrace (prefixWord ++ tailWord_2084219) baseStart_2084219 baseEnd_2084219 := by
    simpa [prefixWord, tailWord_2084219, baseEnd_2084219] using wordTrace_append hprefix tailTrace_2084219
  have hstable : (prefixWord ++ tailWord_2084219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084219).length < 2 ^ (prefixWord ++ tailWord_2084219).sum := by decide
  have hdescent : baseEnd_2084219 < baseStart_2084219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084264 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2084264 : Nat := 118140960795 + 2084264 * 2 ^ 59
def prefixEnd_2084264 : Nat := 4983230072969 + 3 ^ 40 * 2084264 * 2
def baseEnd_2084264 : Nat := 1070229242862738541214651

theorem tailTrace_2084264 : CollatzResearch.WordTrace tailWord_2084264 prefixEnd_2084264 1070229242862738541214651 := by
  unfold tailWord_2084264
  simp only [CollatzResearch.WordTrace]
  refine ⟨38009676660537483398285923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50679568880716644531047897 38009676660537483398285923)
  ·
    refine ⟨57014514990806225097428885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38009676660537483398285923 57014514990806225097428885)
    ·
      refine ⟨2672555390194041801441979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57014514990806225097428885 2672555390194041801441979)
      ·
        refine ⟨4008833085291062702162969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672555390194041801441979 4008833085291062702162969)
        ·
          refine ⟨3006624813968297026622227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008833085291062702162969 3006624813968297026622227)
          ·
            refine ⟨4509937220952445539933341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006624813968297026622227 4509937220952445539933341)
            ·
              refine ⟨1691226457857167077475003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4509937220952445539933341 1691226457857167077475003)
              ·
                refine ⟨2536839686785750616212505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691226457857167077475003 2536839686785750616212505)
                ·
                  refine ⟨1902629765089312962159379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2536839686785750616212505 1902629765089312962159379)
                  ·
                    refine ⟨2853944647633969443239069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1902629765089312962159379 2853944647633969443239069)
                    ·
                      refine ⟨1070229242862738541214651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2853944647633969443239069 1070229242862738541214651)
                      ·
                        rfl

theorem cell23_2084264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2084264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084264 prefixEnd_2084264 := by exact prefixLift 2084264
  have htrace : WordTrace (prefixWord ++ tailWord_2084264) baseStart_2084264 baseEnd_2084264 := by
    simpa [prefixWord, tailWord_2084264, baseEnd_2084264] using wordTrace_append hprefix tailTrace_2084264
  have hstable : (prefixWord ++ tailWord_2084264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084264).length < 2 ^ (prefixWord ++ tailWord_2084264).sum := by decide
  have hdescent : baseEnd_2084264 < baseStart_2084264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084310 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2084310 : Nat := 118140960795 + 2084310 * 2 ^ 59
def prefixEnd_2084310 : Nat := 4983230072969 + 3 ^ 40 * 2084310 * 2
def baseEnd_2084310 : Nat := 118916984774760595693271

theorem tailTrace_2084310 : CollatzResearch.WordTrace tailWord_2084310 prefixEnd_2084310 118916984774760595693271 := by
  unfold tailWord_2084310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751314442431769790796649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50680687385938877768497589 4751314442431769790796649)
  ·
    refine ⟨3563485831823827343097487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4751314442431769790796649 3563485831823827343097487)
    ·
      refine ⟨5345228747735741014646231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563485831823827343097487 5345228747735741014646231)
      ·
        refine ⟨8017843121603611521969347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345228747735741014646231 8017843121603611521969347)
        ·
          refine ⟨12026764682405417282954021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8017843121603611521969347 12026764682405417282954021)
          ·
            refine ⟨2255018377951015740553879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12026764682405417282954021 2255018377951015740553879)
            ·
              refine ⟨3382527566926523610830819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255018377951015740553879 3382527566926523610830819)
              ·
                refine ⟨5073791350389785416246229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382527566926523610830819 5073791350389785416246229)
                ·
                  refine ⟨118916984774760595693271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5073791350389785416246229 118916984774760595693271)
                  ·
                    rfl

theorem cell23_2084310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2084310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084310 prefixEnd_2084310 := by exact prefixLift 2084310
  have htrace : WordTrace (prefixWord ++ tailWord_2084310) baseStart_2084310 baseEnd_2084310 := by
    simpa [prefixWord, tailWord_2084310, baseEnd_2084310] using wordTrace_append hprefix tailTrace_2084310
  have hstable : (prefixWord ++ tailWord_2084310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084310).length < 2 ^ (prefixWord ++ tailWord_2084310).sum := by decide
  have hdescent : baseEnd_2084310 < baseStart_2084310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084329 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_2084329 : Nat := 118140960795 + 2084329 * 2 ^ 59
def prefixEnd_2084329 : Nat := 4983230072969 + 3 ^ 40 * 2084329 * 2
def baseEnd_2084329 : Nat := 1070262619105280786901851

theorem tailTrace_2084329 : CollatzResearch.WordTrace tailWord_2084329 prefixEnd_2084329 1070262619105280786901851 := by
  unfold tailWord_2084329
  simp only [CollatzResearch.WordTrace]
  refine ⟨76021724065839482897688041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50681149377226321931792027 76021724065839482897688041)
  ·
    refine ⟨57016293049379612173266031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76021724065839482897688041 57016293049379612173266031)
    ·
      refine ⟨85524439574069418259899047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57016293049379612173266031 85524439574069418259899047)
      ·
        refine ⟨128286659361104127389848571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85524439574069418259899047 128286659361104127389848571)
        ·
          refine ⟨192429989041656191084772857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128286659361104127389848571 192429989041656191084772857)
          ·
            refine ⟨144322491781242143313579643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192429989041656191084772857 144322491781242143313579643)
            ·
              refine ⟨216483737671863214970369465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144322491781242143313579643 216483737671863214970369465)
              ·
                refine ⟨162362803253897411227777099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216483737671863214970369465 162362803253897411227777099)
                ·
                  refine ⟨243544204880846116841665649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162362803253897411227777099 243544204880846116841665649)
                  ·
                    refine ⟨182658153660634587631249237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243544204880846116841665649 182658153660634587631249237)
                    ·
                      refine ⟨1070262619105280786901851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 182658153660634587631249237 1070262619105280786901851)
                      ·
                        rfl

theorem cell23_2084329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_2084329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084329 prefixEnd_2084329 := by exact prefixLift 2084329
  have htrace : WordTrace (prefixWord ++ tailWord_2084329) baseStart_2084329 baseEnd_2084329 := by
    simpa [prefixWord, tailWord_2084329, baseEnd_2084329] using wordTrace_append hprefix tailTrace_2084329
  have hstable : (prefixWord ++ tailWord_2084329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084329).length < 2 ^ (prefixWord ++ tailWord_2084329).sum := by decide
  have hdescent : baseEnd_2084329 < baseStart_2084329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084461 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2084461 : Nat := 118140960795 + 2084461 * 2 ^ 59
def prefixEnd_2084461 : Nat := 4983230072969 + 3 ^ 40 * 2084461 * 2
def baseEnd_2084461 : Nat := 1070330398551674270451245

theorem tailTrace_2084461 : CollatzResearch.WordTrace tailWord_2084461 prefixEnd_2084461 1070330398551674270451245 := by
  unfold tailWord_2084461
  simp only [CollatzResearch.WordTrace]
  refine ⟨76026538501361269441493237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50684359000907512960995491 76026538501361269441493237)
  ·
    refine ⟨7127487984502619010139991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76026538501361269441493237 7127487984502619010139991)
    ·
      refine ⟨10691231976753928515209987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7127487984502619010139991 10691231976753928515209987)
      ·
        refine ⟨16036847965130892772814981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691231976753928515209987 16036847965130892772814981)
        ·
          refine ⟨3006908993462042394902809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16036847965130892772814981 3006908993462042394902809)
          ·
            refine ⟨2255181745096531796177107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3006908993462042394902809 2255181745096531796177107)
            ·
              refine ⟨3382772617644797694265661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255181745096531796177107 3382772617644797694265661)
              ·
                refine ⟨1268539731616799135349623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382772617644797694265661 1268539731616799135349623)
                ·
                  refine ⟨1902809597425198703024435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268539731616799135349623 1902809597425198703024435)
                  ·
                    refine ⟨2854214396137798054536653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1902809597425198703024435 2854214396137798054536653)
                    ·
                      refine ⟨1070330398551674270451245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2854214396137798054536653 1070330398551674270451245)
                      ·
                        rfl

theorem cell23_2084461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2084461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084461 prefixEnd_2084461 := by exact prefixLift 2084461
  have htrace : WordTrace (prefixWord ++ tailWord_2084461) baseStart_2084461 baseEnd_2084461 := by
    simpa [prefixWord, tailWord_2084461, baseEnd_2084461] using wordTrace_append hprefix tailTrace_2084461
  have hstable : (prefixWord ++ tailWord_2084461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084461).length < 2 ^ (prefixWord ++ tailWord_2084461).sum := by decide
  have hdescent : baseEnd_2084461 < baseStart_2084461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084470 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2084470 : Nat := 118140960795 + 2084470 * 2 ^ 59
def prefixEnd_2084470 : Nat := 4983230072969 + 3 ^ 40 * 2084470 * 2
def baseEnd_2084470 : Nat := 1070335019877564735238703

theorem tailTrace_2084470 : CollatzResearch.WordTrace tailWord_2084470 prefixEnd_2084470 1070335019877564735238703 := by
  unfold tailWord_2084470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751679172395541498660679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50684577838885775985713909 4751679172395541498660679)
  ·
    refine ⟨7127518758593312247991019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751679172395541498660679 7127518758593312247991019)
    ·
      refine ⟨10691278137889968371986529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7127518758593312247991019 10691278137889968371986529)
      ·
        refine ⟨8018458603417476278989897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10691278137889968371986529 8018458603417476278989897)
        ·
          refine ⟨6013843952563107209242423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8018458603417476278989897 6013843952563107209242423)
          ·
            refine ⟨9020765928844660813863635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013843952563107209242423 9020765928844660813863635)
            ·
              refine ⟨13531148893266991220795453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9020765928844660813863635 13531148893266991220795453)
              ·
                refine ⟨5074180834975121707798295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13531148893266991220795453 5074180834975121707798295)
                ·
                  refine ⟨7611271252462682561697443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074180834975121707798295 7611271252462682561697443)
                  ·
                    refine ⟨11416906878694023842546165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7611271252462682561697443 11416906878694023842546165)
                    ·
                      refine ⟨1070335019877564735238703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11416906878694023842546165 1070335019877564735238703)
                      ·
                        rfl

theorem cell23_2084470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2084470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084470 prefixEnd_2084470 := by exact prefixLift 2084470
  have htrace : WordTrace (prefixWord ++ tailWord_2084470) baseStart_2084470 baseEnd_2084470 := by
    simpa [prefixWord, tailWord_2084470, baseEnd_2084470] using wordTrace_append hprefix tailTrace_2084470
  have hstable : (prefixWord ++ tailWord_2084470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084470).length < 2 ^ (prefixWord ++ tailWord_2084470).sum := by decide
  have hdescent : baseEnd_2084470 < baseStart_2084470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084494 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_2084494 : Nat := 118140960795 + 2084494 * 2 ^ 59
def prefixEnd_2084494 : Nat := 4983230072969 + 3 ^ 40 * 2084494 * 2
def baseEnd_2084494 : Nat := 356782447804424213779531

theorem tailTrace_2084494 : CollatzResearch.WordTrace tailWord_2084494 prefixEnd_2084494 356782447804424213779531 := by
  unfold tailWord_2084494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9503467763780214509680567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50685161406827810718296357 9503467763780214509680567)
  ·
    refine ⟨14255201645670321764520851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9503467763780214509680567 14255201645670321764520851)
    ·
      refine ⟨21382802468505482646781277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255201645670321764520851 21382802468505482646781277)
      ·
        refine ⟨8018550925689555992542979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21382802468505482646781277 8018550925689555992542979)
        ·
          refine ⟨12027826388534333988814469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018550925689555992542979 12027826388534333988814469)
          ·
            refine ⟨2255217447850187622902713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12027826388534333988814469 2255217447850187622902713)
            ·
              refine ⟨1691413085887640717177035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255217447850187622902713 1691413085887640717177035)
              ·
                refine ⟨2537119628831461075765553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691413085887640717177035 2537119628831461075765553)
                ·
                  refine ⟨1902839721623595806824165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537119628831461075765553 1902839721623595806824165)
                  ·
                    refine ⟨356782447804424213779531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1902839721623595806824165 356782447804424213779531)
                    ·
                      rfl

theorem cell23_2084494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_2084494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084494 prefixEnd_2084494 := by exact prefixLift 2084494
  have htrace : WordTrace (prefixWord ++ tailWord_2084494) baseStart_2084494 baseEnd_2084494 := by
    simpa [prefixWord, tailWord_2084494, baseEnd_2084494] using wordTrace_append hprefix tailTrace_2084494
  have hstable : (prefixWord ++ tailWord_2084494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084494).length < 2 ^ (prefixWord ++ tailWord_2084494).sum := by decide
  have hdescent : baseEnd_2084494 < baseStart_2084494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084543 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_2084543 : Nat := 118140960795 + 2084543 * 2 ^ 59
def prefixEnd_2084543 : Nat := 4983230072969 + 3 ^ 40 * 2084543 * 2
def baseEnd_2084543 : Nat := 1070372503965342949625867

theorem tailTrace_2084543 : CollatzResearch.WordTrace tailWord_2084543 prefixEnd_2084543 1070372503965342949625867 := by
  unfold tailWord_2084543
  simp only [CollatzResearch.WordTrace]
  refine ⟨76029529287064197445978283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50686352858042798297318855 76029529287064197445978283)
  ·
    refine ⟨114044293930596296168967425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76029529287064197445978283 114044293930596296168967425)
    ·
      refine ⟨85533220447947222126725569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114044293930596296168967425 85533220447947222126725569)
      ·
        refine ⟨64149915335960416595044177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85533220447947222126725569 64149915335960416595044177)
        ·
          refine ⟨48112436501970312446283133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64149915335960416595044177 48112436501970312446283133)
          ·
            refine ⟨18042163688238867167356175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48112436501970312446283133 18042163688238867167356175)
            ·
              refine ⟨27063245532358300751034263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042163688238867167356175 27063245532358300751034263)
              ·
                refine ⟨40594868298537451126551395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27063245532358300751034263 40594868298537451126551395)
                ·
                  refine ⟨60892302447806176689827093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40594868298537451126551395 60892302447806176689827093)
                  ·
                    refine ⟨2854326677240914532335645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60892302447806176689827093 2854326677240914532335645)
                    ·
                      refine ⟨1070372503965342949625867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2854326677240914532335645 1070372503965342949625867)
                      ·
                        rfl

theorem cell23_2084543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_2084543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084543 prefixEnd_2084543 := by exact prefixLift 2084543
  have htrace : WordTrace (prefixWord ++ tailWord_2084543) baseStart_2084543 baseEnd_2084543 := by
    simpa [prefixWord, tailWord_2084543, baseEnd_2084543] using wordTrace_append hprefix tailTrace_2084543
  have hstable : (prefixWord ++ tailWord_2084543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084543).length < 2 ^ (prefixWord ++ tailWord_2084543).sum := by decide
  have hdescent : baseEnd_2084543 < baseStart_2084543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084590 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2084590 : Nat := 118140960795 + 2084590 * 2 ^ 59
def prefixEnd_2084590 : Nat := 4983230072969 + 3 ^ 40 * 2084590 * 2
def baseEnd_2084590 : Nat := 1070396637556104265738151

theorem tailTrace_2084590 : CollatzResearch.WordTrace tailWord_2084590 prefixEnd_2084590 1070396637556104265738151 := by
  unfold tailWord_2084590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9503905439736740559117403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50687495678595949648626149 9503905439736740559117403)
  ·
    refine ⟨14255858159605110838676105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9503905439736740559117403 14255858159605110838676105)
    ·
      refine ⟨10691893619703833129007079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14255858159605110838676105 10691893619703833129007079)
      ·
        refine ⟨16037840429555749693510619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691893619703833129007079 16037840429555749693510619)
        ·
          refine ⟨24056760644333624540265929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037840429555749693510619 24056760644333624540265929)
          ·
            refine ⟨18042570483250218405199447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24056760644333624540265929 18042570483250218405199447)
            ·
              refine ⟨27063855724875327607799171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042570483250218405199447 27063855724875327607799171)
              ·
                refine ⟨40595783587312991411698757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27063855724875327607799171 40595783587312991411698757)
                ·
                  refine ⟨7611709422621185889693517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40595783587312991411698757 7611709422621185889693517)
                  ·
                    refine ⟨2854391033482944708635069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7611709422621185889693517 2854391033482944708635069)
                    ·
                      refine ⟨1070396637556104265738151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2854391033482944708635069 1070396637556104265738151)
                      ·
                        rfl

theorem cell23_2084590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2084590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084590 prefixEnd_2084590 := by exact prefixLift 2084590
  have htrace : WordTrace (prefixWord ++ tailWord_2084590) baseStart_2084590 baseEnd_2084590 := by
    simpa [prefixWord, tailWord_2084590, baseEnd_2084590] using wordTrace_append hprefix tailTrace_2084590
  have hstable : (prefixWord ++ tailWord_2084590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084590).length < 2 ^ (prefixWord ++ tailWord_2084590).sum := by decide
  have hdescent : baseEnd_2084590 < baseStart_2084590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084600 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 2, 5, 2]
def baseStart_2084600 : Nat := 118140960795 + 2084600 * 2 ^ 59
def prefixEnd_2084600 : Nat := 4983230072969 + 3 ^ 40 * 2084600 * 2
def baseEnd_2084600 : Nat := 1070401772362649226613105

theorem tailTrace_2084600 : CollatzResearch.WordTrace tailWord_2084600 prefixEnd_2084600 1070401772362649226613105 := by
  unfold tailWord_2084600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38015804123928848090401627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50687738831905130787202169 38015804123928848090401627)
  ·
    refine ⟨57023706185893272135602441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38015804123928848090401627 57023706185893272135602441)
    ·
      refine ⟨42767779639419954101701831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57023706185893272135602441 42767779639419954101701831)
      ·
        refine ⟨64151669459129931152552747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42767779639419954101701831 64151669459129931152552747)
        ·
          refine ⟨96227504188694896728829121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64151669459129931152552747 96227504188694896728829121)
          ·
            refine ⟨72170628141521172546621841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96227504188694896728829121 72170628141521172546621841)
            ·
              refine ⟨54127971106140879409966381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72170628141521172546621841 54127971106140879409966381)
              ·
                refine ⟨20297989164802829778737393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54127971106140879409966381 20297989164802829778737393)
                ·
                  refine ⟨15223491873602122334053045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20297989164802829778737393 15223491873602122334053045)
                  ·
                    refine ⟨1427202363150198968817473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15223491873602122334053045 1427202363150198968817473)
                    ·
                      refine ⟨1070401772362649226613105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427202363150198968817473 1070401772362649226613105)
                      ·
                        rfl

theorem cell23_2084600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_2084600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084600 prefixEnd_2084600 := by exact prefixLift 2084600
  have htrace : WordTrace (prefixWord ++ tailWord_2084600) baseStart_2084600 baseEnd_2084600 := by
    simpa [prefixWord, tailWord_2084600, baseEnd_2084600] using wordTrace_append hprefix tailTrace_2084600
  have hstable : (prefixWord ++ tailWord_2084600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084600).length < 2 ^ (prefixWord ++ tailWord_2084600).sum := by decide
  have hdescent : baseEnd_2084600 < baseStart_2084600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084610 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2084610 : Nat := 118140960795 + 2084610 * 2 ^ 59
def prefixEnd_2084610 : Nat := 4983230072969 + 3 ^ 40 * 2084610 * 2
def baseEnd_2084610 : Nat := 356802302389731395829353

theorem tailTrace_2084610 : CollatzResearch.WordTrace tailWord_2084610 prefixEnd_2084610 356802302389731395829353 := by
  unfold tailWord_2084610
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007993244455366972166821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50687981985214311925778189 19007993244455366972166821)
  ·
    refine ⟨3563998733335381307281279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19007993244455366972166821 3563998733335381307281279)
    ·
      refine ⟨5345998100003071960921919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563998733335381307281279 5345998100003071960921919)
      ·
        refine ⟨8018997150004607941382879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345998100003071960921919 8018997150004607941382879)
        ·
          refine ⟨12028495725006911912074319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018997150004607941382879 12028495725006911912074319)
          ·
            refine ⟨18042743587510367868111479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028495725006911912074319 18042743587510367868111479)
            ·
              refine ⟨27064115381265551802167219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042743587510367868111479 27064115381265551802167219)
              ·
                refine ⟨40596173071898327703250829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27064115381265551802167219 40596173071898327703250829)
                ·
                  refine ⟨15223564901961872888719061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40596173071898327703250829 15223564901961872888719061)
                  ·
                    refine ⟨356802302389731395829353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15223564901961872888719061 356802302389731395829353)
                    ·
                      rfl

theorem cell23_2084610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2084610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084610 prefixEnd_2084610 := by exact prefixLift 2084610
  have htrace : WordTrace (prefixWord ++ tailWord_2084610) baseStart_2084610 baseEnd_2084610 := by
    simpa [prefixWord, tailWord_2084610, baseEnd_2084610] using wordTrace_append hprefix tailTrace_2084610
  have hstable : (prefixWord ++ tailWord_2084610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084610).length < 2 ^ (prefixWord ++ tailWord_2084610).sum := by decide
  have hdescent : baseEnd_2084610 < baseStart_2084610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084643 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2084643 : Nat := 118140960795 + 2084643 * 2 ^ 59
def prefixEnd_2084643 : Nat := 4983230072969 + 3 ^ 40 * 2084643 * 2
def baseEnd_2084643 : Nat := 1070423852030792558375407

theorem tailTrace_2084643 : CollatzResearch.WordTrace tailWord_2084643 prefixEnd_2084643 1070423852030792558375407 := by
  unfold tailWord_2084643
  simp only [CollatzResearch.WordTrace]
  refine ⟨76033176586701914524618583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50688784391134609683079055 76033176586701914524618583)
  ·
    refine ⟨114049764880052871786927875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76033176586701914524618583 114049764880052871786927875)
    ·
      refine ⟨171074647320079307680391813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114049764880052871786927875 171074647320079307680391813)
      ·
        refine ⟨32076496372514870190073465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171074647320079307680391813 32076496372514870190073465)
        ·
          refine ⟨24057372279386152642555099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32076496372514870190073465 24057372279386152642555099)
          ·
            refine ⟨36086058419079228963832649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24057372279386152642555099 36086058419079228963832649)
            ·
              refine ⟨27064543814309421722874487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36086058419079228963832649 27064543814309421722874487)
              ·
                refine ⟨40596815721464132584311731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27064543814309421722874487 40596815721464132584311731)
                ·
                  refine ⟨60895223582196198876467597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40596815721464132584311731 60895223582196198876467597)
                  ·
                    refine ⟨22835708843323574578675349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60895223582196198876467597 22835708843323574578675349)
                    ·
                      refine ⟨1070423852030792558375407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22835708843323574578675349 1070423852030792558375407)
                      ·
                        rfl

theorem cell23_2084643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2084643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084643 prefixEnd_2084643 := by exact prefixLift 2084643
  have htrace : WordTrace (prefixWord ++ tailWord_2084643) baseStart_2084643 baseEnd_2084643 := by
    simpa [prefixWord, tailWord_2084643, baseEnd_2084643] using wordTrace_append hprefix tailTrace_2084643
  have hstable : (prefixWord ++ tailWord_2084643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084643).length < 2 ^ (prefixWord ++ tailWord_2084643).sum := by decide
  have hdescent : baseEnd_2084643 < baseStart_2084643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084657 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 3, 4]
def baseStart_2084657 : Nat := 118140960795 + 2084657 * 2 ^ 59
def prefixEnd_2084657 : Nat := 4983230072969 + 3 ^ 40 * 2084657 * 2
def baseEnd_2084657 : Nat := 356810346919985167866781

theorem tailTrace_2084657 : CollatzResearch.WordTrace tailWord_2084657 prefixEnd_2084657 356810346919985167866781 := by
  unfold tailWord_2084657
  simp only [CollatzResearch.WordTrace]
  refine ⟨76033687208651194915628225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50689124805767463277085483 76033687208651194915628225)
  ·
    refine ⟨57025265406488396186721169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76033687208651194915628225 57025265406488396186721169)
    ·
      refine ⟨42768949054866297140040877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57025265406488396186721169 42768949054866297140040877)
      ·
        refine ⟨16038355895574861427515329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42768949054866297140040877 16038355895574861427515329)
        ·
          refine ⟨12028766921681146070636497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16038355895574861427515329 12028766921681146070636497)
          ·
            refine ⟨9021575191260859552977373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12028766921681146070636497 9021575191260859552977373)
            ·
              refine ⟨3383090696722822332366515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9021575191260859552977373 3383090696722822332366515)
              ·
                refine ⟨5074636045084233498549773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383090696722822332366515 5074636045084233498549773)
                ·
                  refine ⟨1902988516906587561956165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5074636045084233498549773 1902988516906587561956165)
                  ·
                    refine ⟨356810346919985167866781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1902988516906587561956165 356810346919985167866781)
                    ·
                      rfl

theorem cell23_2084657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_2084657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084657 prefixEnd_2084657 := by exact prefixLift 2084657
  have htrace : WordTrace (prefixWord ++ tailWord_2084657) baseStart_2084657 baseEnd_2084657 := by
    simpa [prefixWord, tailWord_2084657, baseEnd_2084657] using wordTrace_append hprefix tailTrace_2084657
  have hstable : (prefixWord ++ tailWord_2084657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084657).length < 2 ^ (prefixWord ++ tailWord_2084657).sum := by decide
  have hdescent : baseEnd_2084657 < baseStart_2084657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084684 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2084684 : Nat := 118140960795 + 2084684 * 2 ^ 59
def prefixEnd_2084684 : Nat := 4983230072969 + 3 ^ 40 * 2084684 * 2
def baseEnd_2084684 : Nat := 1070444904737626897962719

theorem tailTrace_2084684 : CollatzResearch.WordTrace tailWord_2084684 prefixEnd_2084684 1070444904737626897962719 := by
  unfold tailWord_2084684
  simp only [CollatzResearch.WordTrace]
  refine ⟨38017335989776689263430553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50689781319702252351240737 38017335989776689263430553)
  ·
    refine ⟨28513001992332516947572915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38017335989776689263430553 28513001992332516947572915)
    ·
      refine ⟨42769502988498775421359373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28513001992332516947572915 42769502988498775421359373)
      ·
        refine ⟨16038563620687040783009765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42769502988498775421359373 16038563620687040783009765)
        ·
          refine ⟨3007230678878820146814331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16038563620687040783009765 3007230678878820146814331)
          ·
            refine ⟨4510846018318230220221497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007230678878820146814331 4510846018318230220221497)
            ·
              refine ⟨3383134513738672665166123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510846018318230220221497 3383134513738672665166123)
              ·
                refine ⟨5074701770608008997749185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383134513738672665166123 5074701770608008997749185)
                ·
                  refine ⟨3806026327956006748311889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074701770608008997749185 3806026327956006748311889)
                  ·
                    refine ⟨2854519745967005061233917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3806026327956006748311889 2854519745967005061233917)
                    ·
                      refine ⟨1070444904737626897962719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2854519745967005061233917 1070444904737626897962719)
                      ·
                        rfl

theorem cell23_2084684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2084684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084684 prefixEnd_2084684 := by exact prefixLift 2084684
  have htrace : WordTrace (prefixWord ++ tailWord_2084684) baseStart_2084684 baseEnd_2084684 := by
    simpa [prefixWord, tailWord_2084684, baseEnd_2084684] using wordTrace_append hprefix tailTrace_2084684
  have hstable : (prefixWord ++ tailWord_2084684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084684).length < 2 ^ (prefixWord ++ tailWord_2084684).sum := by decide
  have hdescent : baseEnd_2084684 < baseStart_2084684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084708 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_2084708 : Nat := 118140960795 + 2084708 * 2 ^ 59
def prefixEnd_2084708 : Nat := 4983230072969 + 3 ^ 40 * 2084708 * 2
def baseEnd_2084708 : Nat := 356819076091111601354203

theorem tailTrace_2084708 : CollatzResearch.WordTrace tailWord_2084708 prefixEnd_2084708 356819076091111601354203 := by
  unfold tailWord_2084708
  simp only [CollatzResearch.WordTrace]
  refine ⟨38017773665733215312867389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50690364887644287083823185 38017773665733215312867389)
  ·
    refine ⟨14256665124649955742325271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38017773665733215312867389 14256665124649955742325271)
    ·
      refine ⟨21384997686974933613487907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14256665124649955742325271 21384997686974933613487907)
      ·
        refine ⟨32077496530462400420231861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21384997686974933613487907 32077496530462400420231861)
        ·
          refine ⟨3007265299730850039396737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32077496530462400420231861 3007265299730850039396737)
          ·
            refine ⟨2255448974798137529547553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007265299730850039396737 2255448974798137529547553)
            ·
              refine ⟨1691586731098603147160665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255448974798137529547553 1691586731098603147160665)
              ·
                refine ⟨1268690048323952360370499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691586731098603147160665 1268690048323952360370499)
                ·
                  refine ⟨1903035072485928540555749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268690048323952360370499 1903035072485928540555749)
                  ·
                    refine ⟨356819076091111601354203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903035072485928540555749 356819076091111601354203)
                    ·
                      rfl

theorem cell23_2084708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_2084708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084708 prefixEnd_2084708 := by exact prefixLift 2084708
  have htrace : WordTrace (prefixWord ++ tailWord_2084708) baseStart_2084708 baseEnd_2084708 := by
    simpa [prefixWord, tailWord_2084708, baseEnd_2084708] using wordTrace_append hprefix tailTrace_2084708
  have hstable : (prefixWord ++ tailWord_2084708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084708).length < 2 ^ (prefixWord ++ tailWord_2084708).sum := by decide
  have hdescent : baseEnd_2084708 < baseStart_2084708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084730 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_2084730 : Nat := 118140960795 + 2084730 * 2 ^ 59
def prefixEnd_2084730 : Nat := 4983230072969 + 3 ^ 40 * 2084730 * 2
def baseEnd_2084730 : Nat := 356822841615911239329169

theorem tailTrace_2084730 : CollatzResearch.WordTrace tailWord_2084730 prefixEnd_2084730 356822841615911239329169 := by
  unfold tailWord_2084730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009087434346682095758911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50690899824924485588690429 19009087434346682095758911)
  ·
    refine ⟨28513631151520023143638367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19009087434346682095758911 28513631151520023143638367)
    ·
      refine ⟨42770446727280034715457551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28513631151520023143638367 42770446727280034715457551)
      ·
        refine ⟨64155670090920052073186327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42770446727280034715457551 64155670090920052073186327)
        ·
          refine ⟨96233505136380078109779491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64155670090920052073186327 96233505136380078109779491)
          ·
            refine ⟨144350257704570117164669237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96233505136380078109779491 144350257704570117164669237)
            ·
              refine ⟨13532836659803448484187741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144350257704570117164669237 13532836659803448484187741)
              ·
                refine ⟨5074813747426293181570403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13532836659803448484187741 5074813747426293181570403)
                ·
                  refine ⟨7612220621139439772355605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074813747426293181570403 7612220621139439772355605)
                  ·
                    refine ⟨356822841615911239329169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7612220621139439772355605 356822841615911239329169)
                    ·
                      rfl

theorem cell23_2084730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_2084730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084730 prefixEnd_2084730 := by exact prefixLift 2084730
  have htrace : WordTrace (prefixWord ++ tailWord_2084730) baseStart_2084730 baseEnd_2084730 := by
    simpa [prefixWord, tailWord_2084730, baseEnd_2084730] using wordTrace_append hprefix tailTrace_2084730
  have hstable : (prefixWord ++ tailWord_2084730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084730).length < 2 ^ (prefixWord ++ tailWord_2084730).sum := by decide
  have hdescent : baseEnd_2084730 < baseStart_2084730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084734 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2084734 : Nat := 118140960795 + 2084734 * 2 ^ 59
def prefixEnd_2084734 : Nat := 4983230072969 + 3 ^ 40 * 2084734 * 2
def baseEnd_2084734 : Nat := 356823526256783900779163

theorem tailTrace_2084734 : CollatzResearch.WordTrace tailWord_2084734 prefixEnd_2084734 356823526256783900779163 := by
  unfold tailWord_2084734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504561953671529633272657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50690997086248158044120837 9504561953671529633272657)
  ·
    refine ⟨7128421465253647224954493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9504561953671529633272657 7128421465253647224954493)
    ·
      refine ⟨2673158049470117709357935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7128421465253647224954493 2673158049470117709357935)
      ·
        refine ⟨4009737074205176564036903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673158049470117709357935 4009737074205176564036903)
        ·
          refine ⟨6014605611307764846055355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009737074205176564036903 6014605611307764846055355)
          ·
            refine ⟨9021908416961647269083033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014605611307764846055355 9021908416961647269083033)
            ·
              refine ⟨6766431312721235451812275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9021908416961647269083033 6766431312721235451812275)
              ·
                refine ⟨10149646969081853177718413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766431312721235451812275 10149646969081853177718413)
                ·
                  refine ⟨3806117613405694941644405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10149646969081853177718413 3806117613405694941644405)
                  ·
                    refine ⟨356823526256783900779163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3806117613405694941644405 356823526256783900779163)
                    ·
                      rfl

theorem cell23_2084734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2084734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084734 prefixEnd_2084734 := by exact prefixLift 2084734
  have htrace : WordTrace (prefixWord ++ tailWord_2084734) baseStart_2084734 baseEnd_2084734 := by
    simpa [prefixWord, tailWord_2084734, baseEnd_2084734] using wordTrace_append hprefix tailTrace_2084734
  have hstable : (prefixWord ++ tailWord_2084734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084734).length < 2 ^ (prefixWord ++ tailWord_2084734).sum := by decide
  have hdescent : baseEnd_2084734 < baseStart_2084734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084764 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_2084764 : Nat := 118140960795 + 2084764 * 2 ^ 59
def prefixEnd_2084764 : Nat := 4983230072969 + 3 ^ 40 * 2084764 * 2
def baseEnd_2084764 : Nat := 356828661063328861654117

theorem tailTrace_2084764 : CollatzResearch.WordTrace tailWord_2084764 prefixEnd_2084764 356828661063328861654117 := by
  unfold tailWord_2084764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38018794909631776094886673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50691726546175701459848897 38018794909631776094886673)
  ·
    refine ⟨28514096182223832071165005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38018794909631776094886673 28514096182223832071165005)
    ·
      refine ⟨10692786068333937026686877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28514096182223832071165005 10692786068333937026686877)
      ·
        refine ⟨4009794775625226385007579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10692786068333937026686877 4009794775625226385007579)
        ·
          refine ⟨6014692163437839577511369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009794775625226385007579 6014692163437839577511369)
          ·
            refine ⟨4511019122578379683133527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6014692163437839577511369 4511019122578379683133527)
            ·
              refine ⟨6766528683867569524700291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511019122578379683133527 6766528683867569524700291)
              ·
                refine ⟨10149793025801354287050437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766528683867569524700291 10149793025801354287050437)
                ·
                  refine ⟨1903086192337753928821957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10149793025801354287050437 1903086192337753928821957)
                  ·
                    refine ⟨356828661063328861654117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903086192337753928821957 356828661063328861654117)
                    ·
                      rfl

theorem cell23_2084764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_2084764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084764 prefixEnd_2084764 := by exact prefixLift 2084764
  have htrace : WordTrace (prefixWord ++ tailWord_2084764) baseStart_2084764 baseEnd_2084764 := by
    simpa [prefixWord, tailWord_2084764, baseEnd_2084764] using wordTrace_append hprefix tailTrace_2084764
  have hstable : (prefixWord ++ tailWord_2084764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084764).length < 2 ^ (prefixWord ++ tailWord_2084764).sum := by decide
  have hdescent : baseEnd_2084764 < baseStart_2084764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084788 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2084788 : Nat := 118140960795 + 2084788 * 2 ^ 59
def prefixEnd_2084788 : Nat := 4983230072969 + 3 ^ 40 * 2084788 * 2
def baseEnd_2084788 : Nat := 1070498306725694491062241

theorem tailTrace_2084788 : CollatzResearch.WordTrace tailWord_2084788 prefixEnd_2084788 1070498306725694491062241 := by
  unfold tailWord_2084788
  simp only [CollatzResearch.WordTrace]
  refine ⟨38019232585588302144323509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50692310114117736192431345 38019232585588302144323509)
  ·
    refine ⟨3564303054898903326030329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38019232585588302144323509 3564303054898903326030329)
    ·
      refine ⟨2673227291174177494522747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3564303054898903326030329 2673227291174177494522747)
      ·
        refine ⟨4009840936761266241784121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673227291174177494522747 4009840936761266241784121)
        ·
          refine ⟨3007380702570949681338091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4009840936761266241784121 3007380702570949681338091)
          ·
            refine ⟨4511071053856424522007137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007380702570949681338091 4511071053856424522007137)
            ·
              refine ⟨3383303290392318391505353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511071053856424522007137 3383303290392318391505353)
              ·
                refine ⟨2537477467794238793629015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3383303290392318391505353 2537477467794238793629015)
                ·
                  refine ⟨3806216201691358190443523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537477467794238793629015 3806216201691358190443523)
                  ·
                    refine ⟨5709324302537037285665285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3806216201691358190443523 5709324302537037285665285)
                    ·
                      refine ⟨1070498306725694491062241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5709324302537037285665285 1070498306725694491062241)
                      ·
                        rfl

theorem cell23_2084788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2084788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084788 prefixEnd_2084788 := by exact prefixLift 2084788
  have htrace : WordTrace (prefixWord ++ tailWord_2084788) baseStart_2084788 baseEnd_2084788 := by
    simpa [prefixWord, tailWord_2084788, baseEnd_2084788] using wordTrace_append hprefix tailTrace_2084788
  have hstable : (prefixWord ++ tailWord_2084788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084788).length < 2 ^ (prefixWord ++ tailWord_2084788).sum := by decide
  have hdescent : baseEnd_2084788 < baseStart_2084788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084800 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_2084800 : Nat := 118140960795 + 2084800 * 2 ^ 59
def prefixEnd_2084800 : Nat := 4983230072969 + 3 ^ 40 * 2084800 * 2
def baseEnd_2084800 : Nat := 1070504468493548444112185

theorem tailTrace_2084800 : CollatzResearch.WordTrace tailWord_2084800 prefixEnd_2084800 1070504468493548444112185 := by
  unfold tailWord_2084800
  simp only [CollatzResearch.WordTrace]
  refine ⟨38019451423566565169041927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50692601898088753558722569 38019451423566565169041927)
  ·
    refine ⟨57029177135349847753562891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38019451423566565169041927 57029177135349847753562891)
    ·
      refine ⟨85543765703024771630344337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57029177135349847753562891 85543765703024771630344337)
      ·
        refine ⟨64157824277268578722758253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85543765703024771630344337 64157824277268578722758253)
        ·
          refine ⟨24059184103975717021034345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64157824277268578722758253 24059184103975717021034345)
          ·
            refine ⟨18044388077981787765775759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24059184103975717021034345 18044388077981787765775759)
            ·
              refine ⟨27066582116972681648663639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18044388077981787765775759 27066582116972681648663639)
              ·
                refine ⟨40599873175459022472995459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27066582116972681648663639 40599873175459022472995459)
                ·
                  refine ⟨60899809763188533709493189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40599873175459022472995459 60899809763188533709493189)
                  ·
                    refine ⟨11418714330597850070529973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60899809763188533709493189 11418714330597850070529973)
                    ·
                      refine ⟨1070504468493548444112185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11418714330597850070529973 1070504468493548444112185)
                      ·
                        rfl

theorem cell23_2084800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_2084800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084800 prefixEnd_2084800 := by exact prefixLift 2084800
  have htrace : WordTrace (prefixWord ++ tailWord_2084800) baseStart_2084800 baseEnd_2084800 := by
    simpa [prefixWord, tailWord_2084800, baseEnd_2084800] using wordTrace_append hprefix tailTrace_2084800
  have hstable : (prefixWord ++ tailWord_2084800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084800).length < 2 ^ (prefixWord ++ tailWord_2084800).sum := by decide
  have hdescent : baseEnd_2084800 < baseStart_2084800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084822 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2084822 : Nat := 118140960795 + 2084822 * 2 ^ 59
def prefixEnd_2084822 : Nat := 4983230072969 + 3 ^ 40 * 2084822 * 2
def baseEnd_2084822 : Nat := 1070515765067947358037085

theorem tailTrace_2084822 : CollatzResearch.WordTrace tailWord_2084822 prefixEnd_2084822 1070515765067947358037085 := by
  unfold tailWord_2084822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752481578315839255961545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50693136835368952063589813 4752481578315839255961545)
  ·
    refine ⟨3564361183736879441971159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4752481578315839255961545 3564361183736879441971159)
    ·
      refine ⟨5346541775605319162956739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564361183736879441971159 5346541775605319162956739)
      ·
        refine ⟨8019812663407978744435109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346541775605319162956739 8019812663407978744435109)
        ·
          refine ⟨1503714874388996014581583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8019812663407978744435109 1503714874388996014581583)
          ·
            refine ⟨2255572311583494021872375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503714874388996014581583 2255572311583494021872375)
            ·
              refine ⟨3383358467375241032808563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255572311583494021872375 3383358467375241032808563)
              ·
                refine ⟨5075037701062861549212845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383358467375241032808563 5075037701062861549212845)
                ·
                  refine ⟨1903139137898573080954817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5075037701062861549212845 1903139137898573080954817)
                  ·
                    refine ⟨1427354353423929810716113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903139137898573080954817 1427354353423929810716113)
                    ·
                      refine ⟨1070515765067947358037085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427354353423929810716113 1070515765067947358037085)
                      ·
                        rfl

theorem cell23_2084822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2084822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084822 prefixEnd_2084822 := by exact prefixLift 2084822
  have htrace : WordTrace (prefixWord ++ tailWord_2084822) baseStart_2084822 baseEnd_2084822 := by
    simpa [prefixWord, tailWord_2084822, baseEnd_2084822] using wordTrace_append hprefix tailTrace_2084822
  have hstable : (prefixWord ++ tailWord_2084822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084822).length < 2 ^ (prefixWord ++ tailWord_2084822).sum := by decide
  have hdescent : baseEnd_2084822 < baseStart_2084822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084878 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_2084878 : Nat := 118140960795 + 2084878 * 2 ^ 59
def prefixEnd_2084878 : Nat := 4983230072969 + 3 ^ 40 * 2084878 * 2
def baseEnd_2084878 : Nat := 1070544519984599138936827

theorem tailTrace_2084878 : CollatzResearch.WordTrace tailWord_2084878 prefixEnd_2084878 1070544519984599138936827 := by
  unfold tailWord_2084878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505218467606318707427911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50694498493900366439615525 9505218467606318707427911)
  ·
    refine ⟨14257827701409478061141867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9505218467606318707427911 14257827701409478061141867)
    ·
      refine ⟨21386741552114217091712801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14257827701409478061141867 21386741552114217091712801)
      ·
        refine ⟨16040056164085662818784601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21386741552114217091712801 16040056164085662818784601)
        ·
          refine ⟨12030042123064247114088451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16040056164085662818784601 12030042123064247114088451)
          ·
            refine ⟨18045063184596370671132677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030042123064247114088451 18045063184596370671132677)
            ·
              refine ⟨3383449347111819500837377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18045063184596370671132677 3383449347111819500837377)
              ·
                refine ⟨2537587010333864625628033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3383449347111819500837377 2537587010333864625628033)
                ·
                  refine ⟨1903190257750398469221025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537587010333864625628033 1903190257750398469221025)
                  ·
                    refine ⟨1427392693312798851915769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903190257750398469221025 1427392693312798851915769)
                    ·
                      refine ⟨1070544519984599138936827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427392693312798851915769 1070544519984599138936827)
                      ·
                        rfl

theorem cell23_2084878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_2084878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084878 prefixEnd_2084878 := by exact prefixLift 2084878
  have htrace : WordTrace (prefixWord ++ tailWord_2084878) baseStart_2084878 baseEnd_2084878 := by
    simpa [prefixWord, tailWord_2084878, baseEnd_2084878] using wordTrace_append hprefix tailTrace_2084878
  have hstable : (prefixWord ++ tailWord_2084878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084878).length < 2 ^ (prefixWord ++ tailWord_2084878).sum := by decide
  have hdescent : baseEnd_2084878 < baseStart_2084878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084914 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_2084914 : Nat := 118140960795 + 2084914 * 2 ^ 59
def prefixEnd_2084914 : Nat := 4983230072969 + 3 ^ 40 * 2084914 * 2
def baseEnd_2084914 : Nat := 356854335096053666028887

theorem tailTrace_2084914 : CollatzResearch.WordTrace tailWord_2084914 prefixEnd_2084914 356854335096053666028887 := by
  unfold tailWord_2084914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010765192180031951933449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50695373845813418538489197 19010765192180031951933449)
  ·
    refine ⟨14258073894135023963950087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19010765192180031951933449 14258073894135023963950087)
    ·
      refine ⟨21387110841202535945925131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14258073894135023963950087 21387110841202535945925131)
      ·
        refine ⟨32080666261803803918887697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21387110841202535945925131 32080666261803803918887697)
        ·
          refine ⟨24060499696352852939165773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32080666261803803918887697 24060499696352852939165773)
          ·
            refine ⟨9022687386132319852187165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24060499696352852939165773 9022687386132319852187165)
            ·
              refine ⟨3383507769799619944570187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9022687386132319852187165 3383507769799619944570187)
              ·
                refine ⟨5075261654699429916855281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383507769799619944570187 5075261654699429916855281)
                ·
                  refine ⟨3806446241024572437641461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5075261654699429916855281 3806446241024572437641461)
                  ·
                    refine ⟨356854335096053666028887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3806446241024572437641461 356854335096053666028887)
                    ·
                      rfl

theorem cell23_2084914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_2084914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084914 prefixEnd_2084914 := by exact prefixLift 2084914
  have htrace : WordTrace (prefixWord ++ tailWord_2084914) baseStart_2084914 baseEnd_2084914 := by
    simpa [prefixWord, tailWord_2084914, baseEnd_2084914] using wordTrace_append hprefix tailTrace_2084914
  have hstable : (prefixWord ++ tailWord_2084914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084914).length < 2 ^ (prefixWord ++ tailWord_2084914).sum := by decide
  have hdescent : baseEnd_2084914 < baseStart_2084914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084978 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_2084978 : Nat := 118140960795 + 2084978 * 2 ^ 59
def prefixEnd_2084978 : Nat := 4983230072969 + 3 ^ 40 * 2084978 * 2
def baseEnd_2084978 : Nat := 356865289350016249228789

theorem tailTrace_2084978 : CollatzResearch.WordTrace tailWord_2084978 prefixEnd_2084978 356865289350016249228789 := by
  unfold tailWord_2084978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19011348760122066684515897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50696930026992177825375725 19011348760122066684515897)
  ·
    refine ⟨14258511570091550013386923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19011348760122066684515897 14258511570091550013386923)
    ·
      refine ⟨21387767355137325020080385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14258511570091550013386923 21387767355137325020080385)
      ·
        refine ⟨16040825516352993765060289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21387767355137325020080385 16040825516352993765060289)
        ·
          refine ⟨12030619137264745323795217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16040825516352993765060289 12030619137264745323795217)
          ·
            refine ⟨9022964352948558992846413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12030619137264745323795217 9022964352948558992846413)
            ·
              refine ⟨3383611632355709622317405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9022964352948558992846413 3383611632355709622317405)
              ·
                refine ⟨1268854362133391108369027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3383611632355709622317405 1268854362133391108369027)
                ·
                  refine ⟨1903281543200086662553541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268854362133391108369027 1903281543200086662553541)
                  ·
                    refine ⟨356865289350016249228789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903281543200086662553541 356865289350016249228789)
                    ·
                      rfl

theorem cell23_2084978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_2084978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084978 prefixEnd_2084978 := by exact prefixLift 2084978
  have htrace : WordTrace (prefixWord ++ tailWord_2084978) baseStart_2084978 baseEnd_2084978 := by
    simpa [prefixWord, tailWord_2084978, baseEnd_2084978] using wordTrace_append hprefix tailTrace_2084978
  have hstable : (prefixWord ++ tailWord_2084978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084978).length < 2 ^ (prefixWord ++ tailWord_2084978).sum := by decide
  have hdescent : baseEnd_2084978 < baseStart_2084978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084987 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 7, 5]
def baseStart_2084987 : Nat := 118140960795 + 2084987 * 2 ^ 59
def prefixEnd_2084987 : Nat := 4983230072969 + 3 ^ 40 * 2084987 * 2
def baseEnd_2084987 : Nat := 356866829791979737491275

theorem tailTrace_2084987 : CollatzResearch.WordTrace tailWord_2084987 prefixEnd_2084987 356866829791979737491275 := by
  unfold tailWord_2084987
  simp only [CollatzResearch.WordTrace]
  refine ⟨76045723297455661275141215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50697148864970440850094143 76045723297455661275141215)
  ·
    refine ⟨114068584946183491912711823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76045723297455661275141215 114068584946183491912711823)
    ·
      refine ⟨171102877419275237869067735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114068584946183491912711823 171102877419275237869067735)
      ·
        refine ⟨256654316128912856803601603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171102877419275237869067735 256654316128912856803601603)
        ·
          refine ⟨384981474193369285205402405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256654316128912856803601603 384981474193369285205402405)
          ·
            refine ⟨72184026411256740976012951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384981474193369285205402405 72184026411256740976012951)
            ·
              refine ⟨108276039616885111464019427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72184026411256740976012951 108276039616885111464019427)
              ·
                refine ⟨162414059425327667196029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108276039616885111464019427 162414059425327667196029141)
                ·
                  refine ⟨3806579517781117199906933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162414059425327667196029141 3806579517781117199906933)
                  ·
                    refine ⟨356866829791979737491275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3806579517781117199906933 356866829791979737491275)
                    ·
                      rfl

theorem cell23_2084987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 5].length) (baseStart_2084987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2084987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2084987 prefixEnd_2084987 := by exact prefixLift 2084987
  have htrace : WordTrace (prefixWord ++ tailWord_2084987) baseStart_2084987 baseEnd_2084987 := by
    simpa [prefixWord, tailWord_2084987, baseEnd_2084987] using wordTrace_append hprefix tailTrace_2084987
  have hstable : (prefixWord ++ tailWord_2084987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084987).length < 2 ^ (prefixWord ++ tailWord_2084987).sum := by decide
  have hdescent : baseEnd_2084987 < baseStart_2084987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085017 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_2085017 : Nat := 118140960795 + 2085017 * 2 ^ 59
def prefixEnd_2085017 : Nat := 4983230072969 + 3 ^ 40 * 2085017 * 2
def baseEnd_2085017 : Nat := 356871964598524698366229

theorem tailTrace_2085017 : CollatzResearch.WordTrace tailWord_2085017 prefixEnd_2085017 356871964598524698366229 := by
  unfold tailWord_2085017
  simp only [CollatzResearch.WordTrace]
  refine ⟨76046817487346976398733305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50697878324897984265822203 76046817487346976398733305)
  ·
    refine ⟨57035113115510232299049979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76046817487346976398733305 57035113115510232299049979)
    ·
      refine ⟨85552669673265348448574969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57035113115510232299049979 85552669673265348448574969)
      ·
        refine ⟨64164502254949011336431227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85552669673265348448574969 64164502254949011336431227)
        ·
          refine ⟨96246753382423517004646841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64164502254949011336431227 96246753382423517004646841)
          ·
            refine ⟨72185065036817637753485131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96246753382423517004646841 72185065036817637753485131)
            ·
              refine ⟨108277597555226456630227697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72185065036817637753485131 108277597555226456630227697)
              ·
                refine ⟨81208198166419842472670773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108277597555226456630227697 81208198166419842472670773)
                ·
                  refine ⟨7613268578101860231812885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81208198166419842472670773 7613268578101860231812885)
                  ·
                    refine ⟨356871964598524698366229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7613268578101860231812885 356871964598524698366229)
                    ·
                      rfl

theorem cell23_2085017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_2085017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085017 prefixEnd_2085017 := by exact prefixLift 2085017
  have htrace : WordTrace (prefixWord ++ tailWord_2085017) baseStart_2085017 baseEnd_2085017 := by
    simpa [prefixWord, tailWord_2085017, baseEnd_2085017] using wordTrace_append hprefix tailTrace_2085017
  have hstable : (prefixWord ++ tailWord_2085017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085017).length < 2 ^ (prefixWord ++ tailWord_2085017).sum := by decide
  have hdescent : baseEnd_2085017 < baseStart_2085017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085021 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2085021 : Nat := 118140960795 + 2085021 * 2 ^ 59
def prefixEnd_2085021 : Nat := 4983230072969 + 3 ^ 40 * 2085021 * 2
def baseEnd_2085021 : Nat := 356872649239397359816223

theorem tailTrace_2085021 : CollatzResearch.WordTrace tailWord_2085021 prefixEnd_2085021 356872649239397359816223 := by
  unfold tailWord_2085021
  simp only [CollatzResearch.WordTrace]
  refine ⟨76046963379332485081878917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50697975586221656721252611 76046963379332485081878917)
  ·
    refine ⟨14258805633624840952852297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76046963379332485081878917 14258805633624840952852297)
    ·
      refine ⟨10694104225218630714639223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14258805633624840952852297 10694104225218630714639223)
      ·
        refine ⟨16041156337827946071958835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694104225218630714639223 16041156337827946071958835)
        ·
          refine ⟨24061734506741919107938253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041156337827946071958835 24061734506741919107938253)
          ·
            refine ⟨9023150440028219665476845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24061734506741919107938253 9023150440028219665476845)
            ·
              refine ⟨3383681415010582374553817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9023150440028219665476845 3383681415010582374553817)
              ·
                refine ⟨2537761061257936780915363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3383681415010582374553817 2537761061257936780915363)
                ·
                  refine ⟨3806641591886905171373045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537761061257936780915363 3806641591886905171373045)
                  ·
                    refine ⟨356872649239397359816223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3806641591886905171373045 356872649239397359816223)
                    ·
                      rfl

theorem cell23_2085021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2085021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085021 prefixEnd_2085021 := by exact prefixLift 2085021
  have htrace : WordTrace (prefixWord ++ tailWord_2085021) baseStart_2085021 baseEnd_2085021 := by
    simpa [prefixWord, tailWord_2085021, baseEnd_2085021] using wordTrace_append hprefix tailTrace_2085021
  have hstable : (prefixWord ++ tailWord_2085021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085021).length < 2 ^ (prefixWord ++ tailWord_2085021).sum := by decide
  have hdescent : baseEnd_2085021 < baseStart_2085021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085027 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2085027 : Nat := 118140960795 + 2085027 * 2 ^ 59
def prefixEnd_2085027 : Nat := 4983230072969 + 3 ^ 40 * 2085027 * 2
def baseEnd_2085027 : Nat := 1070621028602119055973641

theorem tailTrace_2085027 : CollatzResearch.WordTrace tailWord_2085027 prefixEnd_2085027 1070621028602119055973641 := by
  unfold tailWord_2085027
  simp only [CollatzResearch.WordTrace]
  refine ⟨76047182217310748106597335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50698121478207165404398223 76047182217310748106597335)
  ·
    refine ⟨114070773325966122159896003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76047182217310748106597335 114070773325966122159896003)
    ·
      refine ⟨171106159988949183239844005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114070773325966122159896003 171106159988949183239844005)
      ·
        refine ⟨32082404997927971857470751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171106159988949183239844005 32082404997927971857470751)
        ·
          refine ⟨48123607496891957786206127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32082404997927971857470751 48123607496891957786206127)
          ·
            refine ⟨72185411245337936679309191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48123607496891957786206127 72185411245337936679309191)
            ·
              refine ⟨108278116868006905018963787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72185411245337936679309191 108278116868006905018963787)
              ·
                refine ⟨162417175302010357528445681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108278116868006905018963787 162417175302010357528445681)
                ·
                  refine ⟨121812881476507768146334261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162417175302010357528445681 121812881476507768146334261)
                  ·
                    refine ⟨11419957638422603263718837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121812881476507768146334261 11419957638422603263718837)
                    ·
                      refine ⟨1070621028602119055973641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11419957638422603263718837 1070621028602119055973641)
                      ·
                        rfl

theorem cell23_2085027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2085027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085027 prefixEnd_2085027 := by exact prefixLift 2085027
  have htrace : WordTrace (prefixWord ++ tailWord_2085027) baseStart_2085027 baseEnd_2085027 := by
    simpa [prefixWord, tailWord_2085027, baseEnd_2085027] using wordTrace_append hprefix tailTrace_2085027
  have hstable : (prefixWord ++ tailWord_2085027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085027).length < 2 ^ (prefixWord ++ tailWord_2085027).sum := by decide
  have hdescent : baseEnd_2085027 < baseStart_2085027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085047 : List Nat := [1, 1, 3, 1, 4, 13]
def baseStart_2085047 : Nat := 118140960795 + 2085047 * 2 ^ 59
def prefixEnd_2085047 : Nat := 4983230072969 + 3 ^ 40 * 2085047 * 2
def baseEnd_2085047 : Nat := 4405890116111971101743

theorem tailTrace_2085047 : CollatzResearch.WordTrace tailWord_2085047 prefixEnd_2085047 4405890116111971101743 := by
  unfold tailWord_2085047
  simp only [CollatzResearch.WordTrace]
  refine ⟨76047911677238291522325395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50698607784825527681550263 76047911677238291522325395)
  ·
    refine ⟨114071867515857437283488093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76047911677238291522325395 114071867515857437283488093)
    ·
      refine ⟨42776950318446538981308035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114071867515857437283488093 42776950318446538981308035)
      ·
        refine ⟨64165425477669808471962053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42776950318446538981308035 64165425477669808471962053)
        ·
          refine ⟨12031017277063089088492885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64165425477669808471962053 12031017277063089088492885)
          ·
            refine ⟨4405890116111971101743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 12031017277063089088492885 4405890116111971101743)
            ·
              rfl

theorem cell23_2085047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 13].length) (baseStart_2085047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085047 prefixEnd_2085047 := by exact prefixLift 2085047
  have htrace : WordTrace (prefixWord ++ tailWord_2085047) baseStart_2085047 baseEnd_2085047 := by
    simpa [prefixWord, tailWord_2085047, baseEnd_2085047] using wordTrace_append hprefix tailTrace_2085047
  have hstable : (prefixWord ++ tailWord_2085047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085047).length < 2 ^ (prefixWord ++ tailWord_2085047).sum := by decide
  have hdescent : baseEnd_2085047 < baseStart_2085047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085051 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 2, 4]
def baseStart_2085051 : Nat := 118140960795 + 2085051 * 2 ^ 59
def prefixEnd_2085051 : Nat := 4983230072969 + 3 ^ 40 * 2085051 * 2
def baseEnd_2085051 : Nat := 356877784045942320691177

theorem tailTrace_2085051 : CollatzResearch.WordTrace tailWord_2085051 prefixEnd_2085051 356877784045942320691177 := by
  unfold tailWord_2085051
  simp only [CollatzResearch.WordTrace]
  refine ⟨76048057569223800205471007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50698705046149200136980671 76048057569223800205471007)
  ·
    refine ⟨114072086353835700308206511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76048057569223800205471007 114072086353835700308206511)
    ·
      refine ⟨171108129530753550462309767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114072086353835700308206511 171108129530753550462309767)
      ·
        refine ⟨256662194296130325693464651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171108129530753550462309767 256662194296130325693464651)
        ·
          refine ⟨384993291444195488540196977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256662194296130325693464651 384993291444195488540196977)
          ·
            refine ⟨288744968583146616405147733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384993291444195488540196977 288744968583146616405147733)
            ·
              refine ⟨3383730100583749410997825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 288744968583146616405147733 3383730100583749410997825)
              ·
                refine ⟨2537797575437812058248369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3383730100583749410997825 2537797575437812058248369)
                ·
                  refine ⟨1903348181578359043686277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537797575437812058248369 1903348181578359043686277)
                  ·
                    refine ⟨356877784045942320691177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903348181578359043686277 356877784045942320691177)
                    ·
                      rfl

theorem cell23_2085051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 4].length) (baseStart_2085051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085051 prefixEnd_2085051 := by exact prefixLift 2085051
  have htrace : WordTrace (prefixWord ++ tailWord_2085051) baseStart_2085051 baseEnd_2085051 := by
    simpa [prefixWord, tailWord_2085051, baseEnd_2085051] using wordTrace_append hprefix tailTrace_2085051
  have hstable : (prefixWord ++ tailWord_2085051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085051).length < 2 ^ (prefixWord ++ tailWord_2085051).sum := by decide
  have hdescent : baseEnd_2085051 < baseStart_2085051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085068 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_2085068 : Nat := 118140960795 + 2085068 * 2 ^ 59
def prefixEnd_2085068 : Nat := 4983230072969 + 3 ^ 40 * 2085068 * 2
def baseEnd_2085068 : Nat := 356880693769651131853651

theorem tailTrace_2085068 : CollatzResearch.WordTrace tailWord_2085068 prefixEnd_2085068 356880693769651131853651 := by
  unfold tailWord_2085068
  simp only [CollatzResearch.WordTrace]
  refine ⟨38024338805081106054419929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50699118406774808072559905 38024338805081106054419929)
  ·
    refine ⟨28518254103810829540814947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38024338805081106054419929 28518254103810829540814947)
    ·
      refine ⟨42777381155716244311222421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28518254103810829540814947 42777381155716244311222421)
      ·
        refine ⟨2005189741674198952088551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42777381155716244311222421 2005189741674198952088551)
        ·
          refine ⟨3007784612511298428132827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005189741674198952088551 3007784612511298428132827)
          ·
            refine ⟨4511676918766947642199241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007784612511298428132827 4511676918766947642199241)
            ·
              refine ⟨3383757689075210731649431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511676918766947642199241 3383757689075210731649431)
              ·
                refine ⟨5075636533612816097474147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383757689075210731649431 5075636533612816097474147)
                ·
                  refine ⟨7613454800419224146211221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075636533612816097474147 7613454800419224146211221)
                  ·
                    refine ⟨356880693769651131853651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7613454800419224146211221 356880693769651131853651)
                    ·
                      rfl

theorem cell23_2085068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_2085068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085068 prefixEnd_2085068 := by exact prefixLift 2085068
  have htrace : WordTrace (prefixWord ++ tailWord_2085068) baseStart_2085068 baseEnd_2085068 := by
    simpa [prefixWord, tailWord_2085068, baseEnd_2085068] using wordTrace_append hprefix tailTrace_2085068
  have hstable : (prefixWord ++ tailWord_2085068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085068).length < 2 ^ (prefixWord ++ tailWord_2085068).sum := by decide
  have hdescent : baseEnd_2085068 < baseStart_2085068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085095 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2085095 : Nat := 118140960795 + 2085095 * 2 ^ 59
def prefixEnd_2085095 : Nat := 4983230072969 + 3 ^ 40 * 2085095 * 2
def baseEnd_2085095 : Nat := 1070655945286624789923329

theorem tailTrace_2085095 : CollatzResearch.WordTrace tailWord_2085095 prefixEnd_2085095 1070655945286624789923329 := by
  unfold tailWord_2085095
  simp only [CollatzResearch.WordTrace]
  refine ⟨76049662381064395720072739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50699774920709597146715159 76049662381064395720072739)
  ·
    refine ⟨114074493571596593580109109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76049662381064395720072739 114074493571596593580109109)
    ·
      refine ⟨10694483772337180648135229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114074493571596593580109109 10694483772337180648135229)
      ·
        refine ⟨4010431414626442743050711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10694483772337180648135229 4010431414626442743050711)
        ·
          refine ⟨6015647121939664114576067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010431414626442743050711 6015647121939664114576067)
          ·
            refine ⟨9023470682909496171864101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015647121939664114576067 9023470682909496171864101)
            ·
              refine ⟨1691900753045530532224519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9023470682909496171864101 1691900753045530532224519)
              ·
                refine ⟨2537851129568295798336779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691900753045530532224519 2537851129568295798336779)
                ·
                  refine ⟨3806776694352443697505169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537851129568295798336779 3806776694352443697505169)
                  ·
                    refine ⟨2855082520764332773128877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3806776694352443697505169 2855082520764332773128877)
                    ·
                      refine ⟨1070655945286624789923329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855082520764332773128877 1070655945286624789923329)
                      ·
                        rfl

theorem cell23_2085095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2085095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085095 prefixEnd_2085095 := by exact prefixLift 2085095
  have htrace : WordTrace (prefixWord ++ tailWord_2085095) baseStart_2085095 baseEnd_2085095 := by
    simpa [prefixWord, tailWord_2085095, baseEnd_2085095] using wordTrace_append hprefix tailTrace_2085095
  have hstable : (prefixWord ++ tailWord_2085095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085095).length < 2 ^ (prefixWord ++ tailWord_2085095).sum := by decide
  have hdescent : baseEnd_2085095 < baseStart_2085095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085151 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2085151 : Nat := 118140960795 + 2085151 * 2 ^ 59
def prefixEnd_2085151 : Nat := 4983230072969 + 3 ^ 40 * 2085151 * 2
def baseEnd_2085151 : Nat := 1070684700203276570823071

theorem tailTrace_2085151 : CollatzResearch.WordTrace tailWord_2085151 prefixEnd_2085151 1070684700203276570823071 := by
  unfold tailWord_2085151
  simp only [CollatzResearch.WordTrace]
  refine ⟨76051704868861517284111307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50701136579241011522740871 76051704868861517284111307)
  ·
    refine ⟨114077557303292275926166961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76051704868861517284111307 114077557303292275926166961)
    ·
      refine ⟨85558167977469206944625221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114077557303292275926166961 85558167977469206944625221)
      ·
        refine ⟨16042156495775476302117229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85558167977469206944625221 16042156495775476302117229)
        ·
          refine ⟨6015808685915803613293961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16042156495775476302117229 6015808685915803613293961)
          ·
            refine ⟨4511856514436852709970471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6015808685915803613293961 4511856514436852709970471)
            ·
              refine ⟨6767784771655279064955707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511856514436852709970471 6767784771655279064955707)
              ·
                refine ⟨10151677157482918597433561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767784771655279064955707 10151677157482918597433561)
                ·
                  refine ⟨7613757868112188948075171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10151677157482918597433561 7613757868112188948075171)
                  ·
                    refine ⟨11420636802168283422112757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613757868112188948075171 11420636802168283422112757)
                    ·
                      refine ⟨1070684700203276570823071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11420636802168283422112757 1070684700203276570823071)
                      ·
                        rfl

theorem cell23_2085151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2085151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085151 prefixEnd_2085151 := by exact prefixLift 2085151
  have htrace : WordTrace (prefixWord ++ tailWord_2085151) baseStart_2085151 baseEnd_2085151 := by
    simpa [prefixWord, tailWord_2085151, baseEnd_2085151] using wordTrace_append hprefix tailTrace_2085151
  have hstable : (prefixWord ++ tailWord_2085151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085151).length < 2 ^ (prefixWord ++ tailWord_2085151).sum := by decide
  have hdescent : baseEnd_2085151 < baseStart_2085151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085182 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_2085182 : Nat := 118140960795 + 2085182 * 2 ^ 59
def prefixEnd_2085182 : Nat := 4983230072969 + 3 ^ 40 * 2085182 * 2
def baseEnd_2085182 : Nat := 1070700618103565949535429

theorem tailTrace_2085182 : CollatzResearch.WordTrace tailWord_2085182 prefixEnd_2085182 1070700618103565949535429 := by
  unfold tailWord_2085182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506604441468651197311225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50701890354499473052326533 9506604441468651197311225)
  ·
    refine ⟨7129953331101488397983419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9506604441468651197311225 7129953331101488397983419)
    ·
      refine ⟨10694929996652232596975129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129953331101488397983419 10694929996652232596975129)
      ·
        refine ⟨8021197497489174447731347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10694929996652232596975129 8021197497489174447731347)
        ·
          refine ⟨12031796246233761671597021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8021197497489174447731347 12031796246233761671597021)
          ·
            refine ⟨4511923592337660626848883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12031796246233761671597021 4511923592337660626848883)
            ·
              refine ⟨6767885388506490940273325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511923592337660626848883 6767885388506490940273325)
              ·
                refine ⟨2537957020689934102602497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6767885388506490940273325 2537957020689934102602497)
                ·
                  refine ⟨1903467765517450576951873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537957020689934102602497 1903467765517450576951873)
                  ·
                    refine ⟨1427600824138087932713905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903467765517450576951873 1427600824138087932713905)
                    ·
                      refine ⟨1070700618103565949535429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427600824138087932713905 1070700618103565949535429)
                      ·
                        rfl

theorem cell23_2085182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_2085182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085182 prefixEnd_2085182 := by exact prefixLift 2085182
  have htrace : WordTrace (prefixWord ++ tailWord_2085182) baseStart_2085182 baseEnd_2085182 := by
    simpa [prefixWord, tailWord_2085182, baseEnd_2085182] using wordTrace_append hprefix tailTrace_2085182
  have hstable : (prefixWord ++ tailWord_2085182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085182).length < 2 ^ (prefixWord ++ tailWord_2085182).sum := by decide
  have hdescent : baseEnd_2085182 < baseStart_2085182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085184 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_2085184 : Nat := 118140960795 + 2085184 * 2 ^ 59
def prefixEnd_2085184 : Nat := 4983230072969 + 3 ^ 40 * 2085184 * 2
def baseEnd_2085184 : Nat := 356900548354958313903473

theorem tailTrace_2085184 : CollatzResearch.WordTrace tailWord_2085184 prefixEnd_2085184 356900548354958313903473 := by
  unfold tailWord_2085184
  simp only [CollatzResearch.WordTrace]
  refine ⟨38026454238870981960031303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50701938985161309280041737 38026454238870981960031303)
  ·
    refine ⟨57039681358306472940046955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38026454238870981960031303 57039681358306472940046955)
    ·
      refine ⟨85559522037459709410070433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57039681358306472940046955 85559522037459709410070433)
      ·
        refine ⟨64169641528094782057552825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85559522037459709410070433 64169641528094782057552825)
        ·
          refine ⟨48127231146071086543164619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64169641528094782057552825 48127231146071086543164619)
          ·
            refine ⟨72190846719106629814746929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48127231146071086543164619 72190846719106629814746929)
            ·
              refine ⟨54143135039329972361060197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72190846719106629814746929 54143135039329972361060197)
              ·
                refine ⟨10151837819874369817698787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54143135039329972361060197 10151837819874369817698787)
                ·
                  refine ⟨15227756729811554726548181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151837819874369817698787 15227756729811554726548181)
                  ·
                    refine ⟨356900548354958313903473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15227756729811554726548181 356900548354958313903473)
                    ·
                      rfl

theorem cell23_2085184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_2085184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085184 prefixEnd_2085184 := by exact prefixLift 2085184
  have htrace : WordTrace (prefixWord ++ tailWord_2085184) baseStart_2085184 baseEnd_2085184 := by
    simpa [prefixWord, tailWord_2085184, baseEnd_2085184] using wordTrace_append hprefix tailTrace_2085184
  have hstable : (prefixWord ++ tailWord_2085184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085184).length < 2 ^ (prefixWord ++ tailWord_2085184).sum := by decide
  have hdescent : baseEnd_2085184 < baseStart_2085184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085201 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_2085201 : Nat := 118140960795 + 2085201 * 2 ^ 59
def prefixEnd_2085201 : Nat := 4983230072969 + 3 ^ 40 * 2085201 * 2
def baseEnd_2085201 : Nat := 356903458078667125065947

theorem tailTrace_2085201 : CollatzResearch.WordTrace tailWord_2085201 prefixEnd_2085201 356903458078667125065947 := by
  unfold tailWord_2085201
  simp only [CollatzResearch.WordTrace]
  refine ⟨76053528518680375823431457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50702352345786917215620971 76053528518680375823431457)
  ·
    refine ⟨57040146389010281867573593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76053528518680375823431457 57040146389010281867573593)
    ·
      refine ⟨42780109791757711400680195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57040146389010281867573593 42780109791757711400680195)
      ·
        refine ⟨64170164687636567101020293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42780109791757711400680195 64170164687636567101020293)
        ·
          refine ⟨12031905878931856331441305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64170164687636567101020293 12031905878931856331441305)
          ·
            refine ⟨9023929409198892248580979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12031905878931856331441305 9023929409198892248580979)
            ·
              refine ⟨13535894113798338372871469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023929409198892248580979 13535894113798338372871469)
              ·
                refine ⟨5075960292674376889826801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13535894113798338372871469 5075960292674376889826801)
                ·
                  refine ⟨3806970219505782667370101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5075960292674376889826801 3806970219505782667370101)
                  ·
                    refine ⟨356903458078667125065947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3806970219505782667370101 356903458078667125065947)
                    ·
                      rfl

theorem cell23_2085201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_2085201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085201 prefixEnd_2085201 := by exact prefixLift 2085201
  have htrace : WordTrace (prefixWord ++ tailWord_2085201) baseStart_2085201 baseEnd_2085201 := by
    simpa [prefixWord, tailWord_2085201, baseEnd_2085201] using wordTrace_append hprefix tailTrace_2085201
  have hstable : (prefixWord ++ tailWord_2085201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085201).length < 2 ^ (prefixWord ++ tailWord_2085201).sum := by decide
  have hdescent : baseEnd_2085201 < baseStart_2085201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085218 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2085218 : Nat := 118140960795 + 2085218 * 2 ^ 59
def prefixEnd_2085218 : Nat := 4983230072969 + 3 ^ 40 * 2085218 * 2
def baseEnd_2085218 : Nat := 356906367802375936228421

theorem tailTrace_2085218 : CollatzResearch.WordTrace tailWord_2085218 prefixEnd_2085218 356906367802375936228421 := by
  unfold tailWord_2085218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19013537139904696931700077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50702765706412525151200205 19013537139904696931700077)
  ·
    refine ⟨7130076427464261349387529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19013537139904696931700077 7130076427464261349387529)
    ·
      refine ⟨5347557320598196012040647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7130076427464261349387529 5347557320598196012040647)
      ·
        refine ⟨8021335980897294018060971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347557320598196012040647 8021335980897294018060971)
        ·
          refine ⟨12032003971345941027091457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8021335980897294018060971 12032003971345941027091457)
          ·
            refine ⟨9024002978509455770318593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12032003971345941027091457 9024002978509455770318593)
            ·
              refine ⟨6768002233882091827738945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9024002978509455770318593 6768002233882091827738945)
              ·
                refine ⟨5076001675411568870804209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768002233882091827738945 5076001675411568870804209)
                ·
                  refine ⟨3807001256558676653103157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076001675411568870804209 3807001256558676653103157)
                  ·
                    refine ⟨356906367802375936228421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3807001256558676653103157 356906367802375936228421)
                    ·
                      rfl

theorem cell23_2085218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2085218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085218 prefixEnd_2085218 := by exact prefixLift 2085218
  have htrace : WordTrace (prefixWord ++ tailWord_2085218) baseStart_2085218 baseEnd_2085218 := by
    simpa [prefixWord, tailWord_2085218, baseEnd_2085218] using wordTrace_append hprefix tailTrace_2085218
  have hstable : (prefixWord ++ tailWord_2085218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085218).length < 2 ^ (prefixWord ++ tailWord_2085218).sum := by decide
  have hdescent : baseEnd_2085218 < baseStart_2085218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085241 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_2085241 : Nat := 118140960795 + 2085241 * 2 ^ 59
def prefixEnd_2085241 : Nat := 4983230072969 + 3 ^ 40 * 2085241 * 2
def baseEnd_2085241 : Nat := 1070730913462181218697657

theorem tailTrace_2085241 : CollatzResearch.WordTrace tailWord_2085241 prefixEnd_2085241 1070730913462181218697657 := by
  unfold tailWord_2085241
  simp only [CollatzResearch.WordTrace]
  refine ⟨76054987438535462654887577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50703324959023641769925051 76054987438535462654887577)
  ·
    refine ⟨57041240578901596991165683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76054987438535462654887577 57041240578901596991165683)
    ·
      refine ⟨85561860868352395486748525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57041240578901596991165683 85561860868352395486748525)
      ·
        refine ⟨32085697825632148307530697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85561860868352395486748525 32085697825632148307530697)
        ·
          refine ⟨24064273369224111230648023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32085697825632148307530697 24064273369224111230648023)
          ·
            refine ⟨36096410053836166845972035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24064273369224111230648023 36096410053836166845972035)
            ·
              refine ⟨54144615080754250268958053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36096410053836166845972035 54144615080754250268958053)
              ·
                refine ⟨10152115327641421925429635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54144615080754250268958053 10152115327641421925429635)
                ·
                  refine ⟨15228172991462132888144453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10152115327641421925429635 15228172991462132888144453)
                  ·
                    refine ⟨2855282435899149916527085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15228172991462132888144453 2855282435899149916527085)
                    ·
                      refine ⟨1070730913462181218697657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855282435899149916527085 1070730913462181218697657)
                      ·
                        rfl

theorem cell23_2085241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_2085241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085241 prefixEnd_2085241 := by exact prefixLift 2085241
  have htrace : WordTrace (prefixWord ++ tailWord_2085241) baseStart_2085241 baseEnd_2085241 := by
    simpa [prefixWord, tailWord_2085241, baseEnd_2085241] using wordTrace_append hprefix tailTrace_2085241
  have hstable : (prefixWord ++ tailWord_2085241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085241).length < 2 ^ (prefixWord ++ tailWord_2085241).sum := by decide
  have hdescent : baseEnd_2085241 < baseStart_2085241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085298 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_2085298 : Nat := 118140960795 + 2085298 * 2 ^ 59
def prefixEnd_2085298 : Nat := 4983230072969 + 3 ^ 40 * 2085298 * 2
def baseEnd_2085298 : Nat := 1070760181859487495684895

theorem tailTrace_2085298 : CollatzResearch.WordTrace tailWord_2085298 prefixEnd_2085298 1070760181859487495684895 := by
  unfold tailWord_2085298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014266599832240347428137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50704710932885974259808365 19014266599832240347428137)
  ·
    refine ⟨14260699949874180260571103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19014266599832240347428137 14260699949874180260571103)
    ·
      refine ⟨21391049924811270390856655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14260699949874180260571103 21391049924811270390856655)
      ·
        refine ⟨32086574887216905586284983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21391049924811270390856655 32086574887216905586284983)
        ·
          refine ⟨48129862330825358379427475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32086574887216905586284983 48129862330825358379427475)
          ·
            refine ⟨72194793496238037569141213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48129862330825358379427475 72194793496238037569141213)
            ·
              refine ⟨27073047561089264088427955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72194793496238037569141213 27073047561089264088427955)
              ·
                refine ⟨40609571341633896132641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27073047561089264088427955 40609571341633896132641933)
                ·
                  refine ⟨15228589253112711049740725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40609571341633896132641933 15228589253112711049740725)
                  ·
                    refine ⟨1427680242479316660913193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15228589253112711049740725 1427680242479316660913193)
                    ·
                      refine ⟨1070760181859487495684895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427680242479316660913193 1070760181859487495684895)
                      ·
                        rfl

theorem cell23_2085298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_2085298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085298 prefixEnd_2085298 := by exact prefixLift 2085298
  have htrace : WordTrace (prefixWord ++ tailWord_2085298) baseStart_2085298 baseEnd_2085298 := by
    simpa [prefixWord, tailWord_2085298, baseEnd_2085298] using wordTrace_append hprefix tailTrace_2085298
  have hstable : (prefixWord ++ tailWord_2085298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085298).length < 2 ^ (prefixWord ++ tailWord_2085298).sum := by decide
  have hdescent : baseEnd_2085298 < baseStart_2085298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085305 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2085305 : Nat := 118140960795 + 2085305 * 2 ^ 59
def prefixEnd_2085305 : Nat := 4983230072969 + 3 ^ 40 * 2085305 * 2
def baseEnd_2085305 : Nat := 1070763776224068968297363

theorem tailTrace_2085305 : CollatzResearch.WordTrace tailWord_2085305 prefixEnd_2085305 1070763776224068968297363 := by
  unfold tailWord_2085305
  simp only [CollatzResearch.WordTrace]
  refine ⟨76057321710303601585217369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50704881140202401056811579 76057321710303601585217369)
  ·
    refine ⟨57042991282727701188913027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76057321710303601585217369 57042991282727701188913027)
    ·
      refine ⟨85564486924091551783369541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57042991282727701188913027 85564486924091551783369541)
      ·
        refine ⟨16043341298267165959381789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85564486924091551783369541 16043341298267165959381789)
        ·
          refine ⟨6016252986850187234768171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16043341298267165959381789 6016252986850187234768171)
          ·
            refine ⟨9024379480275280852152257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6016252986850187234768171 9024379480275280852152257)
            ·
              refine ⟨6768284610206460639114193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9024379480275280852152257 6768284610206460639114193)
              ·
                refine ⟨5076213457654845479335645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768284610206460639114193 5076213457654845479335645)
                ·
                  refine ⟨1903580046620567054750867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5076213457654845479335645 1903580046620567054750867)
                  ·
                    refine ⟨2855370069930850582126301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903580046620567054750867 2855370069930850582126301)
                    ·
                      refine ⟨1070763776224068968297363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855370069930850582126301 1070763776224068968297363)
                      ·
                        rfl

theorem cell23_2085305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2085305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085305 prefixEnd_2085305 := by exact prefixLift 2085305
  have htrace : WordTrace (prefixWord ++ tailWord_2085305) baseStart_2085305 baseEnd_2085305 := by
    simpa [prefixWord, tailWord_2085305, baseEnd_2085305] using wordTrace_append hprefix tailTrace_2085305
  have hstable : (prefixWord ++ tailWord_2085305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085305).length < 2 ^ (prefixWord ++ tailWord_2085305).sum := by decide
  have hdescent : baseEnd_2085305 < baseStart_2085305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085316 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2085316 : Nat := 118140960795 + 2085316 * 2 ^ 59
def prefixEnd_2085316 : Nat := 4983230072969 + 3 ^ 40 * 2085316 * 2
def baseEnd_2085316 : Nat := 356923141503756141753271

theorem tailTrace_2085316 : CollatzResearch.WordTrace tailWord_2085316 prefixEnd_2085316 356923141503756141753271 := by
  unfold tailWord_2085316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38028861456631875231933901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50705148608842500309245201 38028861456631875231933901)
  ·
    refine ⟨14260823046236953211975213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38028861456631875231933901 14260823046236953211975213)
    ·
      refine ⟨5347808642338857454490705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14260823046236953211975213 5347808642338857454490705)
      ·
        refine ⟨4010856481754143090868029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5347808642338857454490705 4010856481754143090868029)
        ·
          refine ⟨1504071180657803659075511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4010856481754143090868029 1504071180657803659075511)
          ·
            refine ⟨2256106770986705488613267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504071180657803659075511 2256106770986705488613267)
            ·
              refine ⟨3384160156480058232919901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256106770986705488613267 3384160156480058232919901)
              ·
                refine ⟨1269060058680021837344963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3384160156480058232919901 1269060058680021837344963)
                ·
                  refine ⟨1903590088020032756017445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269060058680021837344963 1903590088020032756017445)
                  ·
                    refine ⟨356923141503756141753271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903590088020032756017445 356923141503756141753271)
                    ·
                      rfl

theorem cell23_2085316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2085316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085316 prefixEnd_2085316 := by exact prefixLift 2085316
  have htrace : WordTrace (prefixWord ++ tailWord_2085316) baseStart_2085316 baseEnd_2085316 := by
    simpa [prefixWord, tailWord_2085316, baseEnd_2085316] using wordTrace_append hprefix tailTrace_2085316
  have hstable : (prefixWord ++ tailWord_2085316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085316).length < 2 ^ (prefixWord ++ tailWord_2085316).sum := by decide
  have hdescent : baseEnd_2085316 < baseStart_2085316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085321 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_2085321 : Nat := 118140960795 + 2085321 * 2 ^ 59
def prefixEnd_2085321 : Nat := 4983230072969 + 3 ^ 40 * 2085321 * 2
def baseEnd_2085321 : Nat := 356923997304846968565763

theorem tailTrace_2085321 : CollatzResearch.WordTrace tailWord_2085321 prefixEnd_2085321 356923997304846968565763 := by
  unfold tailWord_2085321
  simp only [CollatzResearch.WordTrace]
  refine ⟨76057905278245636317799817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50705270185497090878533211 76057905278245636317799817)
  ·
    refine ⟨57043428958684227238349863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76057905278245636317799817 57043428958684227238349863)
    ·
      refine ⟨85565143438026340857524795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57043428958684227238349863 85565143438026340857524795)
      ·
        refine ⟨128347715157039511286287193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85565143438026340857524795 128347715157039511286287193)
        ·
          refine ⟨96260786367779633464715395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128347715157039511286287193 96260786367779633464715395)
          ·
            refine ⟨144391179551669450197073093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96260786367779633464715395 144391179551669450197073093)
            ·
              refine ⟨27073346165938021911951205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144391179551669450197073093 27073346165938021911951205)
              ·
                refine ⟨5076252406113379108490851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27073346165938021911951205 5076252406113379108490851)
                ·
                  refine ⟨7614378609170068662736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076252406113379108490851 7614378609170068662736277)
                  ·
                    refine ⟨356923997304846968565763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7614378609170068662736277 356923997304846968565763)
                    ·
                      rfl

theorem cell23_2085321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_2085321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085321 prefixEnd_2085321 := by exact prefixLift 2085321
  have htrace : WordTrace (prefixWord ++ tailWord_2085321) baseStart_2085321 baseEnd_2085321 := by
    simpa [prefixWord, tailWord_2085321, baseEnd_2085321] using wordTrace_append hprefix tailTrace_2085321
  have hstable : (prefixWord ++ tailWord_2085321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085321).length < 2 ^ (prefixWord ++ tailWord_2085321).sum := by decide
  have hdescent : baseEnd_2085321 < baseStart_2085321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085331 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 3]
def baseStart_2085331 : Nat := 118140960795 + 2085331 * 2 ^ 59
def prefixEnd_2085331 : Nat := 4983230072969 + 3 ^ 40 * 2085331 * 2
def baseEnd_2085331 : Nat := 1070777126721085866572243

theorem tailTrace_2085331 : CollatzResearch.WordTrace tailWord_2085331 prefixEnd_2085331 1070777126721085866572243 := by
  unfold tailWord_2085331
  simp only [CollatzResearch.WordTrace]
  refine ⟨76058270008209408025663847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50705513338806272017109231 76058270008209408025663847)
  ·
    refine ⟨114087405012314112038495771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76058270008209408025663847 114087405012314112038495771)
    ·
      refine ⟨171131107518471168057743657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114087405012314112038495771 171131107518471168057743657)
      ·
        refine ⟨128348330638853376043307743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171131107518471168057743657 128348330638853376043307743)
        ·
          refine ⟨192522495958280064064961615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128348330638853376043307743 192522495958280064064961615)
          ·
            refine ⟨288783743937420096097442423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192522495958280064064961615 288783743937420096097442423)
            ·
              refine ⟨433175615906130144146163635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288783743937420096097442423 433175615906130144146163635)
              ·
                refine ⟨649763423859195216219245453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433175615906130144146163635 649763423859195216219245453)
                ·
                  refine ⟨243661283947198206082217045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649763423859195216219245453 243661283947198206082217045)
                  ·
                    refine ⟨2855405671256228977525981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 243661283947198206082217045 2855405671256228977525981)
                    ·
                      refine ⟨1070777126721085866572243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855405671256228977525981 1070777126721085866572243)
                      ·
                        rfl

theorem cell23_2085331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_2085331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085331 prefixEnd_2085331 := by exact prefixLift 2085331
  have htrace : WordTrace (prefixWord ++ tailWord_2085331) baseStart_2085331 baseEnd_2085331 := by
    simpa [prefixWord, tailWord_2085331, baseEnd_2085331] using wordTrace_append hprefix tailTrace_2085331
  have hstable : (prefixWord ++ tailWord_2085331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085331).length < 2 ^ (prefixWord ++ tailWord_2085331).sum := by decide
  have hdescent : baseEnd_2085331 < baseStart_2085331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085332 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2085332 : Nat := 118140960795 + 2085332 * 2 ^ 59
def prefixEnd_2085332 : Nat := 4983230072969 + 3 ^ 40 * 2085332 * 2
def baseEnd_2085332 : Nat := 1070777640201740362659739

theorem tailTrace_2085332 : CollatzResearch.WordTrace tailWord_2085332 prefixEnd_2085332 1070777640201740362659739 := by
  unfold tailWord_2085332
  simp only [CollatzResearch.WordTrace]
  refine ⟨38029153240602892598225125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50705537654137190130966833 38029153240602892598225125)
  ·
    refine ⟨7130466232613042362167211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38029153240602892598225125 7130466232613042362167211)
    ·
      refine ⟨10695699348919563543250817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7130466232613042362167211 10695699348919563543250817)
      ·
        refine ⟨8021774511689672657438113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10695699348919563543250817 8021774511689672657438113)
        ·
          refine ⟨6016330883767254493078585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8021774511689672657438113 6016330883767254493078585)
          ·
            refine ⟨4512248162825440869808939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016330883767254493078585 4512248162825440869808939)
            ·
              refine ⟨6768372244238161304713409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512248162825440869808939 6768372244238161304713409)
              ·
                refine ⟨5076279183178620978535057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768372244238161304713409 5076279183178620978535057)
                ·
                  refine ⟨3807209387383965733901293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076279183178620978535057 3807209387383965733901293)
                  ·
                    refine ⟨1427703520268987150212985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3807209387383965733901293 1427703520268987150212985)
                    ·
                      refine ⟨1070777640201740362659739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427703520268987150212985 1070777640201740362659739)
                      ·
                        rfl

theorem cell23_2085332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2085332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085332 prefixEnd_2085332 := by exact prefixLift 2085332
  have htrace : WordTrace (prefixWord ++ tailWord_2085332) baseStart_2085332 baseEnd_2085332 := by
    simpa [prefixWord, tailWord_2085332, baseEnd_2085332] using wordTrace_append hprefix tailTrace_2085332
  have hstable : (prefixWord ++ tailWord_2085332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085332).length < 2 ^ (prefixWord ++ tailWord_2085332).sum := by decide
  have hdescent : baseEnd_2085332 < baseStart_2085332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085338 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_2085338 : Nat := 118140960795 + 2085338 * 2 ^ 59
def prefixEnd_2085338 : Nat := 4983230072969 + 3 ^ 40 * 2085338 * 2
def baseEnd_2085338 : Nat := 356926907028555779728237

theorem tailTrace_2085338 : CollatzResearch.WordTrace tailWord_2085338 prefixEnd_2085338 356926907028555779728237 := by
  unfold tailWord_2085338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014631329796012055292167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50705683546122698814112445 19014631329796012055292167)
  ·
    refine ⟨28521946994694018082938251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014631329796012055292167 28521946994694018082938251)
    ·
      refine ⟨42782920492041027124407377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28521946994694018082938251 42782920492041027124407377)
      ·
        refine ⟨32087190369030770343305533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42782920492041027124407377 32087190369030770343305533)
        ·
          refine ⟨12032696388386538878739575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32087190369030770343305533 12032696388386538878739575)
          ·
            refine ⟨18049044582579808318109363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12032696388386538878739575 18049044582579808318109363)
            ·
              refine ⟨27073566873869712477164045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18049044582579808318109363 27073566873869712477164045)
              ·
                refine ⟨10152587577701142178936517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27073566873869712477164045 10152587577701142178936517)
                ·
                  refine ⟨1903610170818964158550597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10152587577701142178936517 1903610170818964158550597)
                  ·
                    refine ⟨356926907028555779728237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903610170818964158550597 356926907028555779728237)
                    ·
                      rfl

theorem cell23_2085338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_2085338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085338 prefixEnd_2085338 := by exact prefixLift 2085338
  have htrace : WordTrace (prefixWord ++ tailWord_2085338) baseStart_2085338 baseEnd_2085338 := by
    simpa [prefixWord, tailWord_2085338, baseEnd_2085338] using wordTrace_append hprefix tailTrace_2085338
  have hstable : (prefixWord ++ tailWord_2085338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085338).length < 2 ^ (prefixWord ++ tailWord_2085338).sum := by decide
  have hdescent : baseEnd_2085338 < baseStart_2085338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085346 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_2085346 : Nat := 118140960795 + 2085346 * 2 ^ 59
def prefixEnd_2085346 : Nat := 4983230072969 + 3 ^ 40 * 2085346 * 2
def baseEnd_2085346 : Nat := 118976092103433700876075

theorem tailTrace_2085346 : CollatzResearch.WordTrace tailWord_2085346 prefixEnd_2085346 118976092103433700876075 := by
  unfold tailWord_2085346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014704275788766396864973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50705878068770043724973261 19014704275788766396864973)
  ·
    refine ⟨7130514103420787398824365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19014704275788766396864973 7130514103420787398824365)
    ·
      refine ⟨2673942788782795274559137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7130514103420787398824365 2673942788782795274559137)
      ·
        refine ⟨2005457091587096455919353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673942788782795274559137 2005457091587096455919353)
        ·
          refine ⟨1504092818690322341939515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005457091587096455919353 1504092818690322341939515)
          ·
            refine ⟨2256139228035483512909273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504092818690322341939515 2256139228035483512909273)
            ·
              refine ⟨1692104421026612634681955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256139228035483512909273 1692104421026612634681955)
              ·
                refine ⟨2538156631539918952022933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692104421026612634681955 2538156631539918952022933)
                ·
                  refine ⟨118976092103433700876075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2538156631539918952022933 118976092103433700876075)
                  ·
                    rfl

theorem cell23_2085346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_2085346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085346 prefixEnd_2085346 := by exact prefixLift 2085346
  have htrace : WordTrace (prefixWord ++ tailWord_2085346) baseStart_2085346 baseEnd_2085346 := by
    simpa [prefixWord, tailWord_2085346, baseEnd_2085346] using wordTrace_append hprefix tailTrace_2085346
  have hstable : (prefixWord ++ tailWord_2085346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085346).length < 2 ^ (prefixWord ++ tailWord_2085346).sum := by decide
  have hdescent : baseEnd_2085346 < baseStart_2085346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085358 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2085358 : Nat := 118140960795 + 2085358 * 2 ^ 59
def prefixEnd_2085358 : Nat := 4983230072969 + 3 ^ 40 * 2085358 * 2
def baseEnd_2085358 : Nat := 1070790990698757260934619

theorem tailTrace_2085358 : CollatzResearch.WordTrace tailWord_2085358 prefixEnd_2085358 1070790990698757260934619 := by
  unfold tailWord_2085358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9507406847388948954612091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50706169852741061091264485 9507406847388948954612091)
  ·
    refine ⟨14261110271083423431918137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9507406847388948954612091 14261110271083423431918137)
    ·
      refine ⟨10695832703312567573938603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14261110271083423431918137 10695832703312567573938603)
      ·
        refine ⟨16043749054968851360907905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10695832703312567573938603 16043749054968851360907905)
        ·
          refine ⟨12032811791226638520680929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16043749054968851360907905 12032811791226638520680929)
          ·
            refine ⟨9024608843419978890510697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12032811791226638520680929 9024608843419978890510697)
            ·
              refine ⟨6768456632564984167883023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9024608843419978890510697 6768456632564984167883023)
              ·
                refine ⟨10152684948847476251824535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768456632564984167883023 10152684948847476251824535)
                ·
                  refine ⟨15229027423271214377736803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10152684948847476251824535 15229027423271214377736803)
                  ·
                    refine ⟨22843541134906821566605205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15229027423271214377736803 22843541134906821566605205)
                    ·
                      refine ⟨1070790990698757260934619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22843541134906821566605205 1070790990698757260934619)
                      ·
                        rfl

theorem cell23_2085358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2085358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085358 prefixEnd_2085358 := by exact prefixLift 2085358
  have htrace : WordTrace (prefixWord ++ tailWord_2085358) baseStart_2085358 baseEnd_2085358 := by
    simpa [prefixWord, tailWord_2085358, baseEnd_2085358] using wordTrace_append hprefix tailTrace_2085358
  have hstable : (prefixWord ++ tailWord_2085358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085358).length < 2 ^ (prefixWord ++ tailWord_2085358).sum := by decide
  have hdescent : baseEnd_2085358 < baseStart_2085358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085389 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2085389 : Nat := 118140960795 + 2085389 * 2 ^ 59
def prefixEnd_2085389 : Nat := 4983230072969 + 3 ^ 40 * 2085389 * 2
def baseEnd_2085389 : Nat := 356935636199682213215659

theorem tailTrace_2085389 : CollatzResearch.WordTrace tailWord_2085389 prefixEnd_2085389 356935636199682213215659 := by
  unfold tailWord_2085389
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060385441999283931275221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50706923627999522620850147 76060385441999283931275221)
  ·
    refine ⟨1782665283796858217139263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 76060385441999283931275221 1782665283796858217139263)
    ·
      refine ⟨2673997925695287325708895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782665283796858217139263 2673997925695287325708895)
      ·
        refine ⟨4010996888542930988563343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673997925695287325708895 4010996888542930988563343)
        ·
          refine ⟨6016495332814396482845015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010996888542930988563343 6016495332814396482845015)
          ·
            refine ⟨9024742999221594724267523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6016495332814396482845015 9024742999221594724267523)
            ·
              refine ⟨13537114498832392086401285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024742999221594724267523 13537114498832392086401285)
              ·
                refine ⟨2538208968531073516200241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13537114498832392086401285 2538208968531073516200241)
                ·
                  refine ⟨1903656726398305137150181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538208968531073516200241 1903656726398305137150181)
                  ·
                    refine ⟨356935636199682213215659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903656726398305137150181 356935636199682213215659)
                    ·
                      rfl

theorem cell23_2085389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2085389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085389 prefixEnd_2085389 := by exact prefixLift 2085389
  have htrace : WordTrace (prefixWord ++ tailWord_2085389) baseStart_2085389 baseEnd_2085389 := by
    simpa [prefixWord, tailWord_2085389, baseEnd_2085389] using wordTrace_append hprefix tailTrace_2085389
  have hstable : (prefixWord ++ tailWord_2085389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085389).length < 2 ^ (prefixWord ++ tailWord_2085389).sum := by decide
  have hdescent : baseEnd_2085389 < baseStart_2085389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085391 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_2085391 : Nat := 118140960795 + 2085391 * 2 ^ 59
def prefixEnd_2085391 : Nat := 4983230072969 + 3 ^ 40 * 2085391 * 2
def baseEnd_2085391 : Nat := 1070807935560355631821967

theorem tailTrace_2085391 : CollatzResearch.WordTrace tailWord_2085391 prefixEnd_2085391 1070807935560355631821967 := by
  unfold tailWord_2085391
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060458387992038272848027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50706972258661358848565351 76060458387992038272848027)
  ·
    refine ⟨114090687581988057409272041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76060458387992038272848027 114090687581988057409272041)
    ·
      refine ⟨85568015686491043056954031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114090687581988057409272041 85568015686491043056954031)
      ·
        refine ⟨128352023529736564585431047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85568015686491043056954031 128352023529736564585431047)
        ·
          refine ⟨192528035294604846878146571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128352023529736564585431047 192528035294604846878146571)
          ·
            refine ⟨288792052941907270317219857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192528035294604846878146571 288792052941907270317219857)
            ·
              refine ⟨216594039706430452737914893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288792052941907270317219857 216594039706430452737914893)
              ·
                refine ⟨81222764889911419776718085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216594039706430452737914893 81222764889911419776718085)
                ·
                  refine ⟨15229268416858391208134641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81222764889911419776718085 15229268416858391208134641)
                  ·
                    refine ⟨11421951312643793406100981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15229268416858391208134641 11421951312643793406100981)
                    ·
                      refine ⟨1070807935560355631821967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11421951312643793406100981 1070807935560355631821967)
                      ·
                        rfl

theorem cell23_2085391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_2085391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085391 prefixEnd_2085391 := by exact prefixLift 2085391
  have htrace : WordTrace (prefixWord ++ tailWord_2085391) baseStart_2085391 baseEnd_2085391 := by
    simpa [prefixWord, tailWord_2085391, baseEnd_2085391] using wordTrace_append hprefix tailTrace_2085391
  have hstable : (prefixWord ++ tailWord_2085391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085391).length < 2 ^ (prefixWord ++ tailWord_2085391).sum := by decide
  have hdescent : baseEnd_2085391 < baseStart_2085391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085446 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2085446 : Nat := 118140960795 + 2085446 * 2 ^ 59
def prefixEnd_2085446 : Nat := 4983230072969 + 3 ^ 40 * 2085446 * 2
def baseEnd_2085446 : Nat := 1070836176996352916634215

theorem tailTrace_2085446 : CollatzResearch.WordTrace tailWord_2085446 prefixEnd_2085446 1070836176996352916634215 := by
  unfold tailWord_2085446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376952012587274458315631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50708309601861855110733461 2376952012587274458315631)
  ·
    refine ⟨3565428018880911687473447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2376952012587274458315631 3565428018880911687473447)
    ·
      refine ⟨5348142028321367531210171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3565428018880911687473447 5348142028321367531210171)
      ·
        refine ⟨8022213042482051296815257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348142028321367531210171 8022213042482051296815257)
        ·
          refine ⟨6016659781861538472611443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8022213042482051296815257 6016659781861538472611443)
          ·
            refine ⟨9024989672792307708917165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6016659781861538472611443 9024989672792307708917165)
            ·
              refine ⟨3384371127297115390843937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9024989672792307708917165 3384371127297115390843937)
              ·
                refine ⟨2538278345472836543132953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384371127297115390843937 2538278345472836543132953)
                ·
                  refine ⟨1903708759104627407349715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538278345472836543132953 1903708759104627407349715)
                  ·
                    refine ⟨2855563138656941111024573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903708759104627407349715 2855563138656941111024573)
                    ·
                      refine ⟨1070836176996352916634215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855563138656941111024573 1070836176996352916634215)
                      ·
                        rfl

theorem cell23_2085446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2085446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085446 prefixEnd_2085446 := by exact prefixLift 2085446
  have htrace : WordTrace (prefixWord ++ tailWord_2085446) baseStart_2085446 baseEnd_2085446 := by
    simpa [prefixWord, tailWord_2085446, baseEnd_2085446] using wordTrace_append hprefix tailTrace_2085446
  have hstable : (prefixWord ++ tailWord_2085446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085446).length < 2 ^ (prefixWord ++ tailWord_2085446).sum := by decide
  have hdescent : baseEnd_2085446 < baseStart_2085446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085452 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2085452 : Nat := 118140960795 + 2085452 * 2 ^ 59
def prefixEnd_2085452 : Nat := 4983230072969 + 3 ^ 40 * 2085452 * 2
def baseEnd_2085452 : Nat := 1070839257880279893159187

theorem tailTrace_2085452 : CollatzResearch.WordTrace tailWord_2085452 prefixEnd_2085452 1070839257880279893159187 := by
  unfold tailWord_2085452
  simp only [CollatzResearch.WordTrace]
  refine ⟨38031341620385522845409305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50708455493847363793879073 38031341620385522845409305)
  ·
    refine ⟨28523506215289142134056979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38031341620385522845409305 28523506215289142134056979)
    ·
      refine ⟨42785259322933713201085469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28523506215289142134056979 42785259322933713201085469)
      ·
        refine ⟨16044472246100142450407051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42785259322933713201085469 16044472246100142450407051)
        ·
          refine ⟨24066708369150213675610577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16044472246100142450407051 24066708369150213675610577)
          ·
            refine ⟨18050031276862660256707933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24066708369150213675610577 18050031276862660256707933)
            ·
              refine ⟨6768761728823497596265475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18050031276862660256707933 6768761728823497596265475)
              ·
                refine ⟨10153142593235246394398213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768761728823497596265475 10153142593235246394398213)
                ·
                  refine ⟨1903714236231608698949665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10153142593235246394398213 1903714236231608698949665)
                  ·
                    refine ⟨1427785677173706524212249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903714236231608698949665 1427785677173706524212249)
                    ·
                      refine ⟨1070839257880279893159187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427785677173706524212249 1070839257880279893159187)
                      ·
                        rfl

theorem cell23_2085452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2085452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085452 prefixEnd_2085452 := by exact prefixLift 2085452
  have htrace : WordTrace (prefixWord ++ tailWord_2085452) baseStart_2085452 baseEnd_2085452 := by
    simpa [prefixWord, tailWord_2085452, baseEnd_2085452] using wordTrace_append hprefix tailTrace_2085452
  have hstable : (prefixWord ++ tailWord_2085452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085452).length < 2 ^ (prefixWord ++ tailWord_2085452).sum := by decide
  have hdescent : baseEnd_2085452 < baseStart_2085452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085505 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2085505 : Nat := 118140960795 + 2085505 * 2 ^ 59
def prefixEnd_2085505 : Nat := 4983230072969 + 3 ^ 40 * 2085505 * 2
def baseEnd_2085505 : Nat := 356955490784989395265481

theorem tailTrace_2085505 : CollatzResearch.WordTrace tailWord_2085505 prefixEnd_2085505 356955490784989395265481 := by
  unfold tailWord_2085505
  simp only [CollatzResearch.WordTrace]
  refine ⟨76064616309579035742497969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50709744206386023828331979 76064616309579035742497969)
  ·
    refine ⟨57048462232184276806873477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76064616309579035742497969 57048462232184276806873477)
    ·
      refine ⟨10696586668534551901288777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57048462232184276806873477 10696586668534551901288777)
      ·
        refine ⟨8022440001400913925966583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10696586668534551901288777 8022440001400913925966583)
        ·
          refine ⟨12033660002101370888949875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022440001400913925966583 12033660002101370888949875)
          ·
            refine ⟨18050490003152056333424813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033660002101370888949875 18050490003152056333424813)
            ·
              refine ⟨6768933751182021125034305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18050490003152056333424813 6768933751182021125034305)
              ·
                refine ⟨5076700313386515843775729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768933751182021125034305 5076700313386515843775729)
                ·
                  refine ⟨3807525235039886882831797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076700313386515843775729 3807525235039886882831797)
                  ·
                    refine ⟨356955490784989395265481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3807525235039886882831797 356955490784989395265481)
                    ·
                      rfl

theorem cell23_2085505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2085505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085505 prefixEnd_2085505 := by exact prefixLift 2085505
  have htrace : WordTrace (prefixWord ++ tailWord_2085505) baseStart_2085505 baseEnd_2085505 := by
    simpa [prefixWord, tailWord_2085505, baseEnd_2085505] using wordTrace_append hprefix tailTrace_2085505
  have hstable : (prefixWord ++ tailWord_2085505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085505).length < 2 ^ (prefixWord ++ tailWord_2085505).sum := by decide
  have hdescent : baseEnd_2085505 < baseStart_2085505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085545 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_2085545 : Nat := 118140960795 + 2085545 * 2 ^ 59
def prefixEnd_2085545 : Nat := 4983230072969 + 3 ^ 40 * 2085545 * 2
def baseEnd_2085545 : Nat := 1070887011581148029296259

theorem tailTrace_2085545 : CollatzResearch.WordTrace tailWord_2085545 prefixEnd_2085545 1070887011581148029296259 := by
  unfold tailWord_2085545
  simp only [CollatzResearch.WordTrace]
  refine ⟨76066075229434122573954089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50710716819622748382636059 76066075229434122573954089)
  ·
    refine ⟨57049556422075591930465567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76066075229434122573954089 57049556422075591930465567)
    ·
      refine ⟨85574334633113387895698351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57049556422075591930465567 85574334633113387895698351)
      ·
        refine ⟨128361501949670081843547527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85574334633113387895698351 128361501949670081843547527)
        ·
          refine ⟨192542252924505122765321291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128361501949670081843547527 192542252924505122765321291)
          ·
            refine ⟨288813379386757684147981937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192542252924505122765321291 288813379386757684147981937)
            ·
              refine ⟨216610034540068263110986453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288813379386757684147981937 216610034540068263110986453)
              ·
                refine ⟨5076797684532849916663745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 216610034540068263110986453 5076797684532849916663745)
                ·
                  refine ⟨3807598263399637437497809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076797684532849916663745 3807598263399637437497809)
                  ·
                    refine ⟨2855698697549728078123357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807598263399637437497809 2855698697549728078123357)
                    ·
                      refine ⟨1070887011581148029296259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855698697549728078123357 1070887011581148029296259)
                      ·
                        rfl

theorem cell23_2085545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_2085545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085545 prefixEnd_2085545 := by exact prefixLift 2085545
  have htrace : WordTrace (prefixWord ++ tailWord_2085545) baseStart_2085545 baseEnd_2085545 := by
    simpa [prefixWord, tailWord_2085545, baseEnd_2085545] using wordTrace_append hprefix tailTrace_2085545
  have hstable : (prefixWord ++ tailWord_2085545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085545).length < 2 ^ (prefixWord ++ tailWord_2085545).sum := by decide
  have hdescent : baseEnd_2085545 < baseStart_2085545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085552 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 1, 4]
def baseStart_2085552 : Nat := 118140960795 + 2085552 * 2 ^ 59
def prefixEnd_2085552 : Nat := 4983230072969 + 3 ^ 40 * 2085552 * 2
def baseEnd_2085552 : Nat := 356963535315243167302909

theorem tailTrace_2085552 : CollatzResearch.WordTrace tailWord_2085552 prefixEnd_2085552 356963535315243167302909 := by
  unfold tailWord_2085552
  simp only [CollatzResearch.WordTrace]
  refine ⟨38033165270204381384729455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50710887026939175179639273 38033165270204381384729455)
  ·
    refine ⟨57049747905306572077094183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38033165270204381384729455 57049747905306572077094183)
    ·
      refine ⟨85574621857959858115641275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57049747905306572077094183 85574621857959858115641275)
      ·
        refine ⟨128361932786939787173461913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85574621857959858115641275 128361932786939787173461913)
        ·
          refine ⟨96271449590204840380096435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128361932786939787173461913 96271449590204840380096435)
          ·
            refine ⟨144407174385307260570144653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96271449590204840380096435 144407174385307260570144653)
            ·
              refine ⟨54152690394490222713804245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144407174385307260570144653 54152690394490222713804245)
              ·
                refine ⟨1269203681120864594854787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54152690394490222713804245 1269203681120864594854787)
                ·
                  refine ⟨1903805521681296892282181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269203681120864594854787 1903805521681296892282181)
                  ·
                    refine ⟨356963535315243167302909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903805521681296892282181 356963535315243167302909)
                    ·
                      rfl

theorem cell23_2085552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 4].length) (baseStart_2085552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085552 prefixEnd_2085552 := by exact prefixLift 2085552
  have htrace : WordTrace (prefixWord ++ tailWord_2085552) baseStart_2085552 baseEnd_2085552 := by
    simpa [prefixWord, tailWord_2085552, baseEnd_2085552] using wordTrace_append hprefix tailTrace_2085552
  have hstable : (prefixWord ++ tailWord_2085552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085552).length < 2 ^ (prefixWord ++ tailWord_2085552).sum := by decide
  have hdescent : baseEnd_2085552 < baseStart_2085552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085565 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 6]
def baseStart_2085565 : Nat := 118140960795 + 2085565 * 2 ^ 59
def prefixEnd_2085565 : Nat := 4983230072969 + 3 ^ 40 * 2085565 * 2
def baseEnd_2085565 : Nat := 118988586799359772338463

theorem tailTrace_2085565 : CollatzResearch.WordTrace tailWord_2085565 prefixEnd_2085565 118988586799359772338463 := by
  unfold tailWord_2085565
  simp only [CollatzResearch.WordTrace]
  refine ⟨76066804689361665989682149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50711203126241110659788099 76066804689361665989682149)
  ·
    refine ⟨14262525879255312373065403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76066804689361665989682149 14262525879255312373065403)
    ·
      refine ⟨21393788818882968559598105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14262525879255312373065403 21393788818882968559598105)
      ·
        refine ⟨16045341614162226419698579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21393788818882968559598105 16045341614162226419698579)
        ·
          refine ⟨24068012421243339629547869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16045341614162226419698579 24068012421243339629547869)
          ·
            refine ⟨9025504657966252361080451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24068012421243339629547869 9025504657966252361080451)
            ·
              refine ⟨13538256986949378541620677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025504657966252361080451 13538256986949378541620677)
              ·
                refine ⟨2538423185053008476553877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13538256986949378541620677 2538423185053008476553877)
                ·
                  refine ⟨118988586799359772338463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2538423185053008476553877 118988586799359772338463)
                  ·
                    rfl

theorem cell23_2085565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_2085565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085565 prefixEnd_2085565 := by exact prefixLift 2085565
  have htrace : WordTrace (prefixWord ++ tailWord_2085565) baseStart_2085565 baseEnd_2085565 := by
    simpa [prefixWord, tailWord_2085565, baseEnd_2085565] using wordTrace_append hprefix tailTrace_2085565
  have hstable : (prefixWord ++ tailWord_2085565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085565).length < 2 ^ (prefixWord ++ tailWord_2085565).sum := by decide
  have hdescent : baseEnd_2085565 < baseStart_2085565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085592 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2085592 : Nat := 118140960795 + 2085592 * 2 ^ 59
def prefixEnd_2085592 : Nat := 4983230072969 + 3 ^ 40 * 2085592 * 2
def baseEnd_2085592 : Nat := 1070911145171909345408543

theorem tailTrace_2085592 : CollatzResearch.WordTrace tailWord_2085592 prefixEnd_2085592 1070911145171909345408543 := by
  unfold tailWord_2085592
  simp only [CollatzResearch.WordTrace]
  refine ⟨38033894730131924800457515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50711859640175899733943353 38033894730131924800457515)
  ·
    refine ⟨57050842095197887200686273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38033894730131924800457515 57050842095197887200686273)
    ·
      refine ⟨42788131571398415400514705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57050842095197887200686273 42788131571398415400514705)
      ·
        refine ⟨32091098678548811550386029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42788131571398415400514705 32091098678548811550386029)
        ·
          refine ⟨12034162004455804331394761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32091098678548811550386029 12034162004455804331394761)
          ·
            refine ⟨9025621503341853248546071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12034162004455804331394761 9025621503341853248546071)
            ·
              refine ⟨13538432255012779872819107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025621503341853248546071 13538432255012779872819107)
              ·
                refine ⟨20307648382519169809228661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13538432255012779872819107 20307648382519169809228661)
                ·
                  refine ⟨1903842035861172169615187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20307648382519169809228661 1903842035861172169615187)
                  ·
                    refine ⟨2855763053791758254422781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903842035861172169615187 2855763053791758254422781)
                    ·
                      refine ⟨1070911145171909345408543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855763053791758254422781 1070911145171909345408543)
                      ·
                        rfl

theorem cell23_2085592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2085592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085592 prefixEnd_2085592 := by exact prefixLift 2085592
  have htrace : WordTrace (prefixWord ++ tailWord_2085592) baseStart_2085592 baseEnd_2085592 := by
    simpa [prefixWord, tailWord_2085592, baseEnd_2085592] using wordTrace_append hprefix tailTrace_2085592
  have hstable : (prefixWord ++ tailWord_2085592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085592).length < 2 ^ (prefixWord ++ tailWord_2085592).sum := by decide
  have hdescent : baseEnd_2085592 < baseStart_2085592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085596 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2085596 : Nat := 118140960795 + 2085596 * 2 ^ 59
def prefixEnd_2085596 : Nat := 4983230072969 + 3 ^ 40 * 2085596 * 2
def baseEnd_2085596 : Nat := 1070913199094527329758525

theorem tailTrace_2085596 : CollatzResearch.WordTrace tailWord_2085596 prefixEnd_2085596 1070913199094527329758525 := by
  unfold tailWord_2085596
  simp only [CollatzResearch.WordTrace]
  refine ⟨38033967676124679142030321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50711956901499572189373761 38033967676124679142030321)
  ·
    refine ⟨28525475757093509356522741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38033967676124679142030321 28525475757093509356522741)
    ·
      refine ⟨2674263352227516502174007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28525475757093509356522741 2674263352227516502174007)
      ·
        refine ⟨4011395028341274753261011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674263352227516502174007 4011395028341274753261011)
        ·
          refine ⟨6017092542511912129891517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011395028341274753261011 6017092542511912129891517)
          ·
            refine ⟨2256409703441967048709319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6017092542511912129891517 2256409703441967048709319)
            ·
              refine ⟨3384614555162950573063979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256409703441967048709319 3384614555162950573063979)
              ·
                refine ⟨5076921832744425859595969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384614555162950573063979 5076921832744425859595969)
                ·
                  refine ⟨3807691374558319394696977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076921832744425859595969 3807691374558319394696977)
                  ·
                    refine ⟨2855768530918739546022733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807691374558319394696977 2855768530918739546022733)
                    ·
                      refine ⟨1070913199094527329758525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855768530918739546022733 1070913199094527329758525)
                      ·
                        rfl

theorem cell23_2085596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2085596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085596 prefixEnd_2085596 := by exact prefixLift 2085596
  have htrace : WordTrace (prefixWord ++ tailWord_2085596) baseStart_2085596 baseEnd_2085596 := by
    simpa [prefixWord, tailWord_2085596, baseEnd_2085596] using wordTrace_append hprefix tailTrace_2085596
  have hstable : (prefixWord ++ tailWord_2085596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085596).length < 2 ^ (prefixWord ++ tailWord_2085596).sum := by decide
  have hdescent : baseEnd_2085596 < baseStart_2085596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085609 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 1, 1, 3]
def baseStart_2085609 : Nat := 118140960795 + 2085609 * 2 ^ 59
def prefixEnd_2085609 : Nat := 4983230072969 + 3 ^ 40 * 2085609 * 2
def baseEnd_2085609 : Nat := 1070919874343035778895965

theorem tailTrace_2085609 : CollatzResearch.WordTrace tailWord_2085609 prefixEnd_2085609 1070919874343035778895965 := by
  unfold tailWord_2085609
  simp only [CollatzResearch.WordTrace]
  refine ⟨76068409501202261504283881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50712273000801507669522587 76068409501202261504283881)
  ·
    refine ⟨57051307125901696128212911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76068409501202261504283881 57051307125901696128212911)
    ·
      refine ⟨85576960688852544192319367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57051307125901696128212911 85576960688852544192319367)
      ·
        refine ⟨128365441033278816288479051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85576960688852544192319367 128365441033278816288479051)
        ·
          refine ⟨192548161549918224432718577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128365441033278816288479051 192548161549918224432718577)
          ·
            refine ⟨144411121162438668324538933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192548161549918224432718577 144411121162438668324538933)
            ·
              refine ⟨13538542608978625155425525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144411121162438668324538933 13538542608978625155425525)
              ·
                refine ⟨1269238369591746108321143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13538542608978625155425525 1269238369591746108321143)
                ·
                  refine ⟨1903857554387619162481715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269238369591746108321143 1903857554387619162481715)
                  ·
                    refine ⟨2855786331581428743722573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903857554387619162481715 2855786331581428743722573)
                    ·
                      refine ⟨1070919874343035778895965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855786331581428743722573 1070919874343035778895965)
                      ·
                        rfl

theorem cell23_2085609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 1, 3].length) (baseStart_2085609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085609 prefixEnd_2085609 := by exact prefixLift 2085609
  have htrace : WordTrace (prefixWord ++ tailWord_2085609) baseStart_2085609 baseEnd_2085609 := by
    simpa [prefixWord, tailWord_2085609, baseEnd_2085609] using wordTrace_append hprefix tailTrace_2085609
  have hstable : (prefixWord ++ tailWord_2085609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085609).length < 2 ^ (prefixWord ++ tailWord_2085609).sum := by decide
  have hdescent : baseEnd_2085609 < baseStart_2085609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085649 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 3, 2, 2]
def baseStart_2085649 : Nat := 118140960795 + 2085649 * 2 ^ 59
def prefixEnd_2085649 : Nat := 4983230072969 + 3 ^ 40 * 2085649 * 2
def baseEnd_2085649 : Nat := 1070940413569215622395781

theorem tailTrace_2085649 : CollatzResearch.WordTrace tailWord_2085649 prefixEnd_2085649 1070940413569215622395781 := by
  unfold tailWord_2085649
  simp only [CollatzResearch.WordTrace]
  refine ⟨76069868421057348335740001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50713245614038232223826667 76069868421057348335740001)
  ·
    refine ⟨57052401315793011251805001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76069868421057348335740001 57052401315793011251805001)
    ·
      refine ⟨42789300986844758438853751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57052401315793011251805001 42789300986844758438853751)
      ·
        refine ⟨64183951480267137658280627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42789300986844758438853751 64183951480267137658280627)
        ·
          refine ⟨96275927220400706487420941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64183951480267137658280627 96275927220400706487420941)
          ·
            refine ⟨36103472707650264932782853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96275927220400706487420941 36103472707650264932782853)
            ·
              refine ⟨6769401132684424674896785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36103472707650264932782853 6769401132684424674896785)
              ·
                refine ⟨5077050849513318506172589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769401132684424674896785 5077050849513318506172589)
                ·
                  refine ⟨1903894068567494439814721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5077050849513318506172589 1903894068567494439814721)
                  ·
                    refine ⟨1427920551425620829861041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903894068567494439814721 1427920551425620829861041)
                    ·
                      refine ⟨1070940413569215622395781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427920551425620829861041 1070940413569215622395781)
                      ·
                        rfl

theorem cell23_2085649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_2085649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085649 prefixEnd_2085649 := by exact prefixLift 2085649
  have htrace : WordTrace (prefixWord ++ tailWord_2085649) baseStart_2085649 baseEnd_2085649 := by
    simpa [prefixWord, tailWord_2085649, baseEnd_2085649] using wordTrace_append hprefix tailTrace_2085649
  have hstable : (prefixWord ++ tailWord_2085649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085649).length < 2 ^ (prefixWord ++ tailWord_2085649).sum := by decide
  have hdescent : baseEnd_2085649 < baseStart_2085649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085677 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2085677 : Nat := 118140960795 + 2085677 * 2 ^ 59
def prefixEnd_2085677 : Nat := 4983230072969 + 3 ^ 40 * 2085677 * 2
def baseEnd_2085677 : Nat := 1070954791027541512845653

theorem tailTrace_2085677 : CollatzResearch.WordTrace tailWord_2085677 prefixEnd_2085677 1070954791027541512845653 := by
  unfold tailWord_2085677
  simp only [CollatzResearch.WordTrace]
  refine ⟨76070889664955909117759285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50713926443303939411839523 76070889664955909117759285)
  ·
    refine ⟨7131645906089616479789933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76070889664955909117759285 7131645906089616479789933)
    ·
      refine ⟨2674367214783606179921225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7131645906089616479789933 2674367214783606179921225)
      ·
        refine ⟨2005775411087704634940919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2674367214783606179921225 2005775411087704634940919)
        ·
          refine ⟨3008663116631556952411379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005775411087704634940919 3008663116631556952411379)
          ·
            refine ⟨4512994674947335428617069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008663116631556952411379 4512994674947335428617069)
            ·
              refine ⟨1692373003105250785731401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4512994674947335428617069 1692373003105250785731401)
              ·
                refine ⟨1269279752328938089298551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692373003105250785731401 1269279752328938089298551)
                ·
                  refine ⟨1903919628493407133947827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269279752328938089298551 1903919628493407133947827)
                  ·
                    refine ⟨2855879442740110700921741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903919628493407133947827 2855879442740110700921741)
                    ·
                      refine ⟨1070954791027541512845653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855879442740110700921741 1070954791027541512845653)
                      ·
                        rfl

theorem cell23_2085677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2085677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085677 prefixEnd_2085677 := by exact prefixLift 2085677
  have htrace : WordTrace (prefixWord ++ tailWord_2085677) baseStart_2085677 baseEnd_2085677 := by
    simpa [prefixWord, tailWord_2085677, baseEnd_2085677] using wordTrace_append hprefix tailTrace_2085677
  have hstable : (prefixWord ++ tailWord_2085677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085677).length < 2 ^ (prefixWord ++ tailWord_2085677).sum := by decide
  have hdescent : baseEnd_2085677 < baseStart_2085677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085692 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_2085692 : Nat := 118140960795 + 2085692 * 2 ^ 59
def prefixEnd_2085692 : Nat := 4983230072969 + 3 ^ 40 * 2085692 * 2
def baseEnd_2085692 : Nat := 1070962493237358954158083

theorem tailTrace_2085692 : CollatzResearch.WordTrace tailWord_2085692 prefixEnd_2085692 1070962493237358954158083 := by
  unfold tailWord_2085692
  simp only [CollatzResearch.WordTrace]
  refine ⟨38035718379950783339777665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50714291173267711119703553 38035718379950783339777665)
  ·
    refine ⟨28526788784963087504833249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38035718379950783339777665 28526788784963087504833249)
    ·
      refine ⟨21395091588722315628624937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28526788784963087504833249 21395091588722315628624937)
      ·
        refine ⟨16046318691541736721468703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21395091588722315628624937 16046318691541736721468703)
        ·
          refine ⟨24069478037312605082203055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16046318691541736721468703 24069478037312605082203055)
          ·
            refine ⟨36104217055968907623304583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24069478037312605082203055 36104217055968907623304583)
            ·
              refine ⟨54156325583953361434956875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36104217055968907623304583 54156325583953361434956875)
              ·
                refine ⟨81234488375930042152435313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54156325583953361434956875 81234488375930042152435313)
                ·
                  refine ⟨60925866281947531614326485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81234488375930042152435313 60925866281947531614326485)
                  ·
                    refine ⟨1427949990983145272210777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60925866281947531614326485 1427949990983145272210777)
                    ·
                      refine ⟨1070962493237358954158083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427949990983145272210777 1070962493237358954158083)
                      ·
                        rfl

theorem cell23_2085692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_2085692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085692 prefixEnd_2085692 := by exact prefixLift 2085692
  have htrace : WordTrace (prefixWord ++ tailWord_2085692) baseStart_2085692 baseEnd_2085692 := by
    simpa [prefixWord, tailWord_2085692, baseEnd_2085692] using wordTrace_append hprefix tailTrace_2085692
  have hstable : (prefixWord ++ tailWord_2085692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085692).length < 2 ^ (prefixWord ++ tailWord_2085692).sum := by decide
  have hdescent : baseEnd_2085692 < baseStart_2085692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085693 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_2085693 : Nat := 118140960795 + 2085693 * 2 ^ 59
def prefixEnd_2085693 : Nat := 4983230072969 + 3 ^ 40 * 2085693 * 2
def baseEnd_2085693 : Nat := 356987668906004483415193

theorem tailTrace_2085693 : CollatzResearch.WordTrace tailWord_2085693 prefixEnd_2085693 356987668906004483415193 := by
  unfold tailWord_2085693
  simp only [CollatzResearch.WordTrace]
  refine ⟨76071473232897943850341733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50714315488598629233561155 76071473232897943850341733)
  ·
    refine ⟨14263401231168364471939075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76071473232897943850341733 14263401231168364471939075)
    ·
      refine ⟨21395101846752546707908613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14263401231168364471939075 21395101846752546707908613)
      ·
        refine ⟨4011581596266102507732865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21395101846752546707908613 4011581596266102507732865)
        ·
          refine ⟨3008686197199576880799649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4011581596266102507732865 3008686197199576880799649)
          ·
            refine ⟨2256514647899682660599737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008686197199576880799649 2256514647899682660599737)
            ·
              refine ⟨1692385985924761995449803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256514647899682660599737 1692385985924761995449803)
              ·
                refine ⟨2538578978887142993174705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692385985924761995449803 2538578978887142993174705)
                ·
                  refine ⟨1903934234165357244881029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538578978887142993174705 1903934234165357244881029)
                  ·
                    refine ⟨356987668906004483415193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903934234165357244881029 356987668906004483415193)
                    ·
                      rfl

theorem cell23_2085693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_2085693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085693 prefixEnd_2085693 := by exact prefixLift 2085693
  have htrace : WordTrace (prefixWord ++ tailWord_2085693) baseStart_2085693 baseEnd_2085693 := by
    simpa [prefixWord, tailWord_2085693, baseEnd_2085693] using wordTrace_append hprefix tailTrace_2085693
  have hstable : (prefixWord ++ tailWord_2085693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085693).length < 2 ^ (prefixWord ++ tailWord_2085693).sum := by decide
  have hdescent : baseEnd_2085693 < baseStart_2085693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085699 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 3]
def baseStart_2085699 : Nat := 118140960795 + 2085699 * 2 ^ 59
def prefixEnd_2085699 : Nat := 4983230072969 + 3 ^ 40 * 2085699 * 2
def baseEnd_2085699 : Nat := 1070966087601940426770551

theorem tailTrace_2085699 : CollatzResearch.WordTrace tailWord_2085699 prefixEnd_2085699 1070966087601940426770551 := by
  unfold tailWord_2085699
  simp only [CollatzResearch.WordTrace]
  refine ⟨76071692070876206875060151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50714461380584137916706767 76071692070876206875060151)
  ·
    refine ⟨114107538106314310312590227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76071692070876206875060151 114107538106314310312590227)
    ·
      refine ⟨171161307159471465468885341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114107538106314310312590227 171161307159471465468885341)
      ·
        refine ⟨64185490184801799550832003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171161307159471465468885341 64185490184801799550832003)
        ·
          refine ⟨96278235277202699326248005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64185490184801799550832003 96278235277202699326248005)
          ·
            refine ⟨18052169114475506123671501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96278235277202699326248005 18052169114475506123671501)
            ·
              refine ⟨6769563417928314796376813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18052169114475506123671501 6769563417928314796376813)
              ·
                refine ⟨2538586281723118048641305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6769563417928314796376813 2538586281723118048641305)
                ·
                  refine ⟨1903939711292338536480979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538586281723118048641305 1903939711292338536480979)
                  ·
                    refine ⟨2855909566938507804721469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903939711292338536480979 2855909566938507804721469)
                    ·
                      refine ⟨1070966087601940426770551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2855909566938507804721469 1070966087601940426770551)
                      ·
                        rfl

theorem cell23_2085699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_2085699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085699 prefixEnd_2085699 := by exact prefixLift 2085699
  have htrace : WordTrace (prefixWord ++ tailWord_2085699) baseStart_2085699 baseEnd_2085699 := by
    simpa [prefixWord, tailWord_2085699, baseEnd_2085699] using wordTrace_append hprefix tailTrace_2085699
  have hstable : (prefixWord ++ tailWord_2085699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085699).length < 2 ^ (prefixWord ++ tailWord_2085699).sum := by decide
  have hdescent : baseEnd_2085699 < baseStart_2085699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085700 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2085700 : Nat := 118140960795 + 2085700 * 2 ^ 59
def prefixEnd_2085700 : Nat := 4983230072969 + 3 ^ 40 * 2085700 * 2
def baseEnd_2085700 : Nat := 1070966601082594922858047

theorem tailTrace_2085700 : CollatzResearch.WordTrace tailWord_2085700 prefixEnd_2085700 1070966601082594922858047 := by
  unfold tailWord_2085700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38035864271936292022923277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50714485695915056030564369 38035864271936292022923277)
  ·
    refine ⟨14263449101976109508596229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38035864271936292022923277 14263449101976109508596229)
    ·
      refine ⟨2674396706620520532861793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14263449101976109508596229 2674396706620520532861793)
      ·
        refine ⟨2005797529965390399646345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2674396706620520532861793 2005797529965390399646345)
        ·
          refine ⟨1504348147474042799734759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005797529965390399646345 1504348147474042799734759)
          ·
            refine ⟨2256522221211064199602139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504348147474042799734759 2256522221211064199602139)
            ·
              refine ⟨3384783331816596299403209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256522221211064199602139 3384783331816596299403209)
              ·
                refine ⟨2538587498862447224552407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384783331816596299403209 2538587498862447224552407)
                ·
                  refine ⟨3807881248293670836828611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538587498862447224552407 3807881248293670836828611)
                  ·
                    refine ⟨5711821872440506255242917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3807881248293670836828611 5711821872440506255242917)
                    ·
                      refine ⟨1070966601082594922858047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5711821872440506255242917 1070966601082594922858047)
                      ·
                        rfl

theorem cell23_2085700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2085700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085700 prefixEnd_2085700 := by exact prefixLift 2085700
  have htrace : WordTrace (prefixWord ++ tailWord_2085700) baseStart_2085700 baseEnd_2085700 := by
    simpa [prefixWord, tailWord_2085700, baseEnd_2085700] using wordTrace_append hprefix tailTrace_2085700
  have hstable : (prefixWord ++ tailWord_2085700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085700).length < 2 ^ (prefixWord ++ tailWord_2085700).sum := by decide
  have hdescent : baseEnd_2085700 < baseStart_2085700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085739 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 4, 2, 2]
def baseStart_2085739 : Nat := 118140960795 + 2085739 * 2 ^ 59
def prefixEnd_2085739 : Nat := 4983230072969 + 3 ^ 40 * 2085739 * 2
def baseEnd_2085739 : Nat := 1070986626828120270270367

theorem tailTrace_2085739 : CollatzResearch.WordTrace tailWord_2085739 prefixEnd_2085739 1070986626828120270270367 := by
  unfold tailWord_2085739
  simp only [CollatzResearch.WordTrace]
  refine ⟨76073150990731293706516271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50715433993820862471010847 76073150990731293706516271)
  ·
    refine ⟨114109726486096940559774407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76073150990731293706516271 114109726486096940559774407)
    ·
      refine ⟨171164589729145410839661611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114109726486096940559774407 171164589729145410839661611)
      ·
        refine ⟨256746884593718116259492417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171164589729145410839661611 256746884593718116259492417)
        ·
          refine ⟨192560163445288587194619313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256746884593718116259492417 192560163445288587194619313)
          ·
            refine ⟨144420122583966440395964485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192560163445288587194619313 144420122583966440395964485)
            ·
              refine ⟨27078772984493707574243341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144420122583966440395964485 27078772984493707574243341)
              ·
                refine ⟨10154539869185140340341253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27078772984493707574243341 10154539869185140340341253)
                ·
                  refine ⟨1903976225472213813813985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10154539869185140340341253 1903976225472213813813985)
                  ·
                    refine ⟨1427982169104160360360489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903976225472213813813985 1427982169104160360360489)
                    ·
                      refine ⟨1070986626828120270270367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1427982169104160360360489 1070986626828120270270367)
                      ·
                        rfl

theorem cell23_2085739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 2, 2].length) (baseStart_2085739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085739 prefixEnd_2085739 := by exact prefixLift 2085739
  have htrace : WordTrace (prefixWord ++ tailWord_2085739) baseStart_2085739 baseEnd_2085739 := by
    simpa [prefixWord, tailWord_2085739, baseEnd_2085739] using wordTrace_append hprefix tailTrace_2085739
  have hstable : (prefixWord ++ tailWord_2085739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085739).length < 2 ^ (prefixWord ++ tailWord_2085739).sum := by decide
  have hdescent : baseEnd_2085739 < baseStart_2085739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085792 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_2085792 : Nat := 118140960795 + 2085792 * 2 ^ 59
def prefixEnd_2085792 : Nat := 4983230072969 + 3 ^ 40 * 2085792 * 2
def baseEnd_2085792 : Nat := 357004613767602854302541

theorem tailTrace_2085792 : CollatzResearch.WordTrace tailWord_2085792 prefixEnd_2085792 357004613767602854302541 := by
  unfold tailWord_2085792
  simp only [CollatzResearch.WordTrace]
  refine ⟨38037542029769641879097815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50716722706359522505463753 38037542029769641879097815)
  ·
    refine ⟨57056313044654462818646723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38037542029769641879097815 57056313044654462818646723)
    ·
      refine ⟨85584469566981694227970085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57056313044654462818646723 85584469566981694227970085)
      ·
        refine ⟨16047088043809067667744391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85584469566981694227970085 16047088043809067667744391)
        ·
          refine ⟨24070632065713601501616587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16047088043809067667744391 24070632065713601501616587)
          ·
            refine ⟨36105948098570402252424881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24070632065713601501616587 36105948098570402252424881)
            ·
              refine ⟨27079461073927801689318661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36105948098570402252424881 27079461073927801689318661)
              ·
                refine ⟨5077398951361462816747249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27079461073927801689318661 5077398951361462816747249)
                ·
                  refine ⟨3808049213521097112560437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5077398951361462816747249 3808049213521097112560437)
                  ·
                    refine ⟨357004613767602854302541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3808049213521097112560437 357004613767602854302541)
                    ·
                      rfl

theorem cell23_2085792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_2085792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085792 prefixEnd_2085792 := by exact prefixLift 2085792
  have htrace : WordTrace (prefixWord ++ tailWord_2085792) baseStart_2085792 baseEnd_2085792 := by
    simpa [prefixWord, tailWord_2085792, baseEnd_2085792] using wordTrace_append hprefix tailTrace_2085792
  have hstable : (prefixWord ++ tailWord_2085792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085792).length < 2 ^ (prefixWord ++ tailWord_2085792).sum := by decide
  have hdescent : baseEnd_2085792 < baseStart_2085792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085822 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2085822 : Nat := 118140960795 + 2085822 * 2 ^ 59
def prefixEnd_2085822 : Nat := 4983230072969 + 3 ^ 40 * 2085822 * 2
def baseEnd_2085822 : Nat := 357009748574147815177495

theorem tailTrace_2085822 : CollatzResearch.WordTrace tailWord_2085822 prefixEnd_2085822 357009748574147815177495 := by
  unfold tailWord_2085822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9509522281178824860223465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50717452166287065921191813 9509522281178824860223465)
  ·
    refine ⟨7132141710884118645167599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9509522281178824860223465 7132141710884118645167599)
    ·
      refine ⟨10698212566326177967751399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132141710884118645167599 10698212566326177967751399)
      ·
        refine ⟨16047318849489266951627099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698212566326177967751399 16047318849489266951627099)
        ·
          refine ⟨24070978274233900427440649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16047318849489266951627099 24070978274233900427440649)
          ·
            refine ⟨18053233705675425320580487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24070978274233900427440649 18053233705675425320580487)
            ·
              refine ⟨27079850558513137980870731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18053233705675425320580487 27079850558513137980870731)
              ·
                refine ⟨40619775837769706971306097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27079850558513137980870731 40619775837769706971306097)
                ·
                  refine ⟨30464831878327280228479573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40619775837769706971306097 30464831878327280228479573)
                  ·
                    refine ⟨357009748574147815177495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30464831878327280228479573 357009748574147815177495)
                    ·
                      rfl

theorem cell23_2085822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2085822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085822 prefixEnd_2085822 := by exact prefixLift 2085822
  have htrace : WordTrace (prefixWord ++ tailWord_2085822) baseStart_2085822 baseEnd_2085822 := by
    simpa [prefixWord, tailWord_2085822, baseEnd_2085822] using wordTrace_append hprefix tailTrace_2085822
  have hstable : (prefixWord ++ tailWord_2085822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085822).length < 2 ^ (prefixWord ++ tailWord_2085822).sum := by decide
  have hdescent : baseEnd_2085822 < baseStart_2085822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085846 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2085846 : Nat := 118140960795 + 2085846 * 2 ^ 59
def prefixEnd_2085846 : Nat := 4983230072969 + 3 ^ 40 * 2085846 * 2
def baseEnd_2085846 : Nat := 1071041569258151351632375

theorem tailTrace_2085846 : CollatzResearch.WordTrace tailWord_2085846 prefixEnd_2085846 1071041569258151351632375 := by
  unfold tailWord_2085846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754815850083978186291337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50718035734229100653774261 4754815850083978186291337)
  ·
    refine ⟨3566111887562983639718503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4754815850083978186291337 3566111887562983639718503)
    ·
      refine ⟨5349167831344475459577755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566111887562983639718503 5349167831344475459577755)
      ·
        refine ⟨8023751747016713189366633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349167831344475459577755 8023751747016713189366633)
        ·
          refine ⟨6017813810262534892024975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8023751747016713189366633 6017813810262534892024975)
          ·
            refine ⟨9026720715393802338037463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017813810262534892024975 9026720715393802338037463)
            ·
              refine ⟨13540081073090703507056195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026720715393802338037463 13540081073090703507056195)
              ·
                refine ⟨20310121609636055260584293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540081073090703507056195 20310121609636055260584293)
                ·
                  refine ⟨3808147801806760361359555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20310121609636055260584293 3808147801806760361359555)
                  ·
                    refine ⟨5712221702710140542039333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3808147801806760361359555 5712221702710140542039333)
                    ·
                      refine ⟨1071041569258151351632375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5712221702710140542039333 1071041569258151351632375)
                      ·
                        rfl

theorem cell23_2085846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2085846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085846 prefixEnd_2085846 := by exact prefixLift 2085846
  have htrace : WordTrace (prefixWord ++ tailWord_2085846) baseStart_2085846 baseEnd_2085846 := by
    simpa [prefixWord, tailWord_2085846, baseEnd_2085846] using wordTrace_append hprefix tailTrace_2085846
  have hstable : (prefixWord ++ tailWord_2085846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085846).length < 2 ^ (prefixWord ++ tailWord_2085846).sum := by decide
  have hdescent : baseEnd_2085846 < baseStart_2085846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085849 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_2085849 : Nat := 118140960795 + 2085849 * 2 ^ 59
def prefixEnd_2085849 : Nat := 4983230072969 + 3 ^ 40 * 2085849 * 2
def baseEnd_2085849 : Nat := 1071043109700114839894861

theorem tailTrace_2085849 : CollatzResearch.WordTrace tailWord_2085849 prefixEnd_2085849 1071043109700114839894861 := by
  unfold tailWord_2085849
  simp only [CollatzResearch.WordTrace]
  refine ⟨76077163020332782493020601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50718108680221854995347067 76077163020332782493020601)
  ·
    refine ⟨57057872265249586869765451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76077163020332782493020601 57057872265249586869765451)
    ·
      refine ⟨85586808397874380304648177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57057872265249586869765451 85586808397874380304648177)
      ·
        refine ⟨64190106298405785228486133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85586808397874380304648177 64190106298405785228486133)
        ·
          refine ⟨6017822465475542365170575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64190106298405785228486133 6017822465475542365170575)
          ·
            refine ⟨9026733698213313547755863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017822465475542365170575 9026733698213313547755863)
            ·
              refine ⟨13540100547319970321633795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026733698213313547755863 13540100547319970321633795)
              ·
                refine ⟨20310150820979955482450693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540100547319970321633795 20310150820979955482450693)
                ·
                  refine ⟨3808153278933741652959505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20310150820979955482450693 3808153278933741652959505)
                  ·
                    refine ⟨2856114959200306239719629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3808153278933741652959505 2856114959200306239719629)
                    ·
                      refine ⟨1071043109700114839894861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2856114959200306239719629 1071043109700114839894861)
                      ·
                        rfl

theorem cell23_2085849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_2085849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085849 prefixEnd_2085849 := by exact prefixLift 2085849
  have htrace : WordTrace (prefixWord ++ tailWord_2085849) baseStart_2085849 baseEnd_2085849 := by
    simpa [prefixWord, tailWord_2085849, baseEnd_2085849] using wordTrace_append hprefix tailTrace_2085849
  have hstable : (prefixWord ++ tailWord_2085849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085849).length < 2 ^ (prefixWord ++ tailWord_2085849).sum := by decide
  have hdescent : baseEnd_2085849 < baseStart_2085849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085919 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2085919 : Nat := 118140960795 + 2085919 * 2 ^ 59
def prefixEnd_2085919 : Nat := 4983230072969 + 3 ^ 40 * 2085919 * 2
def baseEnd_2085919 : Nat := 1071079053345929566019539

theorem tailTrace_2085919 : CollatzResearch.WordTrace tailWord_2085919 prefixEnd_2085919 1071079053345929566019539 := by
  unfold tailWord_2085919
  simp only [CollatzResearch.WordTrace]
  refine ⟨76079716130079184448068811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50719810753386122965379207 76079716130079184448068811)
  ·
    refine ⟨114119574195118776672103217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76079716130079184448068811 114119574195118776672103217)
    ·
      refine ⟨85589680646339082504077413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114119574195118776672103217 85589680646339082504077413)
      ·
        refine ⟨16048065121188577969514515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85589680646339082504077413 16048065121188577969514515)
        ·
          refine ⟨24072097681782866954271773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16048065121188577969514515 24072097681782866954271773)
          ·
            refine ⟨9027036630668575107851915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24072097681782866954271773 9027036630668575107851915)
            ·
              refine ⟨13540554946002862661777873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027036630668575107851915 13540554946002862661777873)
              ·
                refine ⟨10155416209502146996333405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13540554946002862661777873 10155416209502146996333405)
                ·
                  refine ⟨3808281078563305123625027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10155416209502146996333405 3808281078563305123625027)
                  ·
                    refine ⟨5712421617844957685437541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3808281078563305123625027 5712421617844957685437541)
                    ·
                      refine ⟨1071079053345929566019539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5712421617844957685437541 1071079053345929566019539)
                      ·
                        rfl

theorem cell23_2085919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2085919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085919 prefixEnd_2085919 := by exact prefixLift 2085919
  have htrace : WordTrace (prefixWord ++ tailWord_2085919) baseStart_2085919 baseEnd_2085919 := by
    simpa [prefixWord, tailWord_2085919, baseEnd_2085919] using wordTrace_append hprefix tailTrace_2085919
  have hstable : (prefixWord ++ tailWord_2085919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085919).length < 2 ^ (prefixWord ++ tailWord_2085919).sum := by decide
  have hdescent : baseEnd_2085919 < baseStart_2085919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085940 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2085940 : Nat := 118140960795 + 2085940 * 2 ^ 59
def prefixEnd_2085940 : Nat := 4983230072969 + 3 ^ 40 * 2085940 * 2
def baseEnd_2085940 : Nat := 1071089836439673983856943

theorem tailTrace_2085940 : CollatzResearch.WordTrace tailWord_2085940 prefixEnd_2085940 1071089836439673983856943 := by
  unfold tailWord_2085940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38040241031501552517291637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50720321375335403356388849 38040241031501552517291637)
  ·
    refine ⟨3566272596703270548496091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38040241031501552517291637 3566272596703270548496091)
    ·
      refine ⟨5349408895054905822744137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566272596703270548496091 5349408895054905822744137)
      ·
        refine ⟨4012056671291179367058103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5349408895054905822744137 4012056671291179367058103)
        ·
          refine ⟨6018085006936769050587155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012056671291179367058103 6018085006936769050587155)
          ·
            refine ⟨9027127510405153575880733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018085006936769050587155 9027127510405153575880733)
            ·
              refine ⟨3385172816401932590955275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9027127510405153575880733 3385172816401932590955275)
              ·
                refine ⟨5077759224602898886432913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385172816401932590955275 5077759224602898886432913)
                ·
                  refine ⟨3808319418452174164824685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5077759224602898886432913 3808319418452174164824685)
                  ·
                    refine ⟨1428119781919565311809257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808319418452174164824685 1428119781919565311809257)
                    ·
                      refine ⟨1071089836439673983856943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428119781919565311809257 1071089836439673983856943)
                      ·
                        rfl

theorem cell23_2085940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2085940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085940 prefixEnd_2085940 := by exact prefixLift 2085940
  have htrace : WordTrace (prefixWord ++ tailWord_2085940) baseStart_2085940 baseEnd_2085940 := by
    simpa [prefixWord, tailWord_2085940, baseEnd_2085940] using wordTrace_append hprefix tailTrace_2085940
  have hstable : (prefixWord ++ tailWord_2085940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085940).length < 2 ^ (prefixWord ++ tailWord_2085940).sum := by decide
  have hdescent : baseEnd_2085940 < baseStart_2085940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085950 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2085950 : Nat := 118140960795 + 2085950 * 2 ^ 59
def prefixEnd_2085950 : Nat := 4983230072969 + 3 ^ 40 * 2085950 * 2
def baseEnd_2085950 : Nat := 357031657082072981577299

theorem tailTrace_2085950 : CollatzResearch.WordTrace tailWord_2085950 prefixEnd_2085950 357031657082072981577299 := by
  unfold tailWord_2085950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510105849120859592805913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50720564528644584494964869 9510105849120859592805913)
  ·
    refine ⟨7132579386840644694604435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9510105849120859592805913 7132579386840644694604435)
    ·
      refine ⟨10698869080260967041906653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132579386840644694604435 10698869080260967041906653)
      ·
        refine ⟨4012075905097862640714995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10698869080260967041906653 4012075905097862640714995)
        ·
          refine ⟨6018113857646793961072493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012075905097862640714995 6018113857646793961072493)
          ·
            refine ⟨2256792696617547735402185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6018113857646793961072493 2256792696617547735402185)
            ·
              refine ⟨1692594522463160801551639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256792696617547735402185 1692594522463160801551639)
              ·
                refine ⟨2538891783694741202327459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692594522463160801551639 2538891783694741202327459)
                ·
                  refine ⟨3808337675542111803491189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538891783694741202327459 3808337675542111803491189)
                  ·
                    refine ⟨357031657082072981577299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3808337675542111803491189 357031657082072981577299)
                    ·
                      rfl

theorem cell23_2085950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2085950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085950 prefixEnd_2085950 := by exact prefixLift 2085950
  have htrace : WordTrace (prefixWord ++ tailWord_2085950) baseStart_2085950 baseEnd_2085950 := by
    simpa [prefixWord, tailWord_2085950, baseEnd_2085950] using wordTrace_append hprefix tailTrace_2085950
  have hstable : (prefixWord ++ tailWord_2085950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085950).length < 2 ^ (prefixWord ++ tailWord_2085950).sum := by decide
  have hdescent : baseEnd_2085950 < baseStart_2085950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085953 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2085953 : Nat := 118140960795 + 2085953 * 2 ^ 59
def prefixEnd_2085953 : Nat := 4983230072969 + 3 ^ 40 * 2085953 * 2
def baseEnd_2085953 : Nat := 1071096511688182432994383

theorem tailTrace_2085953 : CollatzResearch.WordTrace tailWord_2085953 prefixEnd_2085953 1071096511688182432994383 := by
  unfold tailWord_2085953
  simp only [CollatzResearch.WordTrace]
  refine ⟨76080956211956008254806513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50720637474637338836537675 76080956211956008254806513)
  ·
    refine ⟨57060717158967006191104885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76080956211956008254806513 57060717158967006191104885)
    ·
      refine ⟨5349442233653156830416083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57060717158967006191104885 5349442233653156830416083)
      ·
        refine ⟨8024163350479735245624125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349442233653156830416083 8024163350479735245624125)
        ·
          refine ⟨3009061256429900717109047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8024163350479735245624125 3009061256429900717109047)
          ·
            refine ⟨4513591884644851075663571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009061256429900717109047 4513591884644851075663571)
            ·
              refine ⟨6770387826967276613495357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513591884644851075663571 6770387826967276613495357)
              ·
                refine ⟨2538895435112728730060759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6770387826967276613495357 2538895435112728730060759)
                ·
                  refine ⟨3808343152669093095091139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538895435112728730060759 3808343152669093095091139)
                  ·
                    refine ⟨5712514729003639642636709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3808343152669093095091139 5712514729003639642636709)
                    ·
                      refine ⟨1071096511688182432994383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5712514729003639642636709 1071096511688182432994383)
                      ·
                        rfl

theorem cell23_2085953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2085953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085953 prefixEnd_2085953 := by exact prefixLift 2085953
  have htrace : WordTrace (prefixWord ++ tailWord_2085953) baseStart_2085953 baseEnd_2085953 := by
    simpa [prefixWord, tailWord_2085953, baseEnd_2085953] using wordTrace_append hprefix tailTrace_2085953
  have hstable : (prefixWord ++ tailWord_2085953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085953).length < 2 ^ (prefixWord ++ tailWord_2085953).sum := by decide
  have hdescent : baseEnd_2085953 < baseStart_2085953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085969 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_2085969 : Nat := 118140960795 + 2085969 * 2 ^ 59
def prefixEnd_2085969 : Nat := 4983230072969 + 3 ^ 40 * 2085969 * 2
def baseEnd_2085969 : Nat := 1071104727378654370394309

theorem tailTrace_2085969 : CollatzResearch.WordTrace tailWord_2085969 prefixEnd_2085969 1071104727378654370394309 := by
  unfold tailWord_2085969
  simp only [CollatzResearch.WordTrace]
  refine ⟨76081539779898042987388961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50721026519932028658259307 76081539779898042987388961)
  ·
    refine ⟨57061154834923532240541721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76081539779898042987388961 57061154834923532240541721)
    ·
      refine ⟨42795866126192649180406291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57061154834923532240541721 42795866126192649180406291)
      ·
        refine ⟨64193799189288973770609437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42795866126192649180406291 64193799189288973770609437)
        ·
          refine ⟨24072674695983365163978539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64193799189288973770609437 24072674695983365163978539)
          ·
            refine ⟨36109012043975047745967809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24072674695983365163978539 36109012043975047745967809)
            ·
              refine ⟨27081759032981285809475857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36109012043975047745967809 27081759032981285809475857)
              ·
                refine ⟨20311319274735964357106893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27081759032981285809475857 20311319274735964357106893)
                ·
                  refine ⟨7616744728025986633915085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20311319274735964357106893 7616744728025986633915085)
                  ·
                    refine ⟨2856279273009744987718157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7616744728025986633915085 2856279273009744987718157)
                    ·
                      refine ⟨1071104727378654370394309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2856279273009744987718157 1071104727378654370394309)
                      ·
                        rfl

theorem cell23_2085969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_2085969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085969 prefixEnd_2085969 := by exact prefixLift 2085969
  have htrace : WordTrace (prefixWord ++ tailWord_2085969) baseStart_2085969 baseEnd_2085969 := by
    simpa [prefixWord, tailWord_2085969, baseEnd_2085969] using wordTrace_append hprefix tailTrace_2085969
  have hstable : (prefixWord ++ tailWord_2085969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085969).length < 2 ^ (prefixWord ++ tailWord_2085969).sum := by decide
  have hdescent : baseEnd_2085969 < baseStart_2085969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085970 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_2085970 : Nat := 118140960795 + 2085970 * 2 ^ 59
def prefixEnd_2085970 : Nat := 4983230072969 + 3 ^ 40 * 2085970 * 2
def baseEnd_2085970 : Nat := 1071105240859308866481805

theorem tailTrace_2085970 : CollatzResearch.WordTrace tailWord_2085970 prefixEnd_2085970 1071105240859308866481805 := by
  unfold tailWord_2085970
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020394063223605039543841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50721050835262946772116909 19020394063223605039543841)
  ·
    refine ⟨14265295547417703779657881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19020394063223605039543841 14265295547417703779657881)
    ·
      refine ⟨10698971660563277834743411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14265295547417703779657881 10698971660563277834743411)
      ·
        refine ⟨16048457490844916752115117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698971660563277834743411 16048457490844916752115117)
        ·
          refine ⟨6018171559066843782043169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16048457490844916752115117 6018171559066843782043169)
          ·
            refine ⟨4513628669300132836532377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6018171559066843782043169 4513628669300132836532377)
            ·
              refine ⟨3385221501975099627399283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4513628669300132836532377 3385221501975099627399283)
              ·
                refine ⟨5077832252962649441098925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385221501975099627399283 5077832252962649441098925)
                ·
                  refine ⟨1904187094860993540412097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5077832252962649441098925 1904187094860993540412097)
                  ·
                    refine ⟨1428140321145745155309073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1904187094860993540412097 1428140321145745155309073)
                    ·
                      refine ⟨1071105240859308866481805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428140321145745155309073 1071105240859308866481805)
                      ·
                        rfl

theorem cell23_2085970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_2085970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2085970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2085970 prefixEnd_2085970 := by exact prefixLift 2085970
  have htrace : WordTrace (prefixWord ++ tailWord_2085970) baseStart_2085970 baseEnd_2085970 := by
    simpa [prefixWord, tailWord_2085970, baseEnd_2085970] using wordTrace_append hprefix tailTrace_2085970
  have hstable : (prefixWord ++ tailWord_2085970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085970).length < 2 ^ (prefixWord ++ tailWord_2085970).sum := by decide
  have hdescent : baseEnd_2085970 < baseStart_2085970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086013 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_2086013 : Nat := 118140960795 + 2086013 * 2 ^ 59
def prefixEnd_2086013 : Nat := 4983230072969 + 3 ^ 40 * 2086013 * 2
def baseEnd_2086013 : Nat := 1071127320527452198244107

theorem tailTrace_2086013 : CollatzResearch.WordTrace tailWord_2086013 prefixEnd_2086013 1071127320527452198244107 := by
  unfold tailWord_2086013
  simp only [CollatzResearch.WordTrace]
  refine ⟨76083144591738638501990693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50722096394492425667993795 76083144591738638501990693)
  ·
    refine ⟨14265589610950994719123255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76083144591738638501990693 14265589610950994719123255)
    ·
      refine ⟨21398384416426492078684883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14265589610950994719123255 21398384416426492078684883)
      ·
        refine ⟨32097576624639738118027325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398384416426492078684883 32097576624639738118027325)
        ·
          refine ⟨12036591234239901794260247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32097576624639738118027325 12036591234239901794260247)
          ·
            refine ⟨18054886851359852691390371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12036591234239901794260247 18054886851359852691390371)
            ·
              refine ⟨27082330277039779037085557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18054886851359852691390371 27082330277039779037085557)
              ·
                refine ⟨2538968463472479284726771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27082330277039779037085557 2538968463472479284726771)
                ·
                  refine ⟨3808452695208718927090157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538968463472479284726771 3808452695208718927090157)
                  ·
                    refine ⟨1428169760703269597658809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808452695208718927090157 1428169760703269597658809)
                    ·
                      refine ⟨1071127320527452198244107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428169760703269597658809 1071127320527452198244107)
                      ·
                        rfl

theorem cell23_2086013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_2086013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086013 prefixEnd_2086013 := by exact prefixLift 2086013
  have htrace : WordTrace (prefixWord ++ tailWord_2086013) baseStart_2086013 baseEnd_2086013 := by
    simpa [prefixWord, tailWord_2086013, baseEnd_2086013] using wordTrace_append hprefix tailTrace_2086013
  have hstable : (prefixWord ++ tailWord_2086013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086013).length < 2 ^ (prefixWord ++ tailWord_2086013).sum := by decide
  have hdescent : baseEnd_2086013 < baseStart_2086013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086047 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2086047 : Nat := 118140960795 + 2086047 * 2 ^ 59
def prefixEnd_2086047 : Nat := 4983230072969 + 3 ^ 40 * 2086047 * 2
def baseEnd_2086047 : Nat := 1071144778869705065218951

theorem tailTrace_2086047 : CollatzResearch.WordTrace tailWord_2086047 prefixEnd_2086047 1071144778869705065218951 := by
  unfold tailWord_2086047
  simp only [CollatzResearch.WordTrace]
  refine ⟨76084384673615462308728395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50722923115743641539152263 76084384673615462308728395)
  ·
    refine ⟨114126577010423193463092593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76084384673615462308728395 114126577010423193463092593)
    ·
      refine ⟨85594932757817395097319445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114126577010423193463092593 85594932757817395097319445)
      ·
        refine ⟨4012262473022690395186849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85594932757817395097319445 4012262473022690395186849)
        ·
          refine ⟨3009196854767017796390137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4012262473022690395186849 3009196854767017796390137)
          ·
            refine ⟨2256897641075263347292603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3009196854767017796390137 2256897641075263347292603)
            ·
              refine ⟨3385346461612895020938905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256897641075263347292603 3385346461612895020938905)
              ·
                refine ⟨2539009846209671265704179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385346461612895020938905 2539009846209671265704179)
                ·
                  refine ⟨3808514769314506898556269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539009846209671265704179 3808514769314506898556269)
                  ·
                    refine ⟨1428193038492940086958601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808514769314506898556269 1428193038492940086958601)
                    ·
                      refine ⟨1071144778869705065218951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428193038492940086958601 1071144778869705065218951)
                      ·
                        rfl

theorem cell23_2086047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2086047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086047 prefixEnd_2086047 := by exact prefixLift 2086047
  have htrace : WordTrace (prefixWord ++ tailWord_2086047) baseStart_2086047 baseEnd_2086047 := by
    simpa [prefixWord, tailWord_2086047, baseEnd_2086047] using wordTrace_append hprefix tailTrace_2086047
  have hstable : (prefixWord ++ tailWord_2086047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086047).length < 2 ^ (prefixWord ++ tailWord_2086047).sum := by decide
  have hdescent : baseEnd_2086047 < baseStart_2086047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086049 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 9]
def baseStart_2086049 : Nat := 118140960795 + 2086049 * 2 ^ 59
def prefixEnd_2086049 : Nat := 4983230072969 + 3 ^ 40 * 2086049 * 2
def baseEnd_2086049 : Nat := 119016200647890450821549

theorem tailTrace_2086049 : CollatzResearch.WordTrace tailWord_2086049 prefixEnd_2086049 119016200647890450821549 := by
  unfold tailWord_2086049
  simp only [CollatzResearch.WordTrace]
  refine ⟨76084457619608216650301201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50722971746405477766867467 76084457619608216650301201)
  ·
    refine ⟨57063343214706162487725901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76084457619608216650301201 57063343214706162487725901)
    ·
      refine ⟨21398753705514810932897213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57063343214706162487725901 21398753705514810932897213)
      ·
        refine ⟨8024532639568054099836455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21398753705514810932897213 8024532639568054099836455)
        ·
          refine ⟨12036798959352081149754683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024532639568054099836455 12036798959352081149754683)
          ·
            refine ⟨18055198439028121724632025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12036798959352081149754683 18055198439028121724632025)
            ·
              refine ⟨13541398829271091293474019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18055198439028121724632025 13541398829271091293474019)
              ·
                refine ⟨20312098243906636940211029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541398829271091293474019 20312098243906636940211029)
                ·
                  refine ⟨119016200647890450821549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20312098243906636940211029 119016200647890450821549)
                  ·
                    rfl

theorem cell23_2086049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_2086049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086049 prefixEnd_2086049 := by exact prefixLift 2086049
  have htrace : WordTrace (prefixWord ++ tailWord_2086049) baseStart_2086049 baseEnd_2086049 := by
    simpa [prefixWord, tailWord_2086049, baseEnd_2086049] using wordTrace_append hprefix tailTrace_2086049
  have hstable : (prefixWord ++ tailWord_2086049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086049).length < 2 ^ (prefixWord ++ tailWord_2086049).sum := by decide
  have hdescent : baseEnd_2086049 < baseStart_2086049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086099 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4]
def baseStart_2086099 : Nat := 118140960795 + 2086099 * 2 ^ 59
def prefixEnd_2086099 : Nat := 4983230072969 + 3 ^ 40 * 2086099 * 2
def baseEnd_2086099 : Nat := 1071171479863738861768711

theorem tailTrace_2086099 : CollatzResearch.WordTrace tailWord_2086099 prefixEnd_2086099 1071171479863738861768711 := by
  unfold tailWord_2086099
  simp only [CollatzResearch.WordTrace]
  refine ⟨76086281269427075189621351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50724187512951383459747567 76086281269427075189621351)
  ·
    refine ⟨114129421904140612784432027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76086281269427075189621351 114129421904140612784432027)
    ·
      refine ⟨171194132856210919176648041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114129421904140612784432027 171194132856210919176648041)
      ·
        refine ⟨128395599642158189382486031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171194132856210919176648041 128395599642158189382486031)
        ·
          refine ⟨192593399463237284073729047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128395599642158189382486031 192593399463237284073729047)
          ·
            refine ⟨288890099194855926110593571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192593399463237284073729047 288890099194855926110593571)
            ·
              refine ⟨433335148792283889165890357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288890099194855926110593571 433335148792283889165890357)
              ·
                refine ⟨40625170199276614609302221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433335148792283889165890357 40625170199276614609302221)
                ·
                  refine ⟨15234438824728730478488333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40625170199276614609302221 15234438824728730478488333)
                  ·
                    refine ⟨5712914559273273929433125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15234438824728730478488333 5712914559273273929433125)
                    ·
                      refine ⟨1071171479863738861768711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5712914559273273929433125 1071171479863738861768711)
                      ·
                        rfl

theorem cell23_2086099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_2086099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086099 prefixEnd_2086099 := by exact prefixLift 2086099
  have htrace : WordTrace (prefixWord ++ tailWord_2086099) baseStart_2086099 baseEnd_2086099 := by
    simpa [prefixWord, tailWord_2086099, baseEnd_2086099] using wordTrace_append hprefix tailTrace_2086099
  have hstable : (prefixWord ++ tailWord_2086099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086099).length < 2 ^ (prefixWord ++ tailWord_2086099).sum := by decide
  have hdescent : baseEnd_2086099 < baseStart_2086099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086113 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2086113 : Nat := 118140960795 + 2086113 * 2 ^ 59
def prefixEnd_2086113 : Nat := 4983230072969 + 3 ^ 40 * 2086113 * 2
def baseEnd_2086113 : Nat := 357059556197633935664549

theorem tailTrace_2086113 : CollatzResearch.WordTrace tailWord_2086113 prefixEnd_2086113 357059556197633935664549 := by
  unfold tailWord_2086113
  simp only [CollatzResearch.WordTrace]
  refine ⟨76086791891376355580630993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50724527927584237053753995 76086791891376355580630993)
  ·
    refine ⟨57065093918532266685473245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76086791891376355580630993 57065093918532266685473245)
    ·
      refine ⟨21399410219449600007052467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57065093918532266685473245 21399410219449600007052467)
      ·
        refine ⟨32099115329174400010578701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21399410219449600007052467 32099115329174400010578701)
        ·
          refine ⟨12037168248440400003967013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32099115329174400010578701 12037168248440400003967013)
          ·
            refine ⟨2256969046582575000743815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12037168248440400003967013 2256969046582575000743815)
            ·
              refine ⟨3385453569873862501115723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256969046582575000743815 3385453569873862501115723)
              ·
                refine ⟨5078180354810793751673585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385453569873862501115723 5078180354810793751673585)
                ·
                  refine ⟨3808635266108095313755189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5078180354810793751673585 3808635266108095313755189)
                  ·
                    refine ⟨357059556197633935664549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3808635266108095313755189 357059556197633935664549)
                    ·
                      rfl

theorem cell23_2086113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2086113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086113 prefixEnd_2086113 := by exact prefixLift 2086113
  have htrace : WordTrace (prefixWord ++ tailWord_2086113) baseStart_2086113 baseEnd_2086113 := by
    simpa [prefixWord, tailWord_2086113, baseEnd_2086113] using wordTrace_append hprefix tailTrace_2086113
  have hstable : (prefixWord ++ tailWord_2086113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086113).length < 2 ^ (prefixWord ++ tailWord_2086113).sum := by decide
  have hdescent : baseEnd_2086113 < baseStart_2086113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086143 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 3, 4]
def baseStart_2086143 : Nat := 118140960795 + 2086143 * 2 ^ 59
def prefixEnd_2086143 : Nat := 4983230072969 + 3 ^ 40 * 2086143 * 2
def baseEnd_2086143 : Nat := 357064691004178896539503

theorem tailTrace_2086143 : CollatzResearch.WordTrace tailWord_2086143 prefixEnd_2086143 357064691004178896539503 := by
  unfold tailWord_2086143
  simp only [CollatzResearch.WordTrace]
  refine ⟨76087886081267670704223083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50725257387511780469482055 76087886081267670704223083)
  ·
    refine ⟨114131829121901506056334625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76087886081267670704223083 114131829121901506056334625)
    ·
      refine ⟨85598871841426129542250969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114131829121901506056334625 85598871841426129542250969)
      ·
        refine ⟨64199153881069597156688227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85598871841426129542250969 64199153881069597156688227)
        ·
          refine ⟨96298730821604395735032341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64199153881069597156688227 96298730821604395735032341)
          ·
            refine ⟨4514003007262706050079641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96298730821604395735032341 4514003007262706050079641)
            ·
              refine ⟨3385502255447029537559731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4514003007262706050079641 3385502255447029537559731)
              ·
                refine ⟨5078253383170544306339597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385502255447029537559731 5078253383170544306339597)
                ·
                  refine ⟨1904345018688954114877349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5078253383170544306339597 1904345018688954114877349)
                  ·
                    refine ⟨357064691004178896539503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1904345018688954114877349 357064691004178896539503)
                    ·
                      rfl

theorem cell23_2086143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_2086143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086143 prefixEnd_2086143 := by exact prefixLift 2086143
  have htrace : WordTrace (prefixWord ++ tailWord_2086143) baseStart_2086143 baseEnd_2086143 := by
    simpa [prefixWord, tailWord_2086143, baseEnd_2086143] using wordTrace_append hprefix tailTrace_2086143
  have hstable : (prefixWord ++ tailWord_2086143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086143).length < 2 ^ (prefixWord ++ tailWord_2086143).sum := by decide
  have hdescent : baseEnd_2086143 < baseStart_2086143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086169 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_2086169 : Nat := 118140960795 + 2086169 * 2 ^ 59
def prefixEnd_2086169 : Nat := 4983230072969 + 3 ^ 40 * 2086169 * 2
def baseEnd_2086169 : Nat := 357069141169851195964463

theorem tailTrace_2086169 : CollatzResearch.WordTrace tailWord_2086169 prefixEnd_2086169 357069141169851195964463 := by
  unfold tailWord_2086169
  simp only [CollatzResearch.WordTrace]
  refine ⟨76088834379173477144669561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50725889586115651429779707 76088834379173477144669561)
  ·
    refine ⟨57066625784380107858502171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76088834379173477144669561 57066625784380107858502171)
    ·
      refine ⟨85599938676570161787753257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57066625784380107858502171 85599938676570161787753257)
      ·
        refine ⟨64199954007427621340814943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85599938676570161787753257 64199954007427621340814943)
        ·
          refine ⟨96299931011141432011222415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64199954007427621340814943 96299931011141432011222415)
          ·
            refine ⟨144449896516712148016833623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96299931011141432011222415 144449896516712148016833623)
            ·
              refine ⟨216674844775068222025250435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144449896516712148016833623 216674844775068222025250435)
              ·
                refine ⟨325012267162602333037875653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216674844775068222025250435 325012267162602333037875653)
                ·
                  refine ⟨60939800092987937444601685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325012267162602333037875653 60939800092987937444601685)
                  ·
                    refine ⟨357069141169851195964463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60939800092987937444601685 357069141169851195964463)
                    ·
                      rfl

theorem cell23_2086169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_2086169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086169 prefixEnd_2086169 := by exact prefixLift 2086169
  have htrace : WordTrace (prefixWord ++ tailWord_2086169) baseStart_2086169 baseEnd_2086169 := by
    simpa [prefixWord, tailWord_2086169, baseEnd_2086169] using wordTrace_append hprefix tailTrace_2086169
  have hstable : (prefixWord ++ tailWord_2086169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086169).length < 2 ^ (prefixWord ++ tailWord_2086169).sum := by decide
  have hdescent : baseEnd_2086169 < baseStart_2086169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086216 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_2086216 : Nat := 118140960795 + 2086216 * 2 ^ 59
def prefixEnd_2086216 : Nat := 4983230072969 + 3 ^ 40 * 2086216 * 2
def baseEnd_2086216 : Nat := 357077185700104968001891

theorem tailTrace_2086216 : CollatzResearch.WordTrace tailWord_2086216 prefixEnd_2086216 357077185700104968001891 := by
  unfold tailWord_2086216
  simp only [CollatzResearch.WordTrace]
  refine ⟨38045274305001602085815251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50727032406668802781087001 38045274305001602085815251)
  ·
    refine ⟨57067911457502403128722877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38045274305001602085815251 57067911457502403128722877)
    ·
      refine ⟨21400466796563401173271079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57067911457502403128722877 21400466796563401173271079)
      ·
        refine ⟨32100700194845101759906619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21400466796563401173271079 32100700194845101759906619)
        ·
          refine ⟨48151050292267652639859929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32100700194845101759906619 48151050292267652639859929)
          ·
            refine ⟨36113287719200739479894947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48151050292267652639859929 36113287719200739479894947)
            ·
              refine ⟨54169931578801109219842421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36113287719200739479894947 54169931578801109219842421)
              ·
                refine ⟨5078431085512603989360227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54169931578801109219842421 5078431085512603989360227)
                ·
                  refine ⟨7617646628268905984040341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078431085512603989360227 7617646628268905984040341)
                  ·
                    refine ⟨357077185700104968001891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7617646628268905984040341 357077185700104968001891)
                    ·
                      rfl

theorem cell23_2086216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_2086216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086216 prefixEnd_2086216 := by exact prefixLift 2086216
  have htrace : WordTrace (prefixWord ++ tailWord_2086216) baseStart_2086216 baseEnd_2086216 := by
    simpa [prefixWord, tailWord_2086216, baseEnd_2086216] using wordTrace_append hprefix tailTrace_2086216
  have hstable : (prefixWord ++ tailWord_2086216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086216).length < 2 ^ (prefixWord ++ tailWord_2086216).sum := by decide
  have hdescent : baseEnd_2086216 < baseStart_2086216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086220 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_2086220 : Nat := 118140960795 + 2086220 * 2 ^ 59
def prefixEnd_2086220 : Nat := 4983230072969 + 3 ^ 40 * 2086220 * 2
def baseEnd_2086220 : Nat := 357077870340977629451885

theorem tailTrace_2086220 : CollatzResearch.WordTrace tailWord_2086220 prefixEnd_2086220 357077870340977629451885 := by
  unfold tailWord_2086220
  simp only [CollatzResearch.WordTrace]
  refine ⟨38045347250994356427388057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50727129667992475236517409 38045347250994356427388057)
  ·
    refine ⟨28534010438245767320541043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38045347250994356427388057 28534010438245767320541043)
    ·
      refine ⟨42801015657368650980811565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28534010438245767320541043 42801015657368650980811565)
      ·
        refine ⟨16050380871513244117804337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42801015657368650980811565 16050380871513244117804337)
        ·
          refine ⟨12037785653634933088353253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16050380871513244117804337 12037785653634933088353253)
          ·
            refine ⟨2257084810056549954066235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12037785653634933088353253 2257084810056549954066235)
            ·
              refine ⟨3385627215084824931099353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257084810056549954066235 3385627215084824931099353)
              ·
                refine ⟨2539220411313618698324515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385627215084824931099353 2539220411313618698324515)
                ·
                  refine ⟨3808830616970428047486773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539220411313618698324515 3808830616970428047486773)
                  ·
                    refine ⟨357077870340977629451885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3808830616970428047486773 357077870340977629451885)
                    ·
                      rfl

theorem cell23_2086220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_2086220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086220 prefixEnd_2086220 := by exact prefixLift 2086220
  have htrace : WordTrace (prefixWord ++ tailWord_2086220) baseStart_2086220 baseEnd_2086220 := by
    simpa [prefixWord, tailWord_2086220, baseEnd_2086220] using wordTrace_append hprefix tailTrace_2086220
  have hstable : (prefixWord ++ tailWord_2086220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086220).length < 2 ^ (prefixWord ++ tailWord_2086220).sum := by decide
  have hdescent : baseEnd_2086220 < baseStart_2086220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086243 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2086243 : Nat := 118140960795 + 2086243 * 2 ^ 59
def prefixEnd_2086243 : Nat := 4983230072969 + 3 ^ 40 * 2086243 * 2
def baseEnd_2086243 : Nat := 1071245421077986298368049

theorem tailTrace_2086243 : CollatzResearch.WordTrace tailWord_2086243 prefixEnd_2086243 1071245421077986298368049 := by
  unfold tailWord_2086243
  simp only [CollatzResearch.WordTrace]
  refine ⟨76091533380905387782863383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50727688920603591855242255 76091533380905387782863383)
  ·
    refine ⟨114137300071358081674295075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76091533380905387782863383 114137300071358081674295075)
    ·
      refine ⟨171205950107037122511442613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114137300071358081674295075 171205950107037122511442613)
      ·
        refine ⟨16050557822534730235447745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171205950107037122511442613 16050557822534730235447745)
        ·
          refine ⟨12037918366901047676585809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16050557822534730235447745 12037918366901047676585809)
          ·
            refine ⟨9028438775175785757439357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12037918366901047676585809 9028438775175785757439357)
            ·
              refine ⟨3385664540690919659039759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9028438775175785757439357 3385664540690919659039759)
              ·
                refine ⟨5078496811036379488559639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385664540690919659039759 5078496811036379488559639)
                ·
                  refine ⟨7617745216554569232839459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078496811036379488559639 7617745216554569232839459)
                  ·
                    refine ⟨11426617824831853849259189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7617745216554569232839459 11426617824831853849259189)
                    ·
                      refine ⟨1071245421077986298368049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11426617824831853849259189 1071245421077986298368049)
                      ·
                        rfl

theorem cell23_2086243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2086243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086243 prefixEnd_2086243 := by exact prefixLift 2086243
  have htrace : WordTrace (prefixWord ++ tailWord_2086243) baseStart_2086243 baseEnd_2086243 := by
    simpa [prefixWord, tailWord_2086243, baseEnd_2086243] using wordTrace_append hprefix tailTrace_2086243
  have hstable : (prefixWord ++ tailWord_2086243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086243).length < 2 ^ (prefixWord ++ tailWord_2086243).sum := by decide
  have hdescent : baseEnd_2086243 < baseStart_2086243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086274 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2086274 : Nat := 118140960795 + 2086274 * 2 ^ 59
def prefixEnd_2086274 : Nat := 4983230072969 + 3 ^ 40 * 2086274 * 2
def baseEnd_2086274 : Nat := 1071261338978275677080407

theorem tailTrace_2086274 : CollatzResearch.WordTrace tailWord_2086274 prefixEnd_2086274 1071261338978275677080407 := by
  unfold tailWord_2086274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19023166010948270019310469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50728442695862053384827917 19023166010948270019310469)
  ·
    refine ⟨3566843627052800628620713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19023166010948270019310469 3566843627052800628620713)
    ·
      refine ⟨2675132720289600471465535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3566843627052800628620713 2675132720289600471465535)
      ·
        refine ⟨4012699080434400707198303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675132720289600471465535 4012699080434400707198303)
        ·
          refine ⟨6019048620651601060797455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012699080434400707198303 6019048620651601060797455)
          ·
            refine ⟨9028572930977401591196183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019048620651601060797455 9028572930977401591196183)
            ·
              refine ⟨13542859396466102386794275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028572930977401591196183 13542859396466102386794275)
              ·
                refine ⟨20314289094699153580191413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13542859396466102386794275 20314289094699153580191413)
                ·
                  refine ⟨1904464602628045648142945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20314289094699153580191413 1904464602628045648142945)
                  ·
                    refine ⟨1428348451971034236107209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1904464602628045648142945 1428348451971034236107209)
                    ·
                      refine ⟨1071261338978275677080407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428348451971034236107209 1071261338978275677080407)
                      ·
                        rfl

theorem cell23_2086274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2086274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086274 prefixEnd_2086274 := by exact prefixLift 2086274
  have htrace : WordTrace (prefixWord ++ tailWord_2086274) baseStart_2086274 baseEnd_2086274 := by
    simpa [prefixWord, tailWord_2086274, baseEnd_2086274] using wordTrace_append hprefix tailTrace_2086274
  have hstable : (prefixWord ++ tailWord_2086274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086274).length < 2 ^ (prefixWord ++ tailWord_2086274).sum := by decide
  have hdescent : baseEnd_2086274 < baseStart_2086274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086313 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 8, 2]
def baseStart_2086313 : Nat := 118140960795 + 2086313 * 2 ^ 59
def prefixEnd_2086313 : Nat := 4983230072969 + 3 ^ 40 * 2086313 * 2
def baseEnd_2086313 : Nat := 1071281364723801024492727

theorem tailTrace_2086313 : CollatzResearch.WordTrace tailWord_2086313 prefixEnd_2086313 1071281364723801024492727 := by
  unfold tailWord_2086313
  simp only [CollatzResearch.WordTrace]
  refine ⟨76094086490651789737911593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50729390993767859825274395 76094086490651789737911593)
  ·
    refine ⟨57070564867988842303433695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76094086490651789737911593 57070564867988842303433695)
    ·
      refine ⟨85605847301983263455150543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57070564867988842303433695 85605847301983263455150543)
      ·
        refine ⟨128408770952974895182725815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85605847301983263455150543 128408770952974895182725815)
        ·
          refine ⟨192613156429462342774088723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128408770952974895182725815 192613156429462342774088723)
          ·
            refine ⟨288919734644193514161133085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192613156429462342774088723 288919734644193514161133085)
            ·
              refine ⟨108344900491572567810424907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288919734644193514161133085 108344900491572567810424907)
              ·
                refine ⟨162517350737358851715637361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108344900491572567810424907 162517350737358851715637361)
                ·
                  refine ⟨121888013053019138786728021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162517350737358851715637361 121888013053019138786728021)
                  ·
                    refine ⟨1428375152965068032656969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121888013053019138786728021 1428375152965068032656969)
                    ·
                      refine ⟨1071281364723801024492727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428375152965068032656969 1071281364723801024492727)
                      ·
                        rfl

theorem cell23_2086313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 8, 2].length) (baseStart_2086313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086313 prefixEnd_2086313 := by exact prefixLift 2086313
  have htrace : WordTrace (prefixWord ++ tailWord_2086313) baseStart_2086313 baseEnd_2086313 := by
    simpa [prefixWord, tailWord_2086313, baseEnd_2086313] using wordTrace_append hprefix tailTrace_2086313
  have hstable : (prefixWord ++ tailWord_2086313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086313).length < 2 ^ (prefixWord ++ tailWord_2086313).sum := by decide
  have hdescent : baseEnd_2086313 < baseStart_2086313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086333 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2086333 : Nat := 118140960795 + 2086333 * 2 ^ 59
def prefixEnd_2086333 : Nat := 4983230072969 + 3 ^ 40 * 2086333 * 2
def baseEnd_2086333 : Nat := 1071291634336890946242635

theorem tailTrace_2086333 : CollatzResearch.WordTrace tailWord_2086333 prefixEnd_2086333 1071291634336890946242635 := by
  unfold tailWord_2086333
  simp only [CollatzResearch.WordTrace]
  refine ⟨76094815950579333153639653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50729877300386222102426435 76094815950579333153639653)
  ·
    refine ⟨14267777990733624966307435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76094815950579333153639653 14267777990733624966307435)
    ·
      refine ⟨21401666986100437449461153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14267777990733624966307435 21401666986100437449461153)
      ·
        refine ⟨16051250239575328087095865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21401666986100437449461153 16051250239575328087095865)
        ·
          refine ⟨12038437679681496065321899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16051250239575328087095865 12038437679681496065321899)
          ·
            refine ⟨18057656519522244097982849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12038437679681496065321899 18057656519522244097982849)
            ·
              refine ⟨13543242389641683073487137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18057656519522244097982849 13543242389641683073487137)
              ·
                refine ⟨10157431792231262305115353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13543242389641683073487137 10157431792231262305115353)
                ·
                  refine ⟨7618073844173446728836515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10157431792231262305115353 7618073844173446728836515)
                  ·
                    refine ⟨11427110766260170093254773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7618073844173446728836515 11427110766260170093254773)
                    ·
                      refine ⟨1071291634336890946242635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11427110766260170093254773 1071291634336890946242635)
                      ·
                        rfl

theorem cell23_2086333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2086333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086333 prefixEnd_2086333 := by exact prefixLift 2086333
  have htrace : WordTrace (prefixWord ++ tailWord_2086333) baseStart_2086333 baseEnd_2086333 := by
    simpa [prefixWord, tailWord_2086333, baseEnd_2086333] using wordTrace_append hprefix tailTrace_2086333
  have hstable : (prefixWord ++ tailWord_2086333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086333).length < 2 ^ (prefixWord ++ tailWord_2086333).sum := by decide
  have hdescent : baseEnd_2086333 < baseStart_2086333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086381 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2086381 : Nat := 118140960795 + 2086381 * 2 ^ 59
def prefixEnd_2086381 : Nat := 4983230072969 + 3 ^ 40 * 2086381 * 2
def baseEnd_2086381 : Nat := 1071316281408306758442415

theorem tailTrace_2086381 : CollatzResearch.WordTrace tailWord_2086381 prefixEnd_2086381 1071316281408306758442415 := by
  unfold tailWord_2086381
  simp only [CollatzResearch.WordTrace]
  refine ⟨76096566654405437351386997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50731044436270291567591331 76096566654405437351386997)
  ·
    refine ⟨7134053123850509751692531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76096566654405437351386997 7134053123850509751692531)
    ·
      refine ⟨10701079685775764627538797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134053123850509751692531 10701079685775764627538797)
      ·
        refine ⟨4012904882165911735327049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10701079685775764627538797 4012904882165911735327049)
        ·
          refine ⟨3009678661624433801495287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4012904882165911735327049 3009678661624433801495287)
          ·
            refine ⟨4514517992436650702242931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009678661624433801495287 4514517992436650702242931)
            ·
              refine ⟨6771776988654976053364397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514517992436650702242931 6771776988654976053364397)
              ·
                refine ⟨2539416370745616020011649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6771776988654976053364397 2539416370745616020011649)
                ·
                  refine ⟨1904562278059212015008737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539416370745616020011649 1904562278059212015008737)
                  ·
                    refine ⟨1428421708544409011256553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1904562278059212015008737 1428421708544409011256553)
                    ·
                      refine ⟨1071316281408306758442415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428421708544409011256553 1071316281408306758442415)
                      ·
                        rfl

theorem cell23_2086381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2086381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086381 prefixEnd_2086381 := by exact prefixLift 2086381
  have htrace : WordTrace (prefixWord ++ tailWord_2086381) baseStart_2086381 baseEnd_2086381 := by
    simpa [prefixWord, tailWord_2086381, baseEnd_2086381] using wordTrace_append hprefix tailTrace_2086381
  have hstable : (prefixWord ++ tailWord_2086381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086381).length < 2 ^ (prefixWord ++ tailWord_2086381).sum := by decide
  have hdescent : baseEnd_2086381 < baseStart_2086381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086457 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2086457 : Nat := 118140960795 + 2086457 * 2 ^ 59
def prefixEnd_2086457 : Nat := 4983230072969 + 3 ^ 40 * 2086457 * 2
def baseEnd_2086457 : Nat := 1071355305938048461092065

theorem tailTrace_2086457 : CollatzResearch.WordTrace tailWord_2086457 prefixEnd_2086457 1071355305938048461092065 := by
  unfold tailWord_2086457
  simp only [CollatzResearch.WordTrace]
  refine ⟨76099338602130102331153625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50732892401420068220769083 76099338602130102331153625)
  ·
    refine ⟨57074503951597576748365219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76099338602130102331153625 57074503951597576748365219)
    ·
      refine ⟨85611755927396365122547829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57074503951597576748365219 85611755927396365122547829)
      ·
        refine ⟨8026102118193409230238859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85611755927396365122547829 8026102118193409230238859)
        ·
          refine ⟨12039153177290113845358289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8026102118193409230238859 12039153177290113845358289)
          ·
            refine ⟨9029364882967585384018717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12039153177290113845358289 9029364882967585384018717)
            ·
              refine ⟨3386011831112844519007019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9029364882967585384018717 3386011831112844519007019)
              ·
                refine ⟨5079017746669266778510529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386011831112844519007019 5079017746669266778510529)
                ·
                  refine ⟨3809263310001950083882897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079017746669266778510529 3809263310001950083882897)
                  ·
                    refine ⟨2856947482501462562912173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3809263310001950083882897 2856947482501462562912173)
                    ·
                      refine ⟨1071355305938048461092065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2856947482501462562912173 1071355305938048461092065)
                      ·
                        rfl

theorem cell23_2086457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2086457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086457 prefixEnd_2086457 := by exact prefixLift 2086457
  have htrace : WordTrace (prefixWord ++ tailWord_2086457) baseStart_2086457 baseEnd_2086457 := by
    simpa [prefixWord, tailWord_2086457, baseEnd_2086457] using wordTrace_append hprefix tailTrace_2086457
  have hstable : (prefixWord ++ tailWord_2086457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086457).length < 2 ^ (prefixWord ++ tailWord_2086457).sum := by decide
  have hdescent : baseEnd_2086457 < baseStart_2086457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086477 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2086477 : Nat := 118140960795 + 2086477 * 2 ^ 59
def prefixEnd_2086477 : Nat := 4983230072969 + 3 ^ 40 * 2086477 * 2
def baseEnd_2086477 : Nat := 119040619505682042537997

theorem tailTrace_2086477 : CollatzResearch.WordTrace tailWord_2086477 prefixEnd_2086477 119040619505682042537997 := by
  unfold tailWord_2086477
  simp only [CollatzResearch.WordTrace]
  refine ⟨76100068062057645746881685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50733378708038430497921123 76100068062057645746881685)
  ·
    refine ⟨3567190690408952144385079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76100068062057645746881685 3567190690408952144385079)
    ·
      refine ⟨5350786035613428216577619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567190690408952144385079 5350786035613428216577619)
      ·
        refine ⟨8026179053420142324866429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350786035613428216577619 8026179053420142324866429)
        ·
          refine ⟨3009817145032553371824911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8026179053420142324866429 3009817145032553371824911)
          ·
            refine ⟨4514725717548830057737367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009817145032553371824911 4514725717548830057737367)
            ·
              refine ⟨6772088576323245086606051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514725717548830057737367 6772088576323245086606051)
              ·
                refine ⟨10158132864484867629909077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772088576323245086606051 10158132864484867629909077)
                ·
                  refine ⟨119040619505682042537997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10158132864484867629909077 119040619505682042537997)
                  ·
                    rfl

theorem cell23_2086477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2086477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086477 prefixEnd_2086477 := by exact prefixLift 2086477
  have htrace : WordTrace (prefixWord ++ tailWord_2086477) baseStart_2086477 baseEnd_2086477 := by
    simpa [prefixWord, tailWord_2086477, baseEnd_2086477] using wordTrace_append hprefix tailTrace_2086477
  have hstable : (prefixWord ++ tailWord_2086477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086477).length < 2 ^ (prefixWord ++ tailWord_2086477).sum := by decide
  have hdescent : baseEnd_2086477 < baseStart_2086477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086487 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_2086487 : Nat := 118140960795 + 2086487 * 2 ^ 59
def prefixEnd_2086487 : Nat := 4983230072969 + 3 ^ 40 * 2086487 * 2
def baseEnd_2086487 : Nat := 1071370710357683343716927

theorem tailTrace_2086487 : CollatzResearch.WordTrace tailWord_2086487 prefixEnd_2086487 1071370710357683343716927 := by
  unfold tailWord_2086487
  simp only [CollatzResearch.WordTrace]
  refine ⟨76100432792021417454745715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50733621861347611636497143 76100432792021417454745715)
  ·
    refine ⟨114150649188032126182118573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76100432792021417454745715 114150649188032126182118573)
    ·
      refine ⟨42806493445512047318294465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114150649188032126182118573 42806493445512047318294465)
      ·
        refine ⟨32104870084134035488720849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42806493445512047318294465 32104870084134035488720849)
        ·
          refine ⟨24078652563100526616540637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32104870084134035488720849 24078652563100526616540637)
          ·
            refine ⟨9029494711162697481202739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24078652563100526616540637 9029494711162697481202739)
            ·
              refine ⟨13544242066744046221804109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029494711162697481202739 13544242066744046221804109)
              ·
                refine ⟨5079090775029017333176541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13544242066744046221804109 5079090775029017333176541)
                ·
                  refine ⟨1904659040635881499941203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5079090775029017333176541 1904659040635881499941203)
                  ·
                    refine ⟨2856988560953822249911805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1904659040635881499941203 2856988560953822249911805)
                    ·
                      refine ⟨1071370710357683343716927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2856988560953822249911805 1071370710357683343716927)
                      ·
                        rfl

theorem cell23_2086487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_2086487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086487 prefixEnd_2086487 := by exact prefixLift 2086487
  have htrace : WordTrace (prefixWord ++ tailWord_2086487) baseStart_2086487 baseEnd_2086487 := by
    simpa [prefixWord, tailWord_2086487, baseEnd_2086487] using wordTrace_append hprefix tailTrace_2086487
  have hstable : (prefixWord ++ tailWord_2086487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086487).length < 2 ^ (prefixWord ++ tailWord_2086487).sum := by decide
  have hdescent : baseEnd_2086487 < baseStart_2086487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086504 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2086504 : Nat := 118140960795 + 2086504 * 2 ^ 59
def prefixEnd_2086504 : Nat := 4983230072969 + 3 ^ 40 * 2086504 * 2
def baseEnd_2086504 : Nat := 1071379439528809777204349

theorem tailTrace_2086504 : CollatzResearch.WordTrace tailWord_2086504 prefixEnd_2086504 1071379439528809777204349 := by
  unfold tailWord_2086504
  simp only [CollatzResearch.WordTrace]
  refine ⟨38050526416479914679057283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50734035221973219572076377 38050526416479914679057283)
  ·
    refine ⟨57075789624719872018585925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38050526416479914679057283 57075789624719872018585925)
    ·
      refine ⟨10701710554634976003484861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57075789624719872018585925 10701710554634976003484861)
      ·
        refine ⟨4013141457988116001306823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10701710554634976003484861 4013141457988116001306823)
        ·
          refine ⟨6019712186982174001960235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013141457988116001306823 6019712186982174001960235)
          ·
            refine ⟨9029568280473261002940353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019712186982174001960235 9029568280473261002940353)
            ·
              refine ⟨6772176210354945752205265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9029568280473261002940353 6772176210354945752205265)
              ·
                refine ⟨5079132157766209314153949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6772176210354945752205265 5079132157766209314153949)
                ·
                  refine ⟨1904674559162328492807731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5079132157766209314153949 1904674559162328492807731)
                  ·
                    refine ⟨2857011838743492739211597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1904674559162328492807731 2857011838743492739211597)
                    ·
                      refine ⟨1071379439528809777204349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857011838743492739211597 1071379439528809777204349)
                      ·
                        rfl

theorem cell23_2086504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2086504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086504 prefixEnd_2086504 := by exact prefixLift 2086504
  have htrace : WordTrace (prefixWord ++ tailWord_2086504) baseStart_2086504 baseEnd_2086504 := by
    simpa [prefixWord, tailWord_2086504, baseEnd_2086504] using wordTrace_append hprefix tailTrace_2086504
  have hstable : (prefixWord ++ tailWord_2086504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086504).length < 2 ^ (prefixWord ++ tailWord_2086504).sum := by decide
  have hdescent : baseEnd_2086504 < baseStart_2086504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086538 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_2086538 : Nat := 118140960795 + 2086538 * 2 ^ 59
def prefixEnd_2086538 : Nat := 4983230072969 + 3 ^ 40 * 2086538 * 2
def baseEnd_2086538 : Nat := 1071396897871062644179193

theorem tailTrace_2086538 : CollatzResearch.WordTrace tailWord_2086538 prefixEnd_2086538 1071396897871062644179193 := by
  unfold tailWord_2086538
  simp only [CollatzResearch.WordTrace]
  refine ⟨19025573228709163291213067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50734861943224435443234845 19025573228709163291213067)
  ·
    refine ⟨28538359843063744936819601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19025573228709163291213067 28538359843063744936819601)
    ·
      refine ⟨21403769882297808702614701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28538359843063744936819601 21403769882297808702614701)
      ·
        refine ⟨8026413705861678263480513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21403769882297808702614701 8026413705861678263480513)
        ·
          refine ⟨6019810279396258697610385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8026413705861678263480513 6019810279396258697610385)
          ·
            refine ⟨4514857709547194023207789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019810279396258697610385 4514857709547194023207789)
            ·
              refine ⟨1693071641080197758702921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4514857709547194023207789 1693071641080197758702921)
              ·
                refine ⟨1269803730810148319027191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693071641080197758702921 1269803730810148319027191)
                ·
                  refine ⟨1904705596215222478540787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269803730810148319027191 1904705596215222478540787)
                  ·
                    refine ⟨2857058394322833717811181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1904705596215222478540787 2857058394322833717811181)
                    ·
                      refine ⟨1071396897871062644179193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857058394322833717811181 1071396897871062644179193)
                      ·
                        rfl

theorem cell23_2086538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_2086538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086538 prefixEnd_2086538 := by exact prefixLift 2086538
  have htrace : WordTrace (prefixWord ++ tailWord_2086538) baseStart_2086538 baseEnd_2086538 := by
    simpa [prefixWord, tailWord_2086538, baseEnd_2086538] using wordTrace_append hprefix tailTrace_2086538
  have hstable : (prefixWord ++ tailWord_2086538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086538).length < 2 ^ (prefixWord ++ tailWord_2086538).sum := by decide
  have hdescent : baseEnd_2086538 < baseStart_2086538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086543 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_2086543 : Nat := 118140960795 + 2086543 * 2 ^ 59
def prefixEnd_2086543 : Nat := 4983230072969 + 3 ^ 40 * 2086543 * 2
def baseEnd_2086543 : Nat := 1071399465274335124616669

theorem tailTrace_2086543 : CollatzResearch.WordTrace tailWord_2086543 prefixEnd_2086543 1071399465274335124616669 := by
  unfold tailWord_2086543
  simp only [CollatzResearch.WordTrace]
  refine ⟨76102475279818539018784283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50734983519879026012522855 76102475279818539018784283)
  ·
    refine ⟨114153712919727808528176425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76102475279818539018784283 114153712919727808528176425)
    ·
      refine ⟨85615284689795856396132319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114153712919727808528176425 85615284689795856396132319)
      ·
        refine ⟨128422927034693784594198479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85615284689795856396132319 128422927034693784594198479)
        ·
          refine ⟨192634390552040676891297719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128422927034693784594198479 192634390552040676891297719)
          ·
            refine ⟨288951585828061015336946579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192634390552040676891297719 288951585828061015336946579)
            ·
              refine ⟨433427378742091523005419869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288951585828061015336946579 433427378742091523005419869)
              ·
                refine ⟨162535267028284321127032451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433427378742091523005419869 162535267028284321127032451)
                ·
                  refine ⟨243802900542426481690548677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162535267028284321127032451 243802900542426481690548677)
                  ·
                    refine ⟨45713043851704965316977877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243802900542426481690548677 45713043851704965316977877)
                    ·
                      refine ⟨1071399465274335124616669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45713043851704965316977877 1071399465274335124616669)
                      ·
                        rfl

theorem cell23_2086543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_2086543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086543 prefixEnd_2086543 := by exact prefixLift 2086543
  have htrace : WordTrace (prefixWord ++ tailWord_2086543) baseStart_2086543 baseEnd_2086543 := by
    simpa [prefixWord, tailWord_2086543, baseEnd_2086543] using wordTrace_append hprefix tailTrace_2086543
  have hstable : (prefixWord ++ tailWord_2086543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086543).length < 2 ^ (prefixWord ++ tailWord_2086543).sum := by decide
  have hdescent : baseEnd_2086543 < baseStart_2086543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086564 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_2086564 : Nat := 118140960795 + 2086564 * 2 ^ 59
def prefixEnd_2086564 : Nat := 4983230072969 + 3 ^ 40 * 2086564 * 2
def baseEnd_2086564 : Nat := 1071410248368079542454073

theorem tailTrace_2086564 : CollatzResearch.WordTrace tailWord_2086564 prefixEnd_2086564 1071410248368079542454073 := by
  unfold tailWord_2086564
  simp only [CollatzResearch.WordTrace]
  refine ⟨38051620606371229802649373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50735494141828306403532497 38051620606371229802649373)
  ·
    refine ⟨14269357727389211175993515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38051620606371229802649373 14269357727389211175993515)
    ·
      refine ⟨21404036591083816763990273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14269357727389211175993515 21404036591083816763990273)
      ·
        refine ⟨16053027443312862572992705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21404036591083816763990273 16053027443312862572992705)
        ·
          refine ⟨12039770582484646929744529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16053027443312862572992705 12039770582484646929744529)
          ·
            refine ⟨9029827936863485197308397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12039770582484646929744529 9029827936863485197308397)
            ·
              refine ⟨3386185476323806948990649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9029827936863485197308397 3386185476323806948990649)
              ·
                refine ⟨2539639107242855211742987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386185476323806948990649 2539639107242855211742987)
                ·
                  refine ⟨3809458660864282817614481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539639107242855211742987 3809458660864282817614481)
                  ·
                    refine ⟨2857093995648212113210861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3809458660864282817614481 2857093995648212113210861)
                    ·
                      refine ⟨1071410248368079542454073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857093995648212113210861 1071410248368079542454073)
                      ·
                        rfl

theorem cell23_2086564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_2086564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086564 prefixEnd_2086564 := by exact prefixLift 2086564
  have htrace : WordTrace (prefixWord ++ tailWord_2086564) baseStart_2086564 baseEnd_2086564 := by
    simpa [prefixWord, tailWord_2086564, baseEnd_2086564] using wordTrace_append hprefix tailTrace_2086564
  have hstable : (prefixWord ++ tailWord_2086564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086564).length < 2 ^ (prefixWord ++ tailWord_2086564).sum := by decide
  have hdescent : baseEnd_2086564 < baseStart_2086564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086581 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2086581 : Nat := 118140960795 + 2086581 * 2 ^ 59
def prefixEnd_2086581 : Nat := 4983230072969 + 3 ^ 40 * 2086581 * 2
def baseEnd_2086581 : Nat := 1071418977539205975941495

theorem tailTrace_2086581 : CollatzResearch.WordTrace tailWord_2086581 prefixEnd_2086581 1071418977539205975941495 := by
  unfold tailWord_2086581
  simp only [CollatzResearch.WordTrace]
  refine ⟨76103861253680871508667597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50735907502453914339111731 76103861253680871508667597)
  ·
    refine ⟨28538947970130326815750349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76103861253680871508667597 28538947970130326815750349)
    ·
      refine ⟨10702105488798872555906381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28538947970130326815750349 10702105488798872555906381)
      ·
        refine ⟨4013289558299577208464893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10702105488798872555906381 4013289558299577208464893)
        ·
          refine ⟨1504983584362341453174335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4013289558299577208464893 1504983584362341453174335)
          ·
            refine ⟨2257475376543512179761503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504983584362341453174335 2257475376543512179761503)
            ·
              refine ⟨3386213064815268269642255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257475376543512179761503 3386213064815268269642255)
              ·
                refine ⟨5079319597222902404463383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386213064815268269642255 5079319597222902404463383)
                ·
                  refine ⟨7618979395834353606695075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079319597222902404463383 7618979395834353606695075)
                  ·
                    refine ⟨11428469093751530410042613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7618979395834353606695075 11428469093751530410042613)
                    ·
                      refine ⟨1071418977539205975941495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11428469093751530410042613 1071418977539205975941495)
                      ·
                        rfl

theorem cell23_2086581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2086581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086581 prefixEnd_2086581 := by exact prefixLift 2086581
  have htrace : WordTrace (prefixWord ++ tailWord_2086581) baseStart_2086581 baseEnd_2086581 := by
    simpa [prefixWord, tailWord_2086581, baseEnd_2086581] using wordTrace_append hprefix tailTrace_2086581
  have hstable : (prefixWord ++ tailWord_2086581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086581).length < 2 ^ (prefixWord ++ tailWord_2086581).sum := by decide
  have hdescent : baseEnd_2086581 < baseStart_2086581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086600 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2086600 : Nat := 118140960795 + 2086600 * 2 ^ 59
def prefixEnd_2086600 : Nat := 4983230072969 + 3 ^ 40 * 2086600 * 2
def baseEnd_2086600 : Nat := 1071428733671641401603907

theorem tailTrace_2086600 : CollatzResearch.WordTrace tailWord_2086600 prefixEnd_2086600 1071428733671641401603907 := by
  unfold tailWord_2086600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38052277120306018876804627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50736369493741358502406169 38052277120306018876804627)
  ·
    refine ⟨57078415680459028315206941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38052277120306018876804627 57078415680459028315206941)
    ·
      refine ⟨21404405880172135618202603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57078415680459028315206941 21404405880172135618202603)
      ·
        refine ⟨32106608820258203427303905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21404405880172135618202603 32106608820258203427303905)
        ·
          refine ⟨24079956615193652570477929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32106608820258203427303905 24079956615193652570477929)
          ·
            refine ⟨18059967461395239427858447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24079956615193652570477929 18059967461395239427858447)
            ·
              refine ⟨27089951192092859141787671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18059967461395239427858447 27089951192092859141787671)
              ·
                refine ⟨40634926788139288712681507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27089951192092859141787671 40634926788139288712681507)
                ·
                  refine ⟨60952390182208933069022261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40634926788139288712681507 60952390182208933069022261)
                  ·
                    refine ⟨5714286579582087475220837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60952390182208933069022261 5714286579582087475220837)
                    ·
                      refine ⟨1071428733671641401603907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5714286579582087475220837 1071428733671641401603907)
                      ·
                        rfl

theorem cell23_2086600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2086600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086600 prefixEnd_2086600 := by exact prefixLift 2086600
  have htrace : WordTrace (prefixWord ++ tailWord_2086600) baseStart_2086600 baseEnd_2086600 := by
    simpa [prefixWord, tailWord_2086600, baseEnd_2086600] using wordTrace_append hprefix tailTrace_2086600
  have hstable : (prefixWord ++ tailWord_2086600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086600).length < 2 ^ (prefixWord ++ tailWord_2086600).sum := by decide
  have hdescent : baseEnd_2086600 < baseStart_2086600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086634 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_2086634 : Nat := 118140960795 + 2086634 * 2 ^ 59
def prefixEnd_2086634 : Nat := 4983230072969 + 3 ^ 40 * 2086634 * 2
def baseEnd_2086634 : Nat := 1071446192013894268578751

theorem tailTrace_2086634 : CollatzResearch.WordTrace tailWord_2086634 prefixEnd_2086634 1071446192013894268578751 := by
  unfold tailWord_2086634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19026448580622215390086739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50737196214992574373564637 19026448580622215390086739)
  ·
    refine ⟨28539672870933323085130109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19026448580622215390086739 28539672870933323085130109)
    ·
      refine ⟨10702377326599996156923791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28539672870933323085130109 10702377326599996156923791)
      ·
        refine ⟨16053565989899994235385687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10702377326599996156923791 16053565989899994235385687)
        ·
          refine ⟨24080348984849991353078531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16053565989899994235385687 24080348984849991353078531)
          ·
            refine ⟨36120523477274987029617797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24080348984849991353078531 36120523477274987029617797)
            ·
              refine ⟨6772598151989060068053337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36120523477274987029617797 6772598151989060068053337)
              ·
                refine ⟨5079448613991795051040003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6772598151989060068053337 5079448613991795051040003)
                ·
                  refine ⟨7619172920987692576560005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079448613991795051040003 7619172920987692576560005)
                  ·
                    refine ⟨1428594922685192358105001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7619172920987692576560005 1428594922685192358105001)
                    ·
                      refine ⟨1071446192013894268578751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428594922685192358105001 1071446192013894268578751)
                      ·
                        rfl

theorem cell23_2086634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_2086634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086634 prefixEnd_2086634 := by exact prefixLift 2086634
  have htrace : WordTrace (prefixWord ++ tailWord_2086634) baseStart_2086634 baseEnd_2086634 := by
    simpa [prefixWord, tailWord_2086634, baseEnd_2086634] using wordTrace_append hprefix tailTrace_2086634
  have hstable : (prefixWord ++ tailWord_2086634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086634).length < 2 ^ (prefixWord ++ tailWord_2086634).sum := by decide
  have hdescent : baseEnd_2086634 < baseStart_2086634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086667 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 3]
def baseStart_2086667 : Nat := 118140960795 + 2086667 * 2 ^ 59
def prefixEnd_2086667 : Nat := 4983230072969 + 3 ^ 40 * 2086667 * 2
def baseEnd_2086667 : Nat := 1071463136875492639466099

theorem tailTrace_2086667 : CollatzResearch.WordTrace tailWord_2086667 prefixEnd_2086667 1071463136875492639466099 := by
  unfold tailWord_2086667
  simp only [CollatzResearch.WordTrace]
  refine ⟨76106997931369308196298255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50737998620912872130865503 76106997931369308196298255)
  ·
    refine ⟨114160496897053962294447383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76106997931369308196298255 114160496897053962294447383)
    ·
      refine ⟨171240745345580943441671075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114160496897053962294447383 171240745345580943441671075)
      ·
        refine ⟨256861118018371415162506613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171240745345580943441671075 256861118018371415162506613)
        ·
          refine ⟨24080729814222320171484995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256861118018371415162506613 24080729814222320171484995)
          ·
            refine ⟨36121094721333480257227493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24080729814222320171484995 36121094721333480257227493)
            ·
              refine ⟨6772705260250027548230155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36121094721333480257227493 6772705260250027548230155)
              ·
                refine ⟨10159057890375041322345233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772705260250027548230155 10159057890375041322345233)
                ·
                  refine ⟨7619293417781280991758925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10159057890375041322345233 7619293417781280991758925)
                  ·
                    refine ⟨2857235031667980371909597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7619293417781280991758925 2857235031667980371909597)
                    ·
                      refine ⟨1071463136875492639466099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857235031667980371909597 1071463136875492639466099)
                      ·
                        rfl

theorem cell23_2086667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 3].length) (baseStart_2086667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086667 prefixEnd_2086667 := by exact prefixLift 2086667
  have htrace : WordTrace (prefixWord ++ tailWord_2086667) baseStart_2086667 baseEnd_2086667 := by
    simpa [prefixWord, tailWord_2086667, baseEnd_2086667] using wordTrace_append hprefix tailTrace_2086667
  have hstable : (prefixWord ++ tailWord_2086667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086667).length < 2 ^ (prefixWord ++ tailWord_2086667).sum := by decide
  have hdescent : baseEnd_2086667 < baseStart_2086667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086674 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_2086674 : Nat := 118140960795 + 2086674 * 2 ^ 59
def prefixEnd_2086674 : Nat := 4983230072969 + 3 ^ 40 * 2086674 * 2
def baseEnd_2086674 : Nat := 119051859026674901342063

theorem tailTrace_2086674 : CollatzResearch.WordTrace tailWord_2086674 prefixEnd_2086674 119051859026674901342063 := by
  unfold tailWord_2086674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19026813310585987097950769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50738168828229298927868717 19026813310585987097950769)
  ·
    refine ⟨14270109982939490323463077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19026813310585987097950769 14270109982939490323463077)
    ·
      refine ⟨2675645621801154435649327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14270109982939490323463077 2675645621801154435649327)
      ·
        refine ⟨4013468432701731653473991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675645621801154435649327 4013468432701731653473991)
        ·
          refine ⟨6020202649052597480210987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013468432701731653473991 6020202649052597480210987)
          ·
            refine ⟨9030303973578896220316481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020202649052597480210987 9030303973578896220316481)
            ·
              refine ⟨6772727980184172165237361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9030303973578896220316481 6772727980184172165237361)
              ·
                refine ⟨5079545985138129123928021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6772727980184172165237361 5079545985138129123928021)
                ·
                  refine ⟨119051859026674901342063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5079545985138129123928021 119051859026674901342063)
                  ·
                    rfl

theorem cell23_2086674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_2086674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086674 prefixEnd_2086674 := by exact prefixLift 2086674
  have htrace : WordTrace (prefixWord ++ tailWord_2086674) baseStart_2086674 baseEnd_2086674 := by
    simpa [prefixWord, tailWord_2086674, baseEnd_2086674] using wordTrace_append hprefix tailTrace_2086674
  have hstable : (prefixWord ++ tailWord_2086674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086674).length < 2 ^ (prefixWord ++ tailWord_2086674).sum := by decide
  have hdescent : baseEnd_2086674 < baseStart_2086674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086687 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 2, 5]
def baseStart_2086687 : Nat := 118140960795 + 2086687 * 2 ^ 59
def prefixEnd_2086687 : Nat := 4983230072969 + 3 ^ 40 * 2086687 * 2
def baseEnd_2086687 : Nat := 357157802162860853738669

theorem tailTrace_2086687 : CollatzResearch.WordTrace tailWord_2086687 prefixEnd_2086687 357157802162860853738669 := by
  unfold tailWord_2086687
  simp only [CollatzResearch.WordTrace]
  refine ⟨76107727391296851612026315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50738484927531234408017543 76107727391296851612026315)
  ·
    refine ⟨114161591086945277418039473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76107727391296851612026315 114161591086945277418039473)
    ·
      refine ⟨85621193315208958063529605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114161591086945277418039473 85621193315208958063529605)
      ·
        refine ⟨16053973746601679636911801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85621193315208958063529605 16053973746601679636911801)
        ·
          refine ⟨12040480309951259727683851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16053973746601679636911801 12040480309951259727683851)
          ·
            refine ⟨18060720464926889591525777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040480309951259727683851 18060720464926889591525777)
            ·
              refine ⟨13545540348695167193644333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18060720464926889591525777 13545540348695167193644333)
              ·
                refine ⟨5079577630760687697616625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13545540348695167193644333 5079577630760687697616625)
                ·
                  refine ⟨3809683223070515773212469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079577630760687697616625 3809683223070515773212469)
                  ·
                    refine ⟨357157802162860853738669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3809683223070515773212469 357157802162860853738669)
                    ·
                      rfl

theorem cell23_2086687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_2086687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086687 prefixEnd_2086687 := by exact prefixLift 2086687
  have htrace : WordTrace (prefixWord ++ tailWord_2086687) baseStart_2086687 baseEnd_2086687 := by
    simpa [prefixWord, tailWord_2086687, baseEnd_2086687] using wordTrace_append hprefix tailTrace_2086687
  have hstable : (prefixWord ++ tailWord_2086687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086687).length < 2 ^ (prefixWord ++ tailWord_2086687).sum := by decide
  have hdescent : baseEnd_2086687 < baseStart_2086687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086708 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2086708 : Nat := 118140960795 + 2086708 * 2 ^ 59
def prefixEnd_2086708 : Nat := 4983230072969 + 3 ^ 40 * 2086708 * 2
def baseEnd_2086708 : Nat := 119053798842480775450379

theorem tailTrace_2086708 : CollatzResearch.WordTrace tailWord_2086708 prefixEnd_2086708 119053798842480775450379 := by
  unfold tailWord_2086708
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054246662110386099270389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50738995549480514799027185 38054246662110386099270389)
  ·
    refine ⟨3567585624572848696806599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38054246662110386099270389 3567585624572848696806599)
    ·
      refine ⟨5351378436859273045209899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567585624572848696806599 5351378436859273045209899)
      ·
        refine ⟨8027067655288909567814849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351378436859273045209899 8027067655288909567814849)
        ·
          refine ⟨6020300741466682175861137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8027067655288909567814849 6020300741466682175861137)
          ·
            refine ⟨4515225556100011631895853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6020300741466682175861137 4515225556100011631895853)
            ·
              refine ⟨1693209583537504361960945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4515225556100011631895853 1693209583537504361960945)
              ·
                refine ⟨1269907187653128271470709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693209583537504361960945 1269907187653128271470709)
                ·
                  refine ⟨119053798842480775450379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269907187653128271470709 119053798842480775450379)
                  ·
                    rfl

theorem cell23_2086708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2086708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086708 prefixEnd_2086708 := by exact prefixLift 2086708
  have htrace : WordTrace (prefixWord ++ tailWord_2086708) baseStart_2086708 baseEnd_2086708 := by
    simpa [prefixWord, tailWord_2086708, baseEnd_2086708] using wordTrace_append hprefix tailTrace_2086708
  have hstable : (prefixWord ++ tailWord_2086708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086708).length < 2 ^ (prefixWord ++ tailWord_2086708).sum := by decide
  have hdescent : baseEnd_2086708 < baseStart_2086708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086727 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_2086727 : Nat := 118140960795 + 2086727 * 2 ^ 59
def prefixEnd_2086727 : Nat := 4983230072969 + 3 ^ 40 * 2086727 * 2
def baseEnd_2086727 : Nat := 1071493945714762404715823

theorem tailTrace_2086727 : CollatzResearch.WordTrace tailWord_2086727 prefixEnd_2086727 1071493945714762404715823 := by
  unfold tailWord_2086727
  simp only [CollatzResearch.WordTrace]
  refine ⟨76109186311151938443482435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50739457540767958962321623 76109186311151938443482435)
  ·
    refine ⟨114163779466727907665223653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76109186311151938443482435 114163779466727907665223653)
    ·
      refine ⟨21405708650011482687229435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114163779466727907665223653 21405708650011482687229435)
      ·
        refine ⟨32108562975017224030844153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21405708650011482687229435 32108562975017224030844153)
        ·
          refine ⟨24081422231262918023133115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32108562975017224030844153 24081422231262918023133115)
          ·
            refine ⟨36122133346894377034699673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24081422231262918023133115 36122133346894377034699673)
            ·
              refine ⟨27091600010170782776024755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36122133346894377034699673 27091600010170782776024755)
              ·
                refine ⟨40637400015256174164037133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27091600010170782776024755 40637400015256174164037133)
                ·
                  refine ⟨15239025005721065311513925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40637400015256174164037133 15239025005721065311513925)
                  ·
                    refine ⟨2857317188572699745908861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15239025005721065311513925 2857317188572699745908861)
                    ·
                      refine ⟨1071493945714762404715823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857317188572699745908861 1071493945714762404715823)
                      ·
                        rfl

theorem cell23_2086727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_2086727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086727 prefixEnd_2086727 := by exact prefixLift 2086727
  have htrace : WordTrace (prefixWord ++ tailWord_2086727) baseStart_2086727 baseEnd_2086727 := by
    simpa [prefixWord, tailWord_2086727, baseEnd_2086727] using wordTrace_append hprefix tailTrace_2086727
  have hstable : (prefixWord ++ tailWord_2086727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086727).length < 2 ^ (prefixWord ++ tailWord_2086727).sum := by decide
  have hdescent : baseEnd_2086727 < baseStart_2086727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086764 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 6]
def baseStart_2086764 : Nat := 118140960795 + 2086764 * 2 ^ 59
def prefixEnd_2086764 : Nat := 4983230072969 + 3 ^ 40 * 2086764 * 2
def baseEnd_2086764 : Nat := 119056993833219862217017

theorem tailTrace_2086764 : CollatzResearch.WordTrace tailWord_2086764 prefixEnd_2086764 119056993833219862217017 := by
  unfold tailWord_2086764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38055267906008946881289673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50740357208011929175052897 38055267906008946881289673)
  ·
    refine ⟨28541450929506710160967255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38055267906008946881289673 28541450929506710160967255)
    ·
      refine ⟨42812176394260065241450883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28541450929506710160967255 42812176394260065241450883)
      ·
        refine ⟨64218264591390097862176325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42812176394260065241450883 64218264591390097862176325)
        ·
          refine ⟨12040924610885643349158061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64218264591390097862176325 12040924610885643349158061)
          ·
            refine ⟨4515346729082116255934273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12040924610885643349158061 4515346729082116255934273)
            ·
              refine ⟨3386510046811587191950705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515346729082116255934273 3386510046811587191950705)
              ·
                refine ⟨2539882535108690393963029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386510046811587191950705 2539882535108690393963029)
                ·
                  refine ⟨119056993833219862217017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2539882535108690393963029 119056993833219862217017)
                  ·
                    rfl

theorem cell23_2086764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_2086764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086764 prefixEnd_2086764 := by exact prefixLift 2086764
  have htrace : WordTrace (prefixWord ++ tailWord_2086764) baseStart_2086764 baseEnd_2086764 := by
    simpa [prefixWord, tailWord_2086764, baseEnd_2086764] using wordTrace_append hprefix tailTrace_2086764
  have hstable : (prefixWord ++ tailWord_2086764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086764).length < 2 ^ (prefixWord ++ tailWord_2086764).sum := by decide
  have hdescent : baseEnd_2086764 < baseStart_2086764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086777 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_2086777 : Nat := 118140960795 + 2086777 * 2 ^ 59
def prefixEnd_2086777 : Nat := 4983230072969 + 3 ^ 40 * 2086777 * 2
def baseEnd_2086777 : Nat := 357173206582495736363531

theorem tailTrace_2086777 : CollatzResearch.WordTrace tailWord_2086777 prefixEnd_2086777 357173206582495736363531 := by
  unfold tailWord_2086777
  simp only [CollatzResearch.WordTrace]
  refine ⟨76111009960970796982802585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50740673307313864655201723 76111009960970796982802585)
  ·
    refine ⟨57083257470728097737101939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76111009960970796982802585 57083257470728097737101939)
    ·
      refine ⟨85624886206092146605652909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57083257470728097737101939 85624886206092146605652909)
      ·
        refine ⟨32109332327284554977119841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85624886206092146605652909 32109332327284554977119841)
        ·
          refine ⟨24081999245463416232839881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32109332327284554977119841 24081999245463416232839881)
          ·
            refine ⟨18061499434097562174629911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24081999245463416232839881 18061499434097562174629911)
            ·
              refine ⟨27092249151146343261944867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18061499434097562174629911 27092249151146343261944867)
              ·
                refine ⟨40638373726719514892917301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27092249151146343261944867 40638373726719514892917301)
                ·
                  refine ⟨3809847536879954521210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40638373726719514892917301 3809847536879954521210997)
                  ·
                    refine ⟨357173206582495736363531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3809847536879954521210997 357173206582495736363531)
                    ·
                      rfl

theorem cell23_2086777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_2086777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086777 prefixEnd_2086777 := by exact prefixLift 2086777
  have htrace : WordTrace (prefixWord ++ tailWord_2086777) baseStart_2086777 baseEnd_2086777 := by
    simpa [prefixWord, tailWord_2086777, baseEnd_2086777] using wordTrace_append hprefix tailTrace_2086777
  have hstable : (prefixWord ++ tailWord_2086777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086777).length < 2 ^ (prefixWord ++ tailWord_2086777).sum := by decide
  have hdescent : baseEnd_2086777 < baseStart_2086777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086784 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 1, 5, 2]
def baseStart_2086784 : Nat := 118140960795 + 2086784 * 2 ^ 59
def prefixEnd_2086784 : Nat := 4983230072969 + 3 ^ 40 * 2086784 * 2
def baseEnd_2086784 : Nat := 1071523214112068681703061

theorem tailTrace_2086784 : CollatzResearch.WordTrace tailWord_2086784 prefixEnd_2086784 1071523214112068681703061 := by
  unfold tailWord_2086784
  simp only [CollatzResearch.WordTrace]
  refine ⟨38055632635972718589153703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50740843514630291452204937 38055632635972718589153703)
  ·
    refine ⟨57083448953959077883730555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38055632635972718589153703 57083448953959077883730555)
    ·
      refine ⟨85625173430938616825595833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57083448953959077883730555 85625173430938616825595833)
      ·
        refine ⟨64218880073203962619196875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85625173430938616825595833 64218880073203962619196875)
        ·
          refine ⟨96328320109805943928795313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64218880073203962619196875 96328320109805943928795313)
          ·
            refine ⟨72246240082354457946596485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96328320109805943928795313 72246240082354457946596485)
            ·
              refine ⟨13546170015441460864986841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72246240082354457946596485 13546170015441460864986841)
              ·
                refine ⟨10159627511581095648740131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13546170015441460864986841 10159627511581095648740131)
                ·
                  refine ⟨15239441267371643473110197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159627511581095648740131 15239441267371643473110197)
                  ·
                    refine ⟨1428697618816091575604081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15239441267371643473110197 1428697618816091575604081)
                    ·
                      refine ⟨1071523214112068681703061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428697618816091575604081 1071523214112068681703061)
                      ·
                        rfl

theorem cell23_2086784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_2086784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086784 prefixEnd_2086784 := by exact prefixLift 2086784
  have htrace : WordTrace (prefixWord ++ tailWord_2086784) baseStart_2086784 baseEnd_2086784 := by
    simpa [prefixWord, tailWord_2086784, baseEnd_2086784] using wordTrace_append hprefix tailTrace_2086784
  have hstable : (prefixWord ++ tailWord_2086784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086784).length < 2 ^ (prefixWord ++ tailWord_2086784).sum := by decide
  have hdescent : baseEnd_2086784 < baseStart_2086784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086801 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 2, 3, 2]
def baseStart_2086801 : Nat := 118140960795 + 2086801 * 2 ^ 59
def prefixEnd_2086801 : Nat := 4983230072969 + 3 ^ 40 * 2086801 * 2
def baseEnd_2086801 : Nat := 1071531943283195115190483

theorem tailTrace_2086801 : CollatzResearch.WordTrace tailWord_2086801 prefixEnd_2086801 1071531943283195115190483 := by
  unfold tailWord_2086801
  simp only [CollatzResearch.WordTrace]
  refine ⟨76111885312883849081676257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50741256875255899387784171 76111885312883849081676257)
  ·
    refine ⟨57083913984662886811257193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76111885312883849081676257 57083913984662886811257193)
    ·
      refine ⟨42812935488497165108442895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57083913984662886811257193 42812935488497165108442895)
      ·
        refine ⟨64219403232745747662664343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42812935488497165108442895 64219403232745747662664343)
        ·
          refine ⟨96329104849118621493996515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64219403232745747662664343 96329104849118621493996515)
          ·
            refine ⟨144493657273677932240994773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96329104849118621493996515 144493657273677932240994773)
            ·
              refine ⟨3386570092351826536898315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144493657273677932240994773 3386570092351826536898315)
              ·
                refine ⟨5079855138527739805347473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386570092351826536898315 5079855138527739805347473)
                ·
                  refine ⟨3809891353895804854010605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079855138527739805347473 3809891353895804854010605)
                  ·
                    refine ⟨1428709257710926820253977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809891353895804854010605 1428709257710926820253977)
                    ·
                      refine ⟨1071531943283195115190483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428709257710926820253977 1071531943283195115190483)
                      ·
                        rfl

theorem cell23_2086801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_2086801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086801 prefixEnd_2086801 := by exact prefixLift 2086801
  have htrace : WordTrace (prefixWord ++ tailWord_2086801) baseStart_2086801 baseEnd_2086801 := by
    simpa [prefixWord, tailWord_2086801, baseEnd_2086801] using wordTrace_append hprefix tailTrace_2086801
  have hstable : (prefixWord ++ tailWord_2086801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086801).length < 2 ^ (prefixWord ++ tailWord_2086801).sum := by decide
  have hdescent : baseEnd_2086801 < baseStart_2086801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086834 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2086834 : Nat := 118140960795 + 2086834 * 2 ^ 59
def prefixEnd_2086834 : Nat := 4983230072969 + 3 ^ 40 * 2086834 * 2
def baseEnd_2086834 : Nat := 1071548888144793486077831

theorem tailTrace_2086834 : CollatzResearch.WordTrace tailWord_2086834 prefixEnd_2086834 1071548888144793486077831 := by
  unfold tailWord_2086834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028272230441073929406889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50742059281176197145085037 19028272230441073929406889)
  ·
    refine ⟨14271204172830805447055167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19028272230441073929406889 14271204172830805447055167)
    ·
      refine ⟨21406806259246208170582751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14271204172830805447055167 21406806259246208170582751)
      ·
        refine ⟨32110209388869312255874127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21406806259246208170582751 32110209388869312255874127)
        ·
          refine ⟨48165314083303968383811191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32110209388869312255874127 48165314083303968383811191)
          ·
            refine ⟨72247971124955952575716787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48165314083303968383811191 72247971124955952575716787)
            ·
              refine ⟨108371956687433928863575181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72247971124955952575716787 108371956687433928863575181)
              ·
                refine ⟨40639483757787723323840693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108371956687433928863575181 40639483757787723323840693)
                ·
                  refine ⟨3809951602292599061610065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40639483757787723323840693 3809951602292599061610065)
                  ·
                    refine ⟨2857463701719449296207549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3809951602292599061610065 2857463701719449296207549)
                    ·
                      refine ⟨1071548888144793486077831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857463701719449296207549 1071548888144793486077831)
                      ·
                        rfl

theorem cell23_2086834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2086834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086834 prefixEnd_2086834 := by exact prefixLift 2086834
  have htrace : WordTrace (prefixWord ++ tailWord_2086834) baseStart_2086834 baseEnd_2086834 := by
    simpa [prefixWord, tailWord_2086834, baseEnd_2086834] using wordTrace_append hprefix tailTrace_2086834
  have hstable : (prefixWord ++ tailWord_2086834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086834).length < 2 ^ (prefixWord ++ tailWord_2086834).sum := by decide
  have hdescent : baseEnd_2086834 < baseStart_2086834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086864 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_2086864 : Nat := 118140960795 + 2086864 * 2 ^ 59
def prefixEnd_2086864 : Nat := 4983230072969 + 3 ^ 40 * 2086864 * 2
def baseEnd_2086864 : Nat := 1071564292564428368702693

theorem tailTrace_2086864 : CollatzResearch.WordTrace tailWord_2086864 prefixEnd_2086864 1071564292564428368702693 := by
  unfold tailWord_2086864
  simp only [CollatzResearch.WordTrace]
  refine ⟨38057091555827805420609823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50742788741103740560813097 38057091555827805420609823)
  ·
    refine ⟨57085637333741708130914735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38057091555827805420609823 57085637333741708130914735)
    ·
      refine ⟨85628456000612562196372103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57085637333741708130914735 85628456000612562196372103)
      ·
        refine ⟨128442684000918843294558155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85628456000612562196372103 128442684000918843294558155)
        ·
          refine ⟨192664026001378264941837233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128442684000918843294558155 192664026001378264941837233)
          ·
            refine ⟨144498019501033698706377925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192664026001378264941837233 144498019501033698706377925)
            ·
              refine ⟨27093378656443818507445861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144498019501033698706377925 27093378656443818507445861)
              ·
                refine ⟨5080008498083215970146099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27093378656443818507445861 5080008498083215970146099)
                ·
                  refine ⟨7620012747124823955219149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080008498083215970146099 7620012747124823955219149)
                  ·
                    refine ⟨2857504780171808983207181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7620012747124823955219149 2857504780171808983207181)
                    ·
                      refine ⟨1071564292564428368702693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857504780171808983207181 1071564292564428368702693)
                      ·
                        rfl

theorem cell23_2086864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_2086864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086864 prefixEnd_2086864 := by exact prefixLift 2086864
  have htrace : WordTrace (prefixWord ++ tailWord_2086864) baseStart_2086864 baseEnd_2086864 := by
    simpa [prefixWord, tailWord_2086864, baseEnd_2086864] using wordTrace_append hprefix tailTrace_2086864
  have hstable : (prefixWord ++ tailWord_2086864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086864).length < 2 ^ (prefixWord ++ tailWord_2086864).sum := by decide
  have hdescent : baseEnd_2086864 < baseStart_2086864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086876 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2086876 : Nat := 118140960795 + 2086876 * 2 ^ 59
def prefixEnd_2086876 : Nat := 4983230072969 + 3 ^ 40 * 2086876 * 2
def baseEnd_2086876 : Nat := 1071570454332282321752639

theorem tailTrace_2086876 : CollatzResearch.WordTrace tailWord_2086876 prefixEnd_2086876 1071570454332282321752639 := by
  unfold tailWord_2086876
  simp only [CollatzResearch.WordTrace]
  refine ⟨38057310393806068445328241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50743080525074757927104321 38057310393806068445328241)
  ·
    refine ⟨28542982795354551333996181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38057310393806068445328241 28542982795354551333996181)
    ·
      refine ⟨1337952318532244593781071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28542982795354551333996181 1337952318532244593781071)
      ·
        refine ⟨2006928477798366890671607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337952318532244593781071 2006928477798366890671607)
        ·
          refine ⟨3010392716697550336007411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006928477798366890671607 3010392716697550336007411)
          ·
            refine ⟨4515589075046325504011117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010392716697550336007411 4515589075046325504011117)
            ·
              refine ⟨1693345903142372064004169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4515589075046325504011117 1693345903142372064004169)
              ·
                refine ⟨1270009427356779048003127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693345903142372064004169 1270009427356779048003127)
                ·
                  refine ⟨1905014141035168572004691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270009427356779048003127 1905014141035168572004691)
                  ·
                    refine ⟨2857521211552752858007037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1905014141035168572004691 2857521211552752858007037)
                    ·
                      refine ⟨1071570454332282321752639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857521211552752858007037 1071570454332282321752639)
                      ·
                        rfl

theorem cell23_2086876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2086876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086876 prefixEnd_2086876 := by exact prefixLift 2086876
  have htrace : WordTrace (prefixWord ++ tailWord_2086876) baseStart_2086876 baseEnd_2086876 := by
    simpa [prefixWord, tailWord_2086876, baseEnd_2086876] using wordTrace_append hprefix tailTrace_2086876
  have hstable : (prefixWord ++ tailWord_2086876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086876).length < 2 ^ (prefixWord ++ tailWord_2086876).sum := by decide
  have hdescent : baseEnd_2086876 < baseStart_2086876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086881 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_2086881 : Nat := 118140960795 + 2086881 * 2 ^ 59
def prefixEnd_2086881 : Nat := 4983230072969 + 3 ^ 40 * 2086881 * 2
def baseEnd_2086881 : Nat := 1071573021735554802190115

theorem tailTrace_2086881 : CollatzResearch.WordTrace tailWord_2086881 prefixEnd_2086881 1071573021735554802190115 := by
  unfold tailWord_2086881
  simp only [CollatzResearch.WordTrace]
  refine ⟨76114803152594022744588497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50743202101729348496392331 76114803152594022744588497)
  ·
    refine ⟨57086102364445517058441373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76114803152594022744588497 57086102364445517058441373)
    ·
      refine ⟨21407288386667068896915515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57086102364445517058441373 21407288386667068896915515)
      ·
        refine ⟨32110932580000603345373273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21407288386667068896915515 32110932580000603345373273)
        ·
          refine ⟨24083199435000452509029955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32110932580000603345373273 24083199435000452509029955)
          ·
            refine ⟨36124799152500678763544933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24083199435000452509029955 36124799152500678763544933)
            ·
              refine ⟨6773399841093877268164675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36124799152500678763544933 6773399841093877268164675)
              ·
                refine ⟨10160099761640815902247013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773399841093877268164675 10160099761640815902247013)
                ·
                  refine ⟨1905018705307652981671315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10160099761640815902247013 1905018705307652981671315)
                  ·
                    refine ⟨2857528057961479472506973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1905018705307652981671315 2857528057961479472506973)
                    ·
                      refine ⟨1071573021735554802190115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857528057961479472506973 1071573021735554802190115)
                      ·
                        rfl

theorem cell23_2086881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_2086881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086881 prefixEnd_2086881 := by exact prefixLift 2086881
  have htrace : WordTrace (prefixWord ++ tailWord_2086881) baseStart_2086881 baseEnd_2086881 := by
    simpa [prefixWord, tailWord_2086881, baseEnd_2086881] using wordTrace_append hprefix tailTrace_2086881
  have hstable : (prefixWord ++ tailWord_2086881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086881).length < 2 ^ (prefixWord ++ tailWord_2086881).sum := by decide
  have hdescent : baseEnd_2086881 < baseStart_2086881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086902 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_2086902 : Nat := 118140960795 + 2086902 * 2 ^ 59
def prefixEnd_2086902 : Nat := 4983230072969 + 3 ^ 40 * 2086902 * 2
def baseEnd_2086902 : Nat := 1071583804829299220027519

theorem tailTrace_2086902 : CollatzResearch.WordTrace tailWord_2086902 prefixEnd_2086902 1071583804829299220027519 := by
  unfold tailWord_2086902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757223067844871458193935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50743712723678628887401973 4757223067844871458193935)
  ·
    refine ⟨7135834601767307187290903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4757223067844871458193935 7135834601767307187290903)
    ·
      refine ⟨10703751902650960780936355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7135834601767307187290903 10703751902650960780936355)
      ·
        refine ⟨16055627853976441171404533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10703751902650960780936355 16055627853976441171404533)
        ·
          refine ⟨1505215111310291359819175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16055627853976441171404533 1505215111310291359819175)
          ·
            refine ⟨2257822666965437039728763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505215111310291359819175 2257822666965437039728763)
            ·
              refine ⟨3386734000448155559593145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257822666965437039728763 3386734000448155559593145)
              ·
                refine ⟨2540050500336116669694859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386734000448155559593145 2540050500336116669694859)
                ·
                  refine ⟨3810075750504175004542289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540050500336116669694859 3810075750504175004542289)
                  ·
                    refine ⟨2857556812878131253406717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810075750504175004542289 2857556812878131253406717)
                    ·
                      refine ⟨1071583804829299220027519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857556812878131253406717 1071583804829299220027519)
                      ·
                        rfl

theorem cell23_2086902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_2086902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086902 prefixEnd_2086902 := by exact prefixLift 2086902
  have htrace : WordTrace (prefixWord ++ tailWord_2086902) baseStart_2086902 baseEnd_2086902 := by
    simpa [prefixWord, tailWord_2086902, baseEnd_2086902] using wordTrace_append hprefix tailTrace_2086902
  have hstable : (prefixWord ++ tailWord_2086902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086902).length < 2 ^ (prefixWord ++ tailWord_2086902).sum := by decide
  have hdescent : baseEnd_2086902 < baseStart_2086902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086924 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2086924 : Nat := 118140960795 + 2086924 * 2 ^ 59
def prefixEnd_2086924 : Nat := 4983230072969 + 3 ^ 40 * 2086924 * 2
def baseEnd_2086924 : Nat := 1071595101403698133952417

theorem tailTrace_2086924 : CollatzResearch.WordTrace tailWord_2086924 prefixEnd_2086924 1071595101403698133952417 := by
  unfold tailWord_2086924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058185745719120544201913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50744247660958827392269217 38058185745719120544201913)
  ·
    refine ⟨28543639309289340408151435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38058185745719120544201913 28543639309289340408151435)
    ·
      refine ⟨42815458963934010612227153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28543639309289340408151435 42815458963934010612227153)
      ·
        refine ⟨32111594222950507959170365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42815458963934010612227153 32111594222950507959170365)
        ·
          refine ⟨12041847833606440484688887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32111594222950507959170365 12041847833606440484688887)
          ·
            refine ⟨18062771750409660727033331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12041847833606440484688887 18062771750409660727033331)
            ·
              refine ⟨27094157625614491090549997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062771750409660727033331 27094157625614491090549997)
              ·
                refine ⟨10160309109605434158956249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27094157625614491090549997 10160309109605434158956249)
                ·
                  refine ⟨7620231832204075619217187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10160309109605434158956249 7620231832204075619217187)
                  ·
                    refine ⟨11430347748306113428825781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620231832204075619217187 11430347748306113428825781)
                    ·
                      refine ⟨1071595101403698133952417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11430347748306113428825781 1071595101403698133952417)
                      ·
                        rfl

theorem cell23_2086924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2086924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086924 prefixEnd_2086924 := by exact prefixLift 2086924
  have htrace : WordTrace (prefixWord ++ tailWord_2086924) baseStart_2086924 baseEnd_2086924 := by
    simpa [prefixWord, tailWord_2086924, baseEnd_2086924] using wordTrace_append hprefix tailTrace_2086924
  have hstable : (prefixWord ++ tailWord_2086924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086924).length < 2 ^ (prefixWord ++ tailWord_2086924).sum := by decide
  have hdescent : baseEnd_2086924 < baseStart_2086924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086941 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2086941 : Nat := 118140960795 + 2086941 * 2 ^ 59
def prefixEnd_2086941 : Nat := 4983230072969 + 3 ^ 40 * 2086941 * 2
def baseEnd_2086941 : Nat := 1071603830574824567439839

theorem tailTrace_2086941 : CollatzResearch.WordTrace tailWord_2086941 prefixEnd_2086941 1071603830574824567439839 := by
  unfold tailWord_2086941
  simp only [CollatzResearch.WordTrace]
  refine ⟨76116991532376652991772677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50744661021584435327848451 76116991532376652991772677)
  ·
    refine ⟨14271935912320622435957377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76116991532376652991772677 14271935912320622435957377)
    ·
      refine ⟨10703951934240466826968033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14271935912320622435957377 10703951934240466826968033)
      ·
        refine ⟨8027963950680350120226025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10703951934240466826968033 8027963950680350120226025)
        ·
          refine ⟨6020972963010262590169519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8027963950680350120226025 6020972963010262590169519)
          ·
            refine ⟨9031459444515393885254279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020972963010262590169519 9031459444515393885254279)
            ·
              refine ⟨13547189166773090827881419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031459444515393885254279 13547189166773090827881419)
              ·
                refine ⟨20320783750159636241822129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547189166773090827881419 20320783750159636241822129)
                ·
                  refine ⟨15240587812619727181366597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20320783750159636241822129 15240587812619727181366597)
                  ·
                    refine ⟨2857610214866198846506237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15240587812619727181366597 2857610214866198846506237)
                    ·
                      refine ⟨1071603830574824567439839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857610214866198846506237 1071603830574824567439839)
                      ·
                        rfl

theorem cell23_2086941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2086941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086941 prefixEnd_2086941 := by exact prefixLift 2086941
  have htrace : WordTrace (prefixWord ++ tailWord_2086941) baseStart_2086941 baseEnd_2086941 := by
    simpa [prefixWord, tailWord_2086941, baseEnd_2086941] using wordTrace_append hprefix tailTrace_2086941
  have hstable : (prefixWord ++ tailWord_2086941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086941).length < 2 ^ (prefixWord ++ tailWord_2086941).sum := by decide
  have hdescent : baseEnd_2086941 < baseStart_2086941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086984 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2086984 : Nat := 118140960795 + 2086984 * 2 ^ 59
def prefixEnd_2086984 : Nat := 4983230072969 + 3 ^ 40 * 2086984 * 2
def baseEnd_2086984 : Nat := 1071625910242967899202141

theorem tailTrace_2086984 : CollatzResearch.WordTrace tailWord_2086984 prefixEnd_2086984 1071625910242967899202141 := by
  unfold tailWord_2086984
  simp only [CollatzResearch.WordTrace]
  refine ⟨38059279935610435667794003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50745706580813914223725337 38059279935610435667794003)
  ·
    refine ⟨57088919903415653501691005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38059279935610435667794003 57088919903415653501691005)
    ·
      refine ⟨21408344963780870063134127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57088919903415653501691005 21408344963780870063134127)
      ·
        refine ⟨32112517445671305094701191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21408344963780870063134127 32112517445671305094701191)
        ·
          refine ⟨48168776168506957642051787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32112517445671305094701191 48168776168506957642051787)
          ·
            refine ⟨72253164252760436463077681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48168776168506957642051787 72253164252760436463077681)
            ·
              refine ⟨54189873189570327347308261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72253164252760436463077681 54189873189570327347308261)
              ·
                refine ⟨10160601223044436377620299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54189873189570327347308261 10160601223044436377620299)
                ·
                  refine ⟨15240901834566654566430449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160601223044436377620299 15240901834566654566430449)
                  ·
                    refine ⟨11430676375924990924822837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15240901834566654566430449 11430676375924990924822837)
                    ·
                      refine ⟨1071625910242967899202141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11430676375924990924822837 1071625910242967899202141)
                      ·
                        rfl

theorem cell23_2086984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2086984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2086984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2086984 prefixEnd_2086984 := by exact prefixLift 2086984
  have htrace : WordTrace (prefixWord ++ tailWord_2086984) baseStart_2086984 baseEnd_2086984 := by
    simpa [prefixWord, tailWord_2086984, baseEnd_2086984] using wordTrace_append hprefix tailTrace_2086984
  have hstable : (prefixWord ++ tailWord_2086984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086984).length < 2 ^ (prefixWord ++ tailWord_2086984).sum := by decide
  have hdescent : baseEnd_2086984 < baseStart_2086984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087006 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2087006 : Nat := 118140960795 + 2087006 * 2 ^ 59
def prefixEnd_2087006 : Nat := 4983230072969 + 3 ^ 40 * 2087006 * 2
def baseEnd_2087006 : Nat := 1071637206817366813127041

theorem tailTrace_2087006 : CollatzResearch.WordTrace tailWord_2087006 prefixEnd_2087006 1071637206817366813127041 := by
  unfold tailWord_2087006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514920284642646136611109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50746241518094112728592581 9514920284642646136611109)
  ·
    refine ⟨1784047553370496150614583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9514920284642646136611109 1784047553370496150614583)
    ·
      refine ⟨2676071330055744225921875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784047553370496150614583 2676071330055744225921875)
      ·
        refine ⟨4014106995083616338882813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676071330055744225921875 4014106995083616338882813)
        ·
          refine ⟨1505290123156356127081055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4014106995083616338882813 1505290123156356127081055)
          ·
            refine ⟨2257935184734534190621583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505290123156356127081055 2257935184734534190621583)
            ·
              refine ⟨3386902777101801285932375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257935184734534190621583 3386902777101801285932375)
              ·
                refine ⟨5080354165652701928898563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386902777101801285932375 5080354165652701928898563)
                ·
                  refine ⟨7620531248479052893347845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080354165652701928898563 7620531248479052893347845)
                  ·
                    refine ⟨1428849609089822417502721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620531248479052893347845 1428849609089822417502721)
                    ·
                      refine ⟨1071637206817366813127041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428849609089822417502721 1071637206817366813127041)
                      ·
                        rfl

theorem cell23_2087006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2087006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087006 prefixEnd_2087006 := by exact prefixLift 2087006
  have htrace : WordTrace (prefixWord ++ tailWord_2087006) baseStart_2087006 baseEnd_2087006 := by
    simpa [prefixWord, tailWord_2087006, baseEnd_2087006] using wordTrace_append hprefix tailTrace_2087006
  have hstable : (prefixWord ++ tailWord_2087006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087006).length < 2 ^ (prefixWord ++ tailWord_2087006).sum := by decide
  have hdescent : baseEnd_2087006 < baseStart_2087006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087031 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_2087031 : Nat := 118140960795 + 2087031 * 2 ^ 59
def prefixEnd_2087031 : Nat := 4983230072969 + 3 ^ 40 * 2087031 * 2
def baseEnd_2087031 : Nat := 1071650043833729215314425

theorem tailTrace_2087031 : CollatzResearch.WordTrace tailWord_2087031 prefixEnd_2087031 1071650043833729215314425 := by
  unfold tailWord_2087031
  simp only [CollatzResearch.WordTrace]
  refine ⟨76120274102050598362548947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50746849401367065575032631 76120274102050598362548947)
  ·
    refine ⟨114180411153075897543823421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76120274102050598362548947 114180411153075897543823421)
    ·
      refine ⟨42817654182403461578933783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114180411153075897543823421 42817654182403461578933783)
      ·
        refine ⟨64226481273605192368400675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817654182403461578933783 64226481273605192368400675)
        ·
          refine ⟨96339721910407788552601013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64226481273605192368400675 96339721910407788552601013)
          ·
            refine ⟨9031848929100730176806345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96339721910407788552601013 9031848929100730176806345)
            ·
              refine ⟨6773886696825547632604759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031848929100730176806345 6773886696825547632604759)
              ·
                refine ⟨10160830045238321448907139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773886696825547632604759 10160830045238321448907139)
                ·
                  refine ⟨15241245067857482173360709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160830045238321448907139 15241245067857482173360709)
                  ·
                    refine ⟨2857733450223277907505133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15241245067857482173360709 2857733450223277907505133)
                    ·
                      refine ⟨1071650043833729215314425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857733450223277907505133 1071650043833729215314425)
                      ·
                        rfl

theorem cell23_2087031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_2087031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087031 prefixEnd_2087031 := by exact prefixLift 2087031
  have htrace : WordTrace (prefixWord ++ tailWord_2087031) baseStart_2087031 baseEnd_2087031 := by
    simpa [prefixWord, tailWord_2087031, baseEnd_2087031] using wordTrace_append hprefix tailTrace_2087031
  have hstable : (prefixWord ++ tailWord_2087031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087031).length < 2 ^ (prefixWord ++ tailWord_2087031).sum := by decide
  have hdescent : baseEnd_2087031 < baseStart_2087031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087048 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2087048 : Nat := 118140960795 + 2087048 * 2 ^ 59
def prefixEnd_2087048 : Nat := 4983230072969 + 3 ^ 40 * 2087048 * 2
def baseEnd_2087048 : Nat := 1071658773004855648801847

theorem tailTrace_2087048 : CollatzResearch.WordTrace tailWord_2087048 prefixEnd_2087048 1071658773004855648801847 := by
  unfold tailWord_2087048
  simp only [CollatzResearch.WordTrace]
  refine ⟨38060447071494505132958899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50747262761992673510611865 38060447071494505132958899)
  ·
    refine ⟨57090670607241757699438349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38060447071494505132958899 57090670607241757699438349)
    ·
      refine ⟨21409001477715659137289381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57090670607241757699438349 21409001477715659137289381)
      ·
        refine ⟨4014187777071686088241759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21409001477715659137289381 4014187777071686088241759)
        ·
          refine ⟨6021281665607529132362639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014187777071686088241759 6021281665607529132362639)
          ·
            refine ⟨9031922498411293698543959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021281665607529132362639 9031922498411293698543959)
            ·
              refine ⟨13547883747616940547815939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031922498411293698543959 13547883747616940547815939)
              ·
                refine ⟨20321825621425410821723909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547883747616940547815939 20321825621425410821723909)
                ·
                  refine ⟨3810342304017264529073233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20321825621425410821723909 3810342304017264529073233)
                  ·
                    refine ⟨2857756728012948396804925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810342304017264529073233 2857756728012948396804925)
                    ·
                      refine ⟨1071658773004855648801847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857756728012948396804925 1071658773004855648801847)
                      ·
                        rfl

theorem cell23_2087048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2087048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087048 prefixEnd_2087048 := by exact prefixLift 2087048
  have htrace : WordTrace (prefixWord ++ tailWord_2087048) baseStart_2087048 baseEnd_2087048 := by
    simpa [prefixWord, tailWord_2087048, baseEnd_2087048] using wordTrace_append hprefix tailTrace_2087048
  have hstable : (prefixWord ++ tailWord_2087048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087048).length < 2 ^ (prefixWord ++ tailWord_2087048).sum := by decide
  have hdescent : baseEnd_2087048 < baseStart_2087048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087082 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2087082 : Nat := 118140960795 + 2087082 * 2 ^ 59
def prefixEnd_2087082 : Nat := 4983230072969 + 3 ^ 40 * 2087082 * 2
def baseEnd_2087082 : Nat := 1071676231347108515776691

theorem tailTrace_2087082 : CollatzResearch.WordTrace tailWord_2087082 prefixEnd_2087082 1071676231347108515776691 := by
  unfold tailWord_2087082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19030533556216458518163875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50748089483243889381770333 19030533556216458518163875)
  ·
    refine ⟨28545800334324687777245813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19030533556216458518163875 28545800334324687777245813)
    ·
      refine ⟨2676168781342939479116795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28545800334324687777245813 2676168781342939479116795)
      ·
        refine ⟨4014253172014409218675193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676168781342939479116795 4014253172014409218675193)
        ·
          refine ⟨3010689879010806914006395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014253172014409218675193 3010689879010806914006395)
          ·
            refine ⟨4516034818516210371009593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010689879010806914006395 4516034818516210371009593)
            ·
              refine ⟨3387026113887157778257195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516034818516210371009593 3387026113887157778257195)
              ·
                refine ⟨5080539170830736667385793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387026113887157778257195 5080539170830736667385793)
                ·
                  refine ⟨3810404378123052500539345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5080539170830736667385793 3810404378123052500539345)
                  ·
                    refine ⟨2857803283592289375404509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810404378123052500539345 2857803283592289375404509)
                    ·
                      refine ⟨1071676231347108515776691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857803283592289375404509 1071676231347108515776691)
                      ·
                        rfl

theorem cell23_2087082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2087082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087082 prefixEnd_2087082 := by exact prefixLift 2087082
  have htrace : WordTrace (prefixWord ++ tailWord_2087082) baseStart_2087082 baseEnd_2087082 := by
    simpa [prefixWord, tailWord_2087082, baseEnd_2087082] using wordTrace_append hprefix tailTrace_2087082
  have hstable : (prefixWord ++ tailWord_2087082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087082).length < 2 ^ (prefixWord ++ tailWord_2087082).sum := by decide
  have hdescent : baseEnd_2087082 < baseStart_2087082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087106 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2087106 : Nat := 118140960795 + 2087106 * 2 ^ 59
def prefixEnd_2087106 : Nat := 4983230072969 + 3 ^ 40 * 2087106 * 2
def baseEnd_2087106 : Nat := 357229518294272140625527

theorem tailTrace_2087106 : CollatzResearch.WordTrace tailWord_2087106 prefixEnd_2087106 357229518294272140625527 := by
  unfold tailWord_2087106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19030752394194721542882293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50748673051185924114352781 19030752394194721542882293)
  ·
    refine ⟨1784133036955755144645215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19030752394194721542882293 1784133036955755144645215)
    ·
      refine ⟨2676199555433632716967823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784133036955755144645215 2676199555433632716967823)
      ·
        refine ⟨4014299333150449075451735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676199555433632716967823 4014299333150449075451735)
        ·
          refine ⟨6021448999725673613177603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014299333150449075451735 6021448999725673613177603)
          ·
            refine ⟨9032173499588510419766405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021448999725673613177603 9032173499588510419766405)
            ·
              refine ⟨1693532531172845703706201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9032173499588510419766405 1693532531172845703706201)
              ·
                refine ⟨1270149398379634277779651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693532531172845703706201 1270149398379634277779651)
                ·
                  refine ⟨1905224097569451416669477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270149398379634277779651 1905224097569451416669477)
                  ·
                    refine ⟨357229518294272140625527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1905224097569451416669477 357229518294272140625527)
                    ·
                      rfl

theorem cell23_2087106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2087106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087106 prefixEnd_2087106 := by exact prefixLift 2087106
  have htrace : WordTrace (prefixWord ++ tailWord_2087106) baseStart_2087106 baseEnd_2087106 := by
    simpa [prefixWord, tailWord_2087106, baseEnd_2087106] using wordTrace_append hprefix tailTrace_2087106
  have hstable : (prefixWord ++ tailWord_2087106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087106).length < 2 ^ (prefixWord ++ tailWord_2087106).sum := by decide
  have hdescent : baseEnd_2087106 < baseStart_2087106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087118 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_2087118 : Nat := 118140960795 + 2087118 * 2 ^ 59
def prefixEnd_2087118 : Nat := 4983230072969 + 3 ^ 40 * 2087118 * 2
def baseEnd_2087118 : Nat := 1071694716650670374926525

theorem tailTrace_2087118 : CollatzResearch.WordTrace tailWord_2087118 prefixEnd_2087118 1071694716650670374926525 := by
  unfold tailWord_2087118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515430906591926527620751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50748964835156941480644005 9515430906591926527620751)
  ·
    refine ⟨14273146359887889791431127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515430906591926527620751 14273146359887889791431127)
    ·
      refine ⟨21409719539831834687146691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273146359887889791431127 21409719539831834687146691)
      ·
        refine ⟨32114579309747752030720037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21409719539831834687146691 32114579309747752030720037)
        ·
          refine ⟨6021483620577703505760007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32114579309747752030720037 6021483620577703505760007)
          ·
            refine ⟨9032225430866555258640011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021483620577703505760007 9032225430866555258640011)
            ·
              refine ⟨13548338146299832887960017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032225430866555258640011 13548338146299832887960017)
              ·
                refine ⟨10161253609724874665970013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13548338146299832887960017 10161253609724874665970013)
                ·
                  refine ⟨3810470103646827999738755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10161253609724874665970013 3810470103646827999738755)
                  ·
                    refine ⟨5715705155470241999608133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3810470103646827999738755 5715705155470241999608133)
                    ·
                      refine ⟨1071694716650670374926525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5715705155470241999608133 1071694716650670374926525)
                      ·
                        rfl

theorem cell23_2087118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_2087118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087118 prefixEnd_2087118 := by exact prefixLift 2087118
  have htrace : WordTrace (prefixWord ++ tailWord_2087118) baseStart_2087118 baseEnd_2087118 := by
    simpa [prefixWord, tailWord_2087118, baseEnd_2087118] using wordTrace_append hprefix tailTrace_2087118
  have hstable : (prefixWord ++ tailWord_2087118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087118).length < 2 ^ (prefixWord ++ tailWord_2087118).sum := by decide
  have hdescent : baseEnd_2087118 < baseStart_2087118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087121 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_2087121 : Nat := 118140960795 + 2087121 * 2 ^ 59
def prefixEnd_2087121 : Nat := 4983230072969 + 3 ^ 40 * 2087121 * 2
def baseEnd_2087121 : Nat := 1071696257092633863189011

theorem tailTrace_2087121 : CollatzResearch.WordTrace tailWord_2087121 prefixEnd_2087121 1071696257092633863189011 := by
  unfold tailWord_2087121
  simp only [CollatzResearch.WordTrace]
  refine ⟨76123556671724543733325217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50749037781149695822216811 76123556671724543733325217)
  ·
    refine ⟨57092667503793407799993913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76123556671724543733325217 57092667503793407799993913)
    ·
      refine ⟨42819500627845055849995435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57092667503793407799993913 42819500627845055849995435)
      ·
        refine ⟨64229250941767583774993153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42819500627845055849995435 64229250941767583774993153)
        ·
          refine ⟨48171938206325687831244865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64229250941767583774993153 48171938206325687831244865)
          ·
            refine ⟨36128953654744265873433649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48171938206325687831244865 36128953654744265873433649)
            ·
              refine ⟨27096715241058199405075237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36128953654744265873433649 27096715241058199405075237)
              ·
                refine ⟨5080634107698412388451607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27096715241058199405075237 5080634107698412388451607)
                ·
                  refine ⟨7620951161547618582677411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080634107698412388451607 7620951161547618582677411)
                  ·
                    refine ⟨11431426742321427874016117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620951161547618582677411 11431426742321427874016117)
                    ·
                      refine ⟨1071696257092633863189011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11431426742321427874016117 1071696257092633863189011)
                      ·
                        rfl

theorem cell23_2087121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_2087121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087121 prefixEnd_2087121 := by exact prefixLift 2087121
  have htrace : WordTrace (prefixWord ++ tailWord_2087121) baseStart_2087121 baseEnd_2087121 := by
    simpa [prefixWord, tailWord_2087121, baseEnd_2087121] using wordTrace_append hprefix tailTrace_2087121
  have hstable : (prefixWord ++ tailWord_2087121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087121).length < 2 ^ (prefixWord ++ tailWord_2087121).sum := by decide
  have hdescent : baseEnd_2087121 < baseStart_2087121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087128 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 1, 6]
def baseStart_2087128 : Nat := 118140960795 + 2087128 * 2 ^ 59
def prefixEnd_2087128 : Nat := 4983230072969 + 3 ^ 40 * 2087128 * 2
def baseEnd_2087128 : Nat := 357233283819071778600493

theorem tailTrace_2087128 : CollatzResearch.WordTrace tailWord_2087128 prefixEnd_2087128 357233283819071778600493 := by
  unfold tailWord_2087128
  simp only [CollatzResearch.WordTrace]
  refine ⟨38061905991349591964415019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50749207988466122619220025 38061905991349591964415019)
  ·
    refine ⟨57092858987024387946622529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38061905991349591964415019 57092858987024387946622529)
    ·
      refine ⟨42819644240268290959966897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57092858987024387946622529 42819644240268290959966897)
      ·
        refine ⟨32114733180201218219975173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42819644240268290959966897 32114733180201218219975173)
        ·
          refine ⟨6021512471287728416245345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32114733180201218219975173 6021512471287728416245345)
          ·
            refine ⟨4516134353465796312184009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6021512471287728416245345 4516134353465796312184009)
            ·
              refine ⟨3387100765099347234138007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516134353465796312184009 3387100765099347234138007)
              ·
                refine ⟨5080651147649020851207011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387100765099347234138007 5080651147649020851207011)
                ·
                  refine ⟨7620976721473531276810517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080651147649020851207011 7620976721473531276810517)
                  ·
                    refine ⟨357233283819071778600493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7620976721473531276810517 357233283819071778600493)
                    ·
                      rfl

theorem cell23_2087128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_2087128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087128 prefixEnd_2087128 := by exact prefixLift 2087128
  have htrace : WordTrace (prefixWord ++ tailWord_2087128) baseStart_2087128 baseEnd_2087128 := by
    simpa [prefixWord, tailWord_2087128, baseEnd_2087128] using wordTrace_append hprefix tailTrace_2087128
  have hstable : (prefixWord ++ tailWord_2087128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087128).length < 2 ^ (prefixWord ++ tailWord_2087128).sum := by decide
  have hdescent : baseEnd_2087128 < baseStart_2087128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087131 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4]
def baseStart_2087131 : Nat := 118140960795 + 2087131 * 2 ^ 59
def prefixEnd_2087131 : Nat := 4983230072969 + 3 ^ 40 * 2087131 * 2
def baseEnd_2087131 : Nat := 1071701391899178824063965

theorem tailTrace_2087131 : CollatzResearch.WordTrace tailWord_2087131 prefixEnd_2087131 1071701391899178824063965 := by
  unfold tailWord_2087131
  simp only [CollatzResearch.WordTrace]
  refine ⟨76123921401688315441189247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50749280934458876960792831 76123921401688315441189247)
  ·
    refine ⟨114185882102532473161783871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76123921401688315441189247 114185882102532473161783871)
    ·
      refine ⟨171278823153798709742675807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114185882102532473161783871 171278823153798709742675807)
      ·
        refine ⟨256918234730698064614013711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171278823153798709742675807 256918234730698064614013711)
        ·
          refine ⟨385377352096047096921020567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256918234730698064614013711 385377352096047096921020567)
          ·
            refine ⟨578066028144070645381530851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385377352096047096921020567 578066028144070645381530851)
            ·
              refine ⟨867099042216105968072296277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578066028144070645381530851 867099042216105968072296277)
              ·
                refine ⟨5080658450484995906673611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 867099042216105968072296277 5080658450484995906673611)
                ·
                  refine ⟨7620987675727493860010417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080658450484995906673611 7620987675727493860010417)
                  ·
                    refine ⟨5715740756795620395007813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620987675727493860010417 5715740756795620395007813)
                    ·
                      refine ⟨1071701391899178824063965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5715740756795620395007813 1071701391899178824063965)
                      ·
                        rfl

theorem cell23_2087131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].length) (baseStart_2087131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087131 prefixEnd_2087131 := by exact prefixLift 2087131
  have htrace : WordTrace (prefixWord ++ tailWord_2087131) baseStart_2087131 baseEnd_2087131 := by
    simpa [prefixWord, tailWord_2087131, baseEnd_2087131] using wordTrace_append hprefix tailTrace_2087131
  have hstable : (prefixWord ++ tailWord_2087131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087131).length < 2 ^ (prefixWord ++ tailWord_2087131).sum := by decide
  have hdescent : baseEnd_2087131 < baseStart_2087131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087139 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2087139 : Nat := 118140960795 + 2087139 * 2 ^ 59
def prefixEnd_2087139 : Nat := 4983230072969 + 3 ^ 40 * 2087139 * 2
def baseEnd_2087139 : Nat := 1071705499744414792763929

theorem tailTrace_2087139 : CollatzResearch.WordTrace tailWord_2087139 prefixEnd_2087139 1071705499744414792763929 := by
  unfold tailWord_2087139
  simp only [CollatzResearch.WordTrace]
  refine ⟨76124213185659332807480471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50749475457106221871653647 76124213185659332807480471)
  ·
    refine ⟨114186319778488999211220707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76124213185659332807480471 114186319778488999211220707)
    ·
      refine ⟨171279479667733498816831061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114186319778488999211220707 171279479667733498816831061)
      ·
        refine ⟨2007181402356251939259739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 171279479667733498816831061 2007181402356251939259739)
        ·
          refine ⟨3010772103534377908889609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007181402356251939259739 3010772103534377908889609)
          ·
            refine ⟨2258079077650783431667207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010772103534377908889609 2258079077650783431667207)
            ·
              refine ⟨3387118616476175147500811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258079077650783431667207 3387118616476175147500811)
              ·
                refine ⟨5080677924714262721251217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387118616476175147500811 5080677924714262721251217)
                ·
                  refine ⟨3810508443535697040938413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5080677924714262721251217 3810508443535697040938413)
                  ·
                    refine ⟨1428940666325886390351905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810508443535697040938413 1428940666325886390351905)
                    ·
                      refine ⟨1071705499744414792763929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428940666325886390351905 1071705499744414792763929)
                      ·
                        rfl

theorem cell23_2087139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2087139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087139 prefixEnd_2087139 := by exact prefixLift 2087139
  have htrace : WordTrace (prefixWord ++ tailWord_2087139) baseStart_2087139 baseEnd_2087139 := by
    simpa [prefixWord, tailWord_2087139, baseEnd_2087139] using wordTrace_append hprefix tailTrace_2087139
  have hstable : (prefixWord ++ tailWord_2087139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087139).length < 2 ^ (prefixWord ++ tailWord_2087139).sum := by decide
  have hdescent : baseEnd_2087139 < baseStart_2087139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087149 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_2087149 : Nat := 118140960795 + 2087149 * 2 ^ 59
def prefixEnd_2087149 : Nat := 4983230072969 + 3 ^ 40 * 2087149 * 2
def baseEnd_2087149 : Nat := 357236878183653251212961

theorem tailTrace_2087149 : CollatzResearch.WordTrace tailWord_2087149 prefixEnd_2087149 357236878183653251212961 := by
  unfold tailWord_2087149
  simp only [CollatzResearch.WordTrace]
  refine ⟨76124577915623104515344501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50749718610415403010229667 76124577915623104515344501)
  ·
    refine ⟨7136679179589666048313547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76124577915623104515344501 7136679179589666048313547)
    ·
      refine ⟨10705018769384499072470321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136679179589666048313547 10705018769384499072470321)
      ·
        refine ⟨8028764077038374304352741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10705018769384499072470321 8028764077038374304352741)
        ·
          refine ⟨1505393264444695182066139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8028764077038374304352741 1505393264444695182066139)
          ·
            refine ⟨2258089896667042773099209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505393264444695182066139 2258089896667042773099209)
            ·
              refine ⟨1693567422500282079824407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258089896667042773099209 1693567422500282079824407)
              ·
                refine ⟨2540351133750423119736611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693567422500282079824407 2540351133750423119736611)
                ·
                  refine ⟨3810526700625634679604917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540351133750423119736611 3810526700625634679604917)
                  ·
                    refine ⟨357236878183653251212961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3810526700625634679604917 357236878183653251212961)
                    ·
                      rfl

theorem cell23_2087149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_2087149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087149 prefixEnd_2087149 := by exact prefixLift 2087149
  have htrace : WordTrace (prefixWord ++ tailWord_2087149) baseStart_2087149 baseEnd_2087149 := by
    simpa [prefixWord, tailWord_2087149, baseEnd_2087149] using wordTrace_append hprefix tailTrace_2087149
  have hstable : (prefixWord ++ tailWord_2087149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087149).length < 2 ^ (prefixWord ++ tailWord_2087149).sum := by decide
  have hdescent : baseEnd_2087149 < baseStart_2087149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087185 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_2087185 : Nat := 118140960795 + 2087185 * 2 ^ 59
def prefixEnd_2087185 : Nat := 4983230072969 + 3 ^ 40 * 2087185 * 2
def baseEnd_2087185 : Nat := 1071729119854521612788717

theorem tailTrace_2087185 : CollatzResearch.WordTrace tailWord_2087185 prefixEnd_2087185 1071729119854521612788717 := by
  unfold tailWord_2087185
  simp only [CollatzResearch.WordTrace]
  refine ⟨76125890943492682663655009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50750593962328455109103339 76125890943492682663655009)
  ·
    refine ⟨57094418207619511997741257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76125890943492682663655009 57094418207619511997741257)
    ·
      refine ⟨42820813655714633998305943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57094418207619511997741257 42820813655714633998305943)
      ·
        refine ⟨64231220483571950997458915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42820813655714633998305943 64231220483571950997458915)
        ·
          refine ⟨96346830725357926496188373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64231220483571950997458915 96346830725357926496188373)
          ·
            refine ⟨2258128845125576402254415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 96346830725357926496188373 2258128845125576402254415)
            ·
              refine ⟨3387193267688364603381623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258128845125576402254415 3387193267688364603381623)
              ·
                refine ⟨5080789901532546905072435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387193267688364603381623 5080789901532546905072435)
                ·
                  refine ⟨7621184852298820357608653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080789901532546905072435 7621184852298820357608653)
                  ·
                    refine ⟨2857944319612057634103245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7621184852298820357608653 2857944319612057634103245)
                    ·
                      refine ⟨1071729119854521612788717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2857944319612057634103245 1071729119854521612788717)
                      ·
                        rfl

theorem cell23_2087185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_2087185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087185 prefixEnd_2087185 := by exact prefixLift 2087185
  have htrace : WordTrace (prefixWord ++ tailWord_2087185) baseStart_2087185 baseEnd_2087185 := by
    simpa [prefixWord, tailWord_2087185, baseEnd_2087185] using wordTrace_append hprefix tailTrace_2087185
  have hstable : (prefixWord ++ tailWord_2087185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087185).length < 2 ^ (prefixWord ++ tailWord_2087185).sum := by decide
  have hdescent : baseEnd_2087185 < baseStart_2087185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087195 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 1, 3, 2]
def baseStart_2087195 : Nat := 118140960795 + 2087195 * 2 ^ 59
def prefixEnd_2087195 : Nat := 4983230072969 + 3 ^ 40 * 2087195 * 2
def baseEnd_2087195 : Nat := 1071734254661066573663671

theorem tailTrace_2087195 : CollatzResearch.WordTrace tailWord_2087195 prefixEnd_2087195 1071734254661066573663671 := by
  unfold tailWord_2087195
  simp only [CollatzResearch.WordTrace]
  refine ⟨76126255673456454371519039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50750837115637636247679359 76126255673456454371519039)
  ·
    refine ⟨114189383510184681557278559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76126255673456454371519039 114189383510184681557278559)
    ·
      refine ⟨171284075265277022335917839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114189383510184681557278559 171284075265277022335917839)
      ·
        refine ⟨256926112897915533503876759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171284075265277022335917839 256926112897915533503876759)
        ·
          refine ⟨385389169346873300255815139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256926112897915533503876759 385389169346873300255815139)
          ·
            refine ⟨578083754020309950383722709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385389169346873300255815139 578083754020309950383722709)
            ·
              refine ⟨13548837984851014462118501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 578083754020309950383722709 13548837984851014462118501)
              ·
                refine ⟨2540407122159565211647219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13548837984851014462118501 2540407122159565211647219)
                ·
                  refine ⟨3810610683239347817470829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540407122159565211647219 3810610683239347817470829)
                  ·
                    refine ⟨1428979006214755431551561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810610683239347817470829 1428979006214755431551561)
                    ·
                      refine ⟨1071734254661066573663671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1428979006214755431551561 1071734254661066573663671)
                      ·
                        rfl

theorem cell23_2087195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 3, 2].length) (baseStart_2087195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087195 prefixEnd_2087195 := by exact prefixLift 2087195
  have htrace : WordTrace (prefixWord ++ tailWord_2087195) baseStart_2087195 baseEnd_2087195 := by
    simpa [prefixWord, tailWord_2087195, baseEnd_2087195] using wordTrace_append hprefix tailTrace_2087195
  have hstable : (prefixWord ++ tailWord_2087195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087195).length < 2 ^ (prefixWord ++ tailWord_2087195).sum := by decide
  have hdescent : baseEnd_2087195 < baseStart_2087195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087201 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2087201 : Nat := 118140960795 + 2087201 * 2 ^ 59
def prefixEnd_2087201 : Nat := 4983230072969 + 3 ^ 40 * 2087201 * 2
def baseEnd_2087201 : Nat := 357245778514997850062881

theorem tailTrace_2087201 : CollatzResearch.WordTrace tailWord_2087201 prefixEnd_2087201 357245778514997850062881 := by
  unfold tailWord_2087201
  simp only [CollatzResearch.WordTrace]
  refine ⟨76126474511434717396237457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50750983007623144930824971 76126474511434717396237457)
  ·
    refine ⟨57094855883576038047178093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76126474511434717396237457 57094855883576038047178093)
    ·
      refine ⟨21410570956341014267691785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57094855883576038047178093 21410570956341014267691785)
      ·
        refine ⟨16057928217255760700768839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21410570956341014267691785 16057928217255760700768839)
        ·
          refine ⟨24086892325883641051153259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057928217255760700768839 24086892325883641051153259)
          ·
            refine ⟨36130338488825461576729889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24086892325883641051153259 36130338488825461576729889)
            ·
              refine ⟨27097753866619096182547417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36130338488825461576729889 27097753866619096182547417)
              ·
                refine ⟨20323315399964322136910563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27097753866619096182547417 20323315399964322136910563)
                ·
                  refine ⟨30484973099946483205365845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20323315399964322136910563 30484973099946483205365845)
                  ·
                    refine ⟨357245778514997850062881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30484973099946483205365845 357245778514997850062881)
                    ·
                      rfl

theorem cell23_2087201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2087201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087201 prefixEnd_2087201 := by exact prefixLift 2087201
  have htrace : WordTrace (prefixWord ++ tailWord_2087201) baseStart_2087201 baseEnd_2087201 := by
    simpa [prefixWord, tailWord_2087201, baseEnd_2087201] using wordTrace_append hprefix tailTrace_2087201
  have hstable : (prefixWord ++ tailWord_2087201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087201).length < 2 ^ (prefixWord ++ tailWord_2087201).sum := by decide
  have hdescent : baseEnd_2087201 < baseStart_2087201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087228 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_2087228 : Nat := 118140960795 + 2087228 * 2 ^ 59
def prefixEnd_2087228 : Nat := 4983230072969 + 3 ^ 40 * 2087228 * 2
def baseEnd_2087228 : Nat := 1071751199522664944551019

theorem tailTrace_2087228 : CollatzResearch.WordTrace tailWord_2087228 prefixEnd_2087228 1071751199522664944551019 := by
  unfold tailWord_2087228
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063729641168450503735169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50751639521557934004980225 38063729641168450503735169)
  ·
    refine ⟨28547797230876337877801377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38063729641168450503735169 28547797230876337877801377)
    ·
      refine ⟨21410847923157253408351033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28547797230876337877801377 21410847923157253408351033)
      ·
        refine ⟨16058135942367940056263275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21410847923157253408351033 16058135942367940056263275)
        ·
          refine ⟨24087203913551910084394913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058135942367940056263275 24087203913551910084394913)
          ·
            refine ⟨18065402935163932563296185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087203913551910084394913 18065402935163932563296185)
            ·
              refine ⟨13549052201372949422472139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18065402935163932563296185 13549052201372949422472139)
              ·
                refine ⟨20323578302059424133708209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549052201372949422472139 20323578302059424133708209)
                ·
                  refine ⟨15242683726544568100281157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20323578302059424133708209 15242683726544568100281157)
                  ·
                    refine ⟨2858003198727106518802717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15242683726544568100281157 2858003198727106518802717)
                    ·
                      refine ⟨1071751199522664944551019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2858003198727106518802717 1071751199522664944551019)
                      ·
                        rfl

theorem cell23_2087228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_2087228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087228 prefixEnd_2087228 := by exact prefixLift 2087228
  have htrace : WordTrace (prefixWord ++ tailWord_2087228) baseStart_2087228 baseEnd_2087228 := by
    simpa [prefixWord, tailWord_2087228, baseEnd_2087228] using wordTrace_append hprefix tailTrace_2087228
  have hstable : (prefixWord ++ tailWord_2087228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087228).length < 2 ^ (prefixWord ++ tailWord_2087228).sum := by decide
  have hdescent : baseEnd_2087228 < baseStart_2087228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087258 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_2087258 : Nat := 118140960795 + 2087258 * 2 ^ 59
def prefixEnd_2087258 : Nat := 4983230072969 + 3 ^ 40 * 2087258 * 2
def baseEnd_2087258 : Nat := 1071766603942299827175881

theorem tailTrace_2087258 : CollatzResearch.WordTrace tailWord_2087258 prefixEnd_2087258 1071766603942299827175881 := by
  unfold tailWord_2087258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19032138368057054032765607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50752368981485477420708285 19032138368057054032765607)
  ·
    refine ⟨28548207552085581049148411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19032138368057054032765607 28548207552085581049148411)
    ·
      refine ⟨42822311328128371573722617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28548207552085581049148411 42822311328128371573722617)
      ·
        refine ⟨32116733496096278680291963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42822311328128371573722617 32116733496096278680291963)
        ·
          refine ⟨48175100244144418020437945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32116733496096278680291963 48175100244144418020437945)
          ·
            refine ⟨36131325183108313515328459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48175100244144418020437945 36131325183108313515328459)
            ·
              refine ⟨54196987774662470272992689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36131325183108313515328459 54196987774662470272992689)
              ·
                refine ⟨40647740830996852704744517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54196987774662470272992689 40647740830996852704744517)
                ·
                  refine ⟨7621451405811909882139597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40647740830996852704744517 7621451405811909882139597)
                  ·
                    refine ⟨2858044277179466205802349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7621451405811909882139597 2858044277179466205802349)
                    ·
                      refine ⟨1071766603942299827175881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2858044277179466205802349 1071766603942299827175881)
                      ·
                        rfl

theorem cell23_2087258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_2087258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087258 prefixEnd_2087258 := by exact prefixLift 2087258
  have htrace : WordTrace (prefixWord ++ tailWord_2087258) baseStart_2087258 baseEnd_2087258 := by
    simpa [prefixWord, tailWord_2087258, baseEnd_2087258] using wordTrace_append hprefix tailTrace_2087258
  have hstable : (prefixWord ++ tailWord_2087258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087258).length < 2 ^ (prefixWord ++ tailWord_2087258).sum := by decide
  have hdescent : baseEnd_2087258 < baseStart_2087258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087282 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_2087282 : Nat := 118140960795 + 2087282 * 2 ^ 59
def prefixEnd_2087282 : Nat := 4983230072969 + 3 ^ 40 * 2087282 * 2
def baseEnd_2087282 : Nat := 119086547497556414808419

theorem tailTrace_2087282 : CollatzResearch.WordTrace tailWord_2087282 prefixEnd_2087282 119086547497556414808419 := by
  unfold tailWord_2087282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19032357206035317057484025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50752952549427512153290733 19032357206035317057484025)
  ·
    refine ⟨14274267904526487793113019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19032357206035317057484025 14274267904526487793113019)
    ·
      refine ⟨21411401856789731689669529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14274267904526487793113019 21411401856789731689669529)
      ·
        refine ⟨16058551392592298767252147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21411401856789731689669529 16058551392592298767252147)
        ·
          refine ⟨24087827088888448150878221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058551392592298767252147 24087827088888448150878221)
          ·
            refine ⟨9032935158333168056579333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24087827088888448150878221 9032935158333168056579333)
            ·
              refine ⟨1693675342187469010608625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9032935158333168056579333 1693675342187469010608625)
              ·
                refine ⟨1270256506640601757956469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693675342187469010608625 1270256506640601757956469)
                ·
                  refine ⟨119086547497556414808419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1270256506640601757956469 119086547497556414808419)
                  ·
                    rfl

theorem cell23_2087282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_2087282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087282 prefixEnd_2087282 := by exact prefixLift 2087282
  have htrace : WordTrace (prefixWord ++ tailWord_2087282) baseStart_2087282 baseEnd_2087282 := by
    simpa [prefixWord, tailWord_2087282, baseEnd_2087282] using wordTrace_append hprefix tailTrace_2087282
  have hstable : (prefixWord ++ tailWord_2087282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087282).length < 2 ^ (prefixWord ++ tailWord_2087282).sum := by decide
  have hdescent : baseEnd_2087282 < baseStart_2087282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087328 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2087328 : Nat := 118140960795 + 2087328 * 2 ^ 59
def prefixEnd_2087328 : Nat := 4983230072969 + 3 ^ 40 * 2087328 * 2
def baseEnd_2087328 : Nat := 1071802547588114553300559

theorem tailTrace_2087328 : CollatzResearch.WordTrace tailWord_2087328 prefixEnd_2087328 1071802547588114553300559 := by
  unfold tailWord_2087328
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065553290987309043055319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50754071054649745390740425 38065553290987309043055319)
  ·
    refine ⟨57098329936480963564582979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38065553290987309043055319 57098329936480963564582979)
    ·
      refine ⟨85647494904721445346874469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57098329936480963564582979 85647494904721445346874469)
      ·
        refine ⟨16058905294635271002538963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85647494904721445346874469 16058905294635271002538963)
        ·
          refine ⟨24088357941952906503808445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058905294635271002538963 24088357941952906503808445)
          ·
            refine ⟨9033134228232339938928167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24088357941952906503808445 9033134228232339938928167)
            ·
              refine ⟨13549701342348509908392251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033134228232339938928167 13549701342348509908392251)
              ·
                refine ⟨20324552013522764862588377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549701342348509908392251 20324552013522764862588377)
                ·
                  refine ⟨15243414010142073646941283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20324552013522764862588377 15243414010142073646941283)
                  ·
                    refine ⟨22865121015213110470411925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15243414010142073646941283 22865121015213110470411925)
                    ·
                      refine ⟨1071802547588114553300559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22865121015213110470411925 1071802547588114553300559)
                      ·
                        rfl

theorem cell23_2087328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2087328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087328 prefixEnd_2087328 := by exact prefixLift 2087328
  have htrace : WordTrace (prefixWord ++ tailWord_2087328) baseStart_2087328 baseEnd_2087328 := by
    simpa [prefixWord, tailWord_2087328, baseEnd_2087328] using wordTrace_append hprefix tailTrace_2087328
  have hstable : (prefixWord ++ tailWord_2087328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087328).length < 2 ^ (prefixWord ++ tailWord_2087328).sum := by decide
  have hdescent : baseEnd_2087328 < baseStart_2087328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087385 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 1, 5]
def baseStart_2087385 : Nat := 118140960795 + 2087385 * 2 ^ 59
def prefixEnd_2087385 : Nat := 4983230072969 + 3 ^ 40 * 2087385 * 2
def baseEnd_2087385 : Nat := 357277271995140276762599

theorem tailTrace_2087385 : CollatzResearch.WordTrace tailWord_2087385 prefixEnd_2087385 357277271995140276762599 := by
  unfold tailWord_2087385
  simp only [CollatzResearch.WordTrace]
  refine ⟨76133185542768116820935609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50755457028512077880623739 76133185542768116820935609)
  ·
    refine ⟨57099889157076087615701707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76133185542768116820935609 57099889157076087615701707)
    ·
      refine ⟨85649833735614131423552561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57099889157076087615701707 85649833735614131423552561)
      ·
        refine ⟨64237375301710598567664421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85649833735614131423552561 64237375301710598567664421)
        ·
          refine ⟨12044507869070737231437079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64237375301710598567664421 12044507869070737231437079)
          ·
            refine ⟨18066761803606105847155619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044507869070737231437079 18066761803606105847155619)
            ·
              refine ⟨27100142705409158770733429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18066761803606105847155619 27100142705409158770733429)
              ·
                refine ⟨2540638378632108634756259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27100142705409158770733429 2540638378632108634756259)
                ·
                  refine ⟨3810957567948162952134389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540638378632108634756259 3810957567948162952134389)
                  ·
                    refine ⟨357277271995140276762599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3810957567948162952134389 357277271995140276762599)
                    ·
                      rfl

theorem cell23_2087385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_2087385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087385 prefixEnd_2087385 := by exact prefixLift 2087385
  have htrace : WordTrace (prefixWord ++ tailWord_2087385) baseStart_2087385 baseEnd_2087385 := by
    simpa [prefixWord, tailWord_2087385, baseEnd_2087385] using wordTrace_append hprefix tailTrace_2087385
  have hstable : (prefixWord ++ tailWord_2087385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087385).length < 2 ^ (prefixWord ++ tailWord_2087385).sum := by decide
  have hdescent : baseEnd_2087385 < baseStart_2087385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087392 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 2, 3, 2]
def baseStart_2087392 : Nat := 118140960795 + 2087392 * 2 ^ 59
def prefixEnd_2087392 : Nat := 4983230072969 + 3 ^ 40 * 2087392 * 2
def baseEnd_2087392 : Nat := 1071835410350002302900265

theorem tailTrace_2087392 : CollatzResearch.WordTrace tailWord_2087392 prefixEnd_2087392 1071835410350002302900265 := by
  unfold tailWord_2087392
  simp only [CollatzResearch.WordTrace]
  refine ⟨38066720426871378508220215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50755627235828504677626953 38066720426871378508220215)
  ·
    refine ⟨57100080640307067762330323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38066720426871378508220215 57100080640307067762330323)
    ·
      refine ⟨85650120960460601643495485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57100080640307067762330323 85650120960460601643495485)
      ·
        refine ⟨32118795360172725616310807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85650120960460601643495485 32118795360172725616310807)
        ·
          refine ⟨48178193040259088424466211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32118795360172725616310807 48178193040259088424466211)
          ·
            refine ⟨72267289560388632636699317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48178193040259088424466211 72267289560388632636699317)
            ·
              refine ⟨6775058396286434309690561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72267289560388632636699317 6775058396286434309690561)
              ·
                refine ⟨5081293797214825732267921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6775058396286434309690561 5081293797214825732267921)
                ·
                  refine ⟨3810970347911119299200941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081293797214825732267921 3810970347911119299200941)
                  ·
                    refine ⟨1429113880466669737200353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810970347911119299200941 1429113880466669737200353)
                    ·
                      refine ⟨1071835410350002302900265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429113880466669737200353 1071835410350002302900265)
                      ·
                        rfl

theorem cell23_2087392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_2087392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087392 prefixEnd_2087392 := by exact prefixLift 2087392
  have htrace : WordTrace (prefixWord ++ tailWord_2087392) baseStart_2087392 baseEnd_2087392 := by
    simpa [prefixWord, tailWord_2087392, baseEnd_2087392] using wordTrace_append hprefix tailTrace_2087392
  have hstable : (prefixWord ++ tailWord_2087392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087392).length < 2 ^ (prefixWord ++ tailWord_2087392).sum := by decide
  have hdescent : baseEnd_2087392 < baseStart_2087392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087435 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4]
def baseStart_2087435 : Nat := 118140960795 + 2087435 * 2 ^ 59
def prefixEnd_2087435 : Nat := 4983230072969 + 3 ^ 40 * 2087435 * 2
def baseEnd_2087435 : Nat := 1071857490018145634662567

theorem tailTrace_2087435 : CollatzResearch.WordTrace tailWord_2087435 prefixEnd_2087435 1071857490018145634662567 := by
  unfold tailWord_2087435
  simp only [CollatzResearch.WordTrace]
  refine ⟨76135009192586975360255759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50756672795057983573503839 76135009192586975360255759)
  ·
    refine ⟨114202513788880463040383639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76135009192586975360255759 114202513788880463040383639)
    ·
      refine ⟨171303770683320694560575459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114202513788880463040383639 171303770683320694560575459)
      ·
        refine ⟨256955656024981041840863189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171303770683320694560575459 256955656024981041840863189)
        ·
          refine ⟨6022398188085493168145231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 256955656024981041840863189 6022398188085493168145231)
          ·
            refine ⟨9033597282128239752217847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022398188085493168145231 9033597282128239752217847)
            ·
              refine ⟨13550395923192359628326771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033597282128239752217847 13550395923192359628326771)
              ·
                refine ⟨20325593884788539442490157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550395923192359628326771 20325593884788539442490157)
                ·
                  refine ⟨7622097706795702290933809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20325593884788539442490157 7622097706795702290933809)
                  ·
                    refine ⟨5716573280096776718200357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622097706795702290933809 5716573280096776718200357)
                    ·
                      refine ⟨1071857490018145634662567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5716573280096776718200357 1071857490018145634662567)
                      ·
                        rfl

theorem cell23_2087435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_2087435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087435 prefixEnd_2087435 := by exact prefixLift 2087435
  have htrace : WordTrace (prefixWord ++ tailWord_2087435) baseStart_2087435 baseEnd_2087435 := by
    simpa [prefixWord, tailWord_2087435, baseEnd_2087435] using wordTrace_append hprefix tailTrace_2087435
  have hstable : (prefixWord ++ tailWord_2087435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087435).length < 2 ^ (prefixWord ++ tailWord_2087435).sum := by decide
  have hdescent : baseEnd_2087435 < baseStart_2087435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087455 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2087455 : Nat := 118140960795 + 2087455 * 2 ^ 59
def prefixEnd_2087455 : Nat := 4983230072969 + 3 ^ 40 * 2087455 * 2
def baseEnd_2087455 : Nat := 1071867759631235556412475

theorem tailTrace_2087455 : CollatzResearch.WordTrace tailWord_2087455 prefixEnd_2087455 1071867759631235556412475 := by
  unfold tailWord_2087455
  simp only [CollatzResearch.WordTrace]
  refine ⟨76135738652514518775983819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50757159101676345850655879 76135738652514518775983819)
  ·
    refine ⟨114203607978771778163975729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76135738652514518775983819 114203607978771778163975729)
    ·
      refine ⟨85652705984078833622981797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114203607978771778163975729 85652705984078833622981797)
      ·
        refine ⟨16059882372014781304309087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85652705984078833622981797 16059882372014781304309087)
        ·
          refine ⟨24089823558022171956463631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16059882372014781304309087 24089823558022171956463631)
          ·
            refine ⟨36134735337033257934695447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24089823558022171956463631 36134735337033257934695447)
            ·
              refine ⟨54202103005549886902043171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36134735337033257934695447 54202103005549886902043171)
              ·
                refine ⟨81303154508324830353064757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54202103005549886902043171 81303154508324830353064757)
                ·
                  refine ⟨7622170735155452845599821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81303154508324830353064757 7622170735155452845599821)
                  ·
                    refine ⟨2858314025683294817099933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7622170735155452845599821 2858314025683294817099933)
                    ·
                      refine ⟨1071867759631235556412475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2858314025683294817099933 1071867759631235556412475)
                      ·
                        rfl

theorem cell23_2087455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2087455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087455 prefixEnd_2087455 := by exact prefixLift 2087455
  have htrace : WordTrace (prefixWord ++ tailWord_2087455) baseStart_2087455 baseEnd_2087455 := by
    simpa [prefixWord, tailWord_2087455, baseEnd_2087455] using wordTrace_append hprefix tailTrace_2087455
  have hstable : (prefixWord ++ tailWord_2087455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087455).length < 2 ^ (prefixWord ++ tailWord_2087455).sum := by decide
  have hdescent : baseEnd_2087455 < baseStart_2087455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087505 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_2087505 : Nat := 118140960795 + 2087505 * 2 ^ 59
def prefixEnd_2087505 : Nat := 4983230072969 + 3 ^ 40 * 2087505 * 2
def baseEnd_2087505 : Nat := 357297811221320120262415

theorem tailTrace_2087505 : CollatzResearch.WordTrace tailWord_2087505 prefixEnd_2087505 357297811221320120262415 := by
  unfold tailWord_2087505
  simp only [CollatzResearch.WordTrace]
  refine ⟨76137562302333377315303969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50758374868222251543535979 76137562302333377315303969)
  ·
    refine ⟨57103171726750032986477977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76137562302333377315303969 57103171726750032986477977)
    ·
      refine ⟨42827378795062524739858483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57103171726750032986477977 42827378795062524739858483)
      ·
        refine ⟨64241068192593787109787725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42827378795062524739858483 64241068192593787109787725)
        ·
          refine ⟨24090400572222670166170397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64241068192593787109787725 24090400572222670166170397)
          ·
            refine ⟨9033900214583501312313899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24090400572222670166170397 9033900214583501312313899)
            ·
              refine ⟨13550850321875251968470849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033900214583501312313899 13550850321875251968470849)
              ·
                refine ⟨10163137741406438976353137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13550850321875251968470849 10163137741406438976353137)
                ·
                  refine ⟨7622353306054829232264853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163137741406438976353137 7622353306054829232264853)
                  ·
                    refine ⟨357297811221320120262415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7622353306054829232264853 357297811221320120262415)
                    ·
                      rfl

theorem cell23_2087505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_2087505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087505 prefixEnd_2087505 := by exact prefixLift 2087505
  have htrace : WordTrace (prefixWord ++ tailWord_2087505) baseStart_2087505 baseEnd_2087505 := by
    simpa [prefixWord, tailWord_2087505, baseEnd_2087505] using wordTrace_append hprefix tailTrace_2087505
  have hstable : (prefixWord ++ tailWord_2087505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087505).length < 2 ^ (prefixWord ++ tailWord_2087505).sum := by decide
  have hdescent : baseEnd_2087505 < baseStart_2087505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087512 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 3, 4, 2]
def baseStart_2087512 : Nat := 118140960795 + 2087512 * 2 ^ 59
def prefixEnd_2087512 : Nat := 4983230072969 + 3 ^ 40 * 2087512 * 2
def baseEnd_2087512 : Nat := 1071897028028541833399713

theorem tailTrace_2087512 : CollatzResearch.WordTrace tailWord_2087512 prefixEnd_2087512 1071897028028541833399713 := by
  unfold tailWord_2087512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38068908806654008755404395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50758545075538678340539193 38068908806654008755404395)
  ·
    refine ⟨57103363209981013133106593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38068908806654008755404395 57103363209981013133106593)
    ·
      refine ⟨42827522407485759849829945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57103363209981013133106593 42827522407485759849829945)
      ·
        refine ⟨32120641805614319887372459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42827522407485759849829945 32120641805614319887372459)
        ·
          refine ⟨48180962708421479831058689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32120641805614319887372459 48180962708421479831058689)
          ·
            refine ⟨36135722031316109873294017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48180962708421479831058689 36135722031316109873294017)
            ·
              refine ⟨27101791523487082404970513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36135722031316109873294017 27101791523487082404970513)
              ·
                refine ⟨20326343642615311803727885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27101791523487082404970513 20326343642615311803727885)
                ·
                  refine ⟨7622378865980741926397957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20326343642615311803727885 7622378865980741926397957)
                  ·
                    refine ⟨1429196037371389111199617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622378865980741926397957 1429196037371389111199617)
                    ·
                      refine ⟨1071897028028541833399713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429196037371389111199617 1071897028028541833399713)
                      ·
                        rfl

theorem cell23_2087512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_2087512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087512 prefixEnd_2087512 := by exact prefixLift 2087512
  have htrace : WordTrace (prefixWord ++ tailWord_2087512) baseStart_2087512 baseEnd_2087512 := by
    simpa [prefixWord, tailWord_2087512, baseEnd_2087512] using wordTrace_append hprefix tailTrace_2087512
  have hstable : (prefixWord ++ tailWord_2087512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087512).length < 2 ^ (prefixWord ++ tailWord_2087512).sum := by decide
  have hdescent : baseEnd_2087512 < baseStart_2087512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087535 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 7]
def baseStart_2087535 : Nat := 118140960795 + 2087535 * 2 ^ 59
def prefixEnd_2087535 : Nat := 4983230072969 + 3 ^ 40 * 2087535 * 2
def baseEnd_2087535 : Nat := 119100982009288360379123

theorem tailTrace_2087535 : CollatzResearch.WordTrace tailWord_2087535 prefixEnd_2087535 119100982009288360379123 := by
  unfold tailWord_2087535
  simp only [CollatzResearch.WordTrace]
  refine ⟨76138656492224692438896059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50759104328149794959264039 76138656492224692438896059)
  ·
    refine ⟨114207984738337038658344089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76138656492224692438896059 114207984738337038658344089)
    ·
      refine ⟨85655988553752778993758067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114207984738337038658344089 85655988553752778993758067)
      ·
        refine ⟨128483982830629168490637101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85655988553752778993758067 128483982830629168490637101)
        ·
          refine ⟨48181493561485938183988913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128483982830629168490637101 48181493561485938183988913)
          ·
            refine ⟨36136120171114453637991685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48181493561485938183988913 36136120171114453637991685)
            ·
              refine ⟨6775522532083960057123441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36136120171114453637991685 6775522532083960057123441)
              ·
                refine ⟨5081641899062970042842581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6775522532083960057123441 5081641899062970042842581)
                ·
                  refine ⟨119100982009288360379123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5081641899062970042842581 119100982009288360379123)
                  ·
                    rfl

theorem cell23_2087535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 7].length) (baseStart_2087535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087535 prefixEnd_2087535 := by exact prefixLift 2087535
  have htrace : WordTrace (prefixWord ++ tailWord_2087535) baseStart_2087535 baseEnd_2087535 := by
    simpa [prefixWord, tailWord_2087535, baseEnd_2087535] using wordTrace_append hprefix tailTrace_2087535
  have hstable : (prefixWord ++ tailWord_2087535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087535).length < 2 ^ (prefixWord ++ tailWord_2087535).sum := by decide
  have hdescent : baseEnd_2087535 < baseStart_2087535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087580 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2087580 : Nat := 118140960795 + 2087580 * 2 ^ 59
def prefixEnd_2087580 : Nat := 4983230072969 + 3 ^ 40 * 2087580 * 2
def baseEnd_2087580 : Nat := 1071931944713047567349401

theorem tailTrace_2087580 : CollatzResearch.WordTrace tailWord_2087580 prefixEnd_2087580 1071931944713047567349401 := by
  unfold tailWord_2087580
  simp only [CollatzResearch.WordTrace]
  refine ⟨38070148888530832562142097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50760198518041110082856129 38070148888530832562142097)
  ·
    refine ⟨28552611666398124421606573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38070148888530832562142097 28552611666398124421606573)
    ·
      refine ⟨10707229374899296658102465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28552611666398124421606573 10707229374899296658102465)
      ·
        refine ⟨8030422031174472493576849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10707229374899296658102465 8030422031174472493576849)
        ·
          refine ⟨6022816523380854370182637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8030422031174472493576849 6022816523380854370182637)
          ·
            refine ⟨2258556196267820388818489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6022816523380854370182637 2258556196267820388818489)
            ·
              refine ⟨1693917147200865291613867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258556196267820388818489 1693917147200865291613867)
              ·
                refine ⟨2540875720801297937420801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693917147200865291613867 2540875720801297937420801)
                ·
                  refine ⟨1905656790600973453065601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2540875720801297937420801 1905656790600973453065601)
                  ·
                    refine ⟨1429242592950730089799201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1905656790600973453065601 1429242592950730089799201)
                    ·
                      refine ⟨1071931944713047567349401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429242592950730089799201 1071931944713047567349401)
                      ·
                        rfl

theorem cell23_2087580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2087580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087580 prefixEnd_2087580 := by exact prefixLift 2087580
  have htrace : WordTrace (prefixWord ++ tailWord_2087580) baseStart_2087580 baseEnd_2087580 := by
    simpa [prefixWord, tailWord_2087580, baseEnd_2087580] using wordTrace_append hprefix tailTrace_2087580
  have hstable : (prefixWord ++ tailWord_2087580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087580).length < 2 ^ (prefixWord ++ tailWord_2087580).sum := by decide
  have hdescent : baseEnd_2087580 < baseStart_2087580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087642 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_2087642 : Nat := 118140960795 + 2087642 * 2 ^ 59
def prefixEnd_2087642 : Nat := 4983230072969 + 3 ^ 40 * 2087642 * 2
def baseEnd_2087642 : Nat := 119107086723736258308235

theorem tailTrace_2087642 : CollatzResearch.WordTrace tailWord_2087642 prefixEnd_2087642 119107086723736258308235 := by
  unfold tailWord_2087642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19035639775709262428260295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50761706068558033142027453 19035639775709262428260295)
  ·
    refine ⟨28553459663563893642390443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19035639775709262428260295 28553459663563893642390443)
    ·
      refine ⟨42830189495345840463585665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28553459663563893642390443 42830189495345840463585665)
      ·
        refine ⟨32122642121509380347689249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42830189495345840463585665 32122642121509380347689249)
        ·
          refine ⟨24091981591132035260766937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32122642121509380347689249 24091981591132035260766937)
          ·
            refine ⟨18068986193349026445575203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24091981591132035260766937 18068986193349026445575203)
            ·
              refine ⟨27103479290023539668362805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18068986193349026445575203 27103479290023539668362805)
              ·
                refine ⟨2540951183439706843909013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27103479290023539668362805 2540951183439706843909013)
                ·
                  refine ⟨119107086723736258308235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2540951183439706843909013 119107086723736258308235)
                  ·
                    rfl

theorem cell23_2087642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_2087642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087642 prefixEnd_2087642 := by exact prefixLift 2087642
  have htrace : WordTrace (prefixWord ++ tailWord_2087642) baseStart_2087642 baseEnd_2087642 := by
    simpa [prefixWord, tailWord_2087642, baseEnd_2087642] using wordTrace_append hprefix tailTrace_2087642
  have hstable : (prefixWord ++ tailWord_2087642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087642).length < 2 ^ (prefixWord ++ tailWord_2087642).sum := by decide
  have hdescent : baseEnd_2087642 < baseStart_2087642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087679 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 4, 3, 2]
def baseStart_2087679 : Nat := 118140960795 + 2087679 * 2 ^ 59
def prefixEnd_2087679 : Nat := 4983230072969 + 3 ^ 40 * 2087679 * 2
def baseEnd_2087679 : Nat := 1071982779297842680011445

theorem tailTrace_2087679 : CollatzResearch.WordTrace tailWord_2087679 prefixEnd_2087679 1071982779297842680011445 := by
  unfold tailWord_2087679
  simp only [CollatzResearch.WordTrace]
  refine ⟨76143908603703005032138091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50762605735802003354758727 76143908603703005032138091)
  ·
    refine ⟨114215862905554507548207137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76143908603703005032138091 114215862905554507548207137)
    ·
      refine ⟨85661897179165880661155353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114215862905554507548207137 85661897179165880661155353)
      ·
        refine ⟨64246422884374410495866515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85661897179165880661155353 64246422884374410495866515)
        ·
          refine ⟨96369634326561615743799773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64246422884374410495866515 96369634326561615743799773)
          ·
            refine ⟨36138612872460605903924915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96369634326561615743799773 36138612872460605903924915)
            ·
              refine ⟨54207919308690908855887373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36138612872460605903924915 54207919308690908855887373)
              ·
                refine ⟨20327969740759090820957765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54207919308690908855887373 20327969740759090820957765)
                ·
                  refine ⟨3811494326392329528929581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20327969740759090820957765 3811494326392329528929581)
                  ·
                    refine ⟨1429310372397123573348593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3811494326392329528929581 1429310372397123573348593)
                    ·
                      refine ⟨1071982779297842680011445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429310372397123573348593 1071982779297842680011445)
                      ·
                        rfl

theorem cell23_2087679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_2087679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087679 prefixEnd_2087679 := by exact prefixLift 2087679
  have htrace : WordTrace (prefixWord ++ tailWord_2087679) baseStart_2087679 baseEnd_2087679 := by
    simpa [prefixWord, tailWord_2087679, baseEnd_2087679] using wordTrace_append hprefix tailTrace_2087679
  have hstable : (prefixWord ++ tailWord_2087679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087679).length < 2 ^ (prefixWord ++ tailWord_2087679).sum := by decide
  have hdescent : baseEnd_2087679 < baseStart_2087679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087729 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_2087729 : Nat := 118140960795 + 2087729 * 2 ^ 59
def prefixEnd_2087729 : Nat := 4983230072969 + 3 ^ 40 * 2087729 * 2
def baseEnd_2087729 : Nat := 1072008453330567484386215

theorem tailTrace_2087729 : CollatzResearch.WordTrace tailWord_2087729 prefixEnd_2087729 1072008453330567484386215 := by
  unfold tailWord_2087729
  simp only [CollatzResearch.WordTrace]
  refine ⟨76145732253521863571458241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50763821502347909047638827 76145732253521863571458241)
  ·
    refine ⟨57109299190141397678593681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76145732253521863571458241 57109299190141397678593681)
    ·
      refine ⟨42831974392606048258945261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57109299190141397678593681 42831974392606048258945261)
      ·
        refine ⟨16061990397227268097104473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42831974392606048258945261 16061990397227268097104473)
        ·
          refine ⟨12046492797920451072828355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16061990397227268097104473 12046492797920451072828355)
          ·
            refine ⟨18069739196880676609242533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12046492797920451072828355 18069739196880676609242533)
            ·
              refine ⟨3388076099415126864232975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18069739196880676609242533 3388076099415126864232975)
              ·
                refine ⟨5082114149122690296349463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388076099415126864232975 5082114149122690296349463)
                ·
                  refine ⟨7623171223684035444524195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082114149122690296349463 7623171223684035444524195)
                  ·
                    refine ⟨11434756835526053166786293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7623171223684035444524195 11434756835526053166786293)
                    ·
                      refine ⟨1072008453330567484386215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11434756835526053166786293 1072008453330567484386215)
                      ·
                        rfl

theorem cell23_2087729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_2087729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087729 prefixEnd_2087729 := by exact prefixLift 2087729
  have htrace : WordTrace (prefixWord ++ tailWord_2087729) baseStart_2087729 baseEnd_2087729 := by
    simpa [prefixWord, tailWord_2087729, baseEnd_2087729] using wordTrace_append hprefix tailTrace_2087729
  have hstable : (prefixWord ++ tailWord_2087729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087729).length < 2 ^ (prefixWord ++ tailWord_2087729).sum := by decide
  have hdescent : baseEnd_2087729 < baseStart_2087729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087743 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 3, 2, 2]
def baseStart_2087743 : Nat := 118140960795 + 2087743 * 2 ^ 59
def prefixEnd_2087743 : Nat := 4983230072969 + 3 ^ 40 * 2087743 * 2
def baseEnd_2087743 : Nat := 1072015642059730429611151

theorem tailTrace_2087743 : CollatzResearch.WordTrace tailWord_2087743 prefixEnd_2087743 1072015642059730429611151 := by
  unfold tailWord_2087743
  simp only [CollatzResearch.WordTrace]
  refine ⟨76146242875471143962467883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50764161916980762641645255 76146242875471143962467883)
  ·
    refine ⟨114219364313206715943701825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76146242875471143962467883 114219364313206715943701825)
    ·
      refine ⟨85664523234905036957776369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114219364313206715943701825 85664523234905036957776369)
      ·
        refine ⟨64248392426178777718332277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85664523234905036957776369 64248392426178777718332277)
        ·
          refine ⟨6023286789954260411093651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64248392426178777718332277 6023286789954260411093651)
          ·
            refine ⟨9034930184931390616640477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023286789954260411093651 9034930184931390616640477)
            ·
              refine ⟨3388098819349271481240179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9034930184931390616640477 3388098819349271481240179)
              ·
                refine ⟨5082148229023907221860269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388098819349271481240179 5082148229023907221860269)
                ·
                  refine ⟨1905805585883965208197601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5082148229023907221860269 1905805585883965208197601)
                  ·
                    refine ⟨1429354189412973906148201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1905805585883965208197601 1429354189412973906148201)
                    ·
                      refine ⟨1072015642059730429611151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429354189412973906148201 1072015642059730429611151)
                      ·
                        rfl

theorem cell23_2087743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_2087743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087743 prefixEnd_2087743 := by exact prefixLift 2087743
  have htrace : WordTrace (prefixWord ++ tailWord_2087743) baseStart_2087743 baseEnd_2087743 := by
    simpa [prefixWord, tailWord_2087743, baseEnd_2087743] using wordTrace_append hprefix tailTrace_2087743
  have hstable : (prefixWord ++ tailWord_2087743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087743).length < 2 ^ (prefixWord ++ tailWord_2087743).sum := by decide
  have hdescent : baseEnd_2087743 < baseStart_2087743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087752 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2087752 : Nat := 118140960795 + 2087752 * 2 ^ 59
def prefixEnd_2087752 : Nat := 4983230072969 + 3 ^ 40 * 2087752 * 2
def baseEnd_2087752 : Nat := 1072020263385620894398609

theorem tailTrace_2087752 : CollatzResearch.WordTrace tailWord_2087752 prefixEnd_2087752 1072020263385620894398609 := by
  unfold tailWord_2087752
  simp only [CollatzResearch.WordTrace]
  refine ⟨38073285566219269249772755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50764380754959025666363673 38073285566219269249772755)
  ·
    refine ⟨57109928349328903874659133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38073285566219269249772755 57109928349328903874659133)
    ·
      refine ⟨21416223130998338952997175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57109928349328903874659133 21416223130998338952997175)
      ·
        refine ⟨32124334696497508429495763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21416223130998338952997175 32124334696497508429495763)
        ·
          refine ⟨48186502044746262644243645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32124334696497508429495763 48186502044746262644243645)
          ·
            refine ⟨18069938266779848491591367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48186502044746262644243645 18069938266779848491591367)
            ·
              refine ⟨27104907400169772737387051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18069938266779848491591367 27104907400169772737387051)
              ·
                refine ⟨40657361100254659106080577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27104907400169772737387051 40657361100254659106080577)
                ·
                  refine ⟨30493020825190994329560433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40657361100254659106080577 30493020825190994329560433)
                  ·
                    refine ⟨22869765618893245747170325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30493020825190994329560433 22869765618893245747170325)
                    ·
                      refine ⟨1072020263385620894398609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22869765618893245747170325 1072020263385620894398609)
                      ·
                        rfl

theorem cell23_2087752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2087752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087752 prefixEnd_2087752 := by exact prefixLift 2087752
  have htrace : WordTrace (prefixWord ++ tailWord_2087752) baseStart_2087752 baseEnd_2087752 := by
    simpa [prefixWord, tailWord_2087752, baseEnd_2087752] using wordTrace_append hprefix tailTrace_2087752
  have hstable : (prefixWord ++ tailWord_2087752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087752).length < 2 ^ (prefixWord ++ tailWord_2087752).sum := by decide
  have hdescent : baseEnd_2087752 < baseStart_2087752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087753 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 2, 4]
def baseStart_2087753 : Nat := 118140960795 + 2087753 * 2 ^ 59
def prefixEnd_2087753 : Nat := 4983230072969 + 3 ^ 40 * 2087753 * 2
def baseEnd_2087753 : Nat := 357340258955425130162035

theorem tailTrace_2087753 : CollatzResearch.WordTrace tailWord_2087753 prefixEnd_2087753 357340258955425130162035 := by
  unfold tailWord_2087753
  simp only [CollatzResearch.WordTrace]
  refine ⟨76146607605434915670331913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50764405070289943780221275 76146607605434915670331913)
  ·
    refine ⟨57109955704076186752748935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76146607605434915670331913 57109955704076186752748935)
    ·
      refine ⟨85664933556114280129123403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57109955704076186752748935 85664933556114280129123403)
      ·
        refine ⟨128497400334171420193685105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85664933556114280129123403 128497400334171420193685105)
        ·
          refine ⟨96373050250628565145263829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128497400334171420193685105 96373050250628565145263829)
          ·
            refine ⟨2258743365249106995592121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 96373050250628565145263829 2258743365249106995592121)
            ·
              refine ⟨1694057523936830246694091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258743365249106995592121 1694057523936830246694091)
              ·
                refine ⟨2541086285905245370041137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694057523936830246694091 2541086285905245370041137)
                ·
                  refine ⟨1905814714428934027530853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541086285905245370041137 1905814714428934027530853)
                  ·
                    refine ⟨357340258955425130162035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1905814714428934027530853 357340258955425130162035)
                    ·
                      rfl

theorem cell23_2087753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 4].length) (baseStart_2087753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087753 prefixEnd_2087753 := by exact prefixLift 2087753
  have htrace : WordTrace (prefixWord ++ tailWord_2087753) baseStart_2087753 baseEnd_2087753 := by
    simpa [prefixWord, tailWord_2087753, baseEnd_2087753] using wordTrace_append hprefix tailTrace_2087753
  have hstable : (prefixWord ++ tailWord_2087753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087753).length < 2 ^ (prefixWord ++ tailWord_2087753).sum := by decide
  have hdescent : baseEnd_2087753 < baseStart_2087753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087793 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_2087793 : Nat := 118140960795 + 2087793 * 2 ^ 59
def prefixEnd_2087793 : Nat := 4983230072969 + 3 ^ 40 * 2087793 * 2
def baseEnd_2087793 : Nat := 1072041316092455233985921

theorem tailTrace_2087793 : CollatzResearch.WordTrace tailWord_2087793 prefixEnd_2087793 1072041316092455233985921 := by
  unfold tailWord_2087793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76148066525290002501788033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50765377683526668334525355 76148066525290002501788033)
  ·
    refine ⟨57111049893967501876341025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76148066525290002501788033 57111049893967501876341025)
    ·
      refine ⟨42833287420475626407255769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57111049893967501876341025 42833287420475626407255769)
      ·
        refine ⟨32124965565356719805441827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42833287420475626407255769 32124965565356719805441827)
        ·
          refine ⟨48187448348035079708162741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32124965565356719805441827 48187448348035079708162741)
          ·
            refine ⟨4517573282628288722640257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48187448348035079708162741 4517573282628288722640257)
            ·
              refine ⟨3388179961971216541980193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517573282628288722640257 3388179961971216541980193)
              ·
                refine ⟨2541134971478412406485145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388179961971216541980193 2541134971478412406485145)
                ·
                  refine ⟨1905851228608809304863859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541134971478412406485145 1905851228608809304863859)
                  ·
                    refine ⟨2858776842913213957295789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1905851228608809304863859 2858776842913213957295789)
                    ·
                      refine ⟨1072041316092455233985921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2858776842913213957295789 1072041316092455233985921)
                      ·
                        rfl

theorem cell23_2087793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_2087793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087793 prefixEnd_2087793 := by exact prefixLift 2087793
  have htrace : WordTrace (prefixWord ++ tailWord_2087793) baseStart_2087793 baseEnd_2087793 := by
    simpa [prefixWord, tailWord_2087793, baseEnd_2087793] using wordTrace_append hprefix tailTrace_2087793
  have hstable : (prefixWord ++ tailWord_2087793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087793).length < 2 ^ (prefixWord ++ tailWord_2087793).sum := by decide
  have hdescent : baseEnd_2087793 < baseStart_2087793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087849 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_2087849 : Nat := 118140960795 + 2087849 * 2 ^ 59
def prefixEnd_2087849 : Nat := 4983230072969 + 3 ^ 40 * 2087849 * 2
def baseEnd_2087849 : Nat := 1072070071009107014885663

theorem tailTrace_2087849 : CollatzResearch.WordTrace tailWord_2087849 prefixEnd_2087849 1072070071009107014885663 := by
  unfold tailWord_2087849
  simp only [CollatzResearch.WordTrace]
  refine ⟨76150109013087124065826601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50766739342058082710551067 76150109013087124065826601)
  ·
    refine ⟨57112581759815343049369951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76150109013087124065826601 57112581759815343049369951)
    ·
      refine ⟨85668872639723014574054927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57112581759815343049369951 85668872639723014574054927)
      ·
        refine ⟨128503308959584521861082391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85668872639723014574054927 128503308959584521861082391)
        ·
          refine ⟨192754963439376782791623587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128503308959584521861082391 192754963439376782791623587)
          ·
            refine ⟨289132445159065174187435381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192754963439376782791623587 289132445159065174187435381)
            ·
              refine ⟨27106166733662360080072067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289132445159065174187435381 27106166733662360080072067)
              ·
                refine ⟨40659250100493540120108101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27106166733662360080072067 40659250100493540120108101)
                ·
                  refine ⟨7623609393842538772520269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40659250100493540120108101 7623609393842538772520269)
                  ·
                    refine ⟨2858853522690952039695101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7623609393842538772520269 2858853522690952039695101)
                    ·
                      refine ⟨1072070071009107014885663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2858853522690952039695101 1072070071009107014885663)
                      ·
                        rfl

theorem cell23_2087849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_2087849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087849 prefixEnd_2087849 := by exact prefixLift 2087849
  have htrace : WordTrace (prefixWord ++ tailWord_2087849) baseStart_2087849 baseEnd_2087849 := by
    simpa [prefixWord, tailWord_2087849, baseEnd_2087849] using wordTrace_append hprefix tailTrace_2087849
  have hstable : (prefixWord ++ tailWord_2087849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087849).length < 2 ^ (prefixWord ++ tailWord_2087849).sum := by decide
  have hdescent : baseEnd_2087849 < baseStart_2087849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087889 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_2087889 : Nat := 118140960795 + 2087889 * 2 ^ 59
def prefixEnd_2087889 : Nat := 4983230072969 + 3 ^ 40 * 2087889 * 2
def baseEnd_2087889 : Nat := 1072090610235286858385479

theorem tailTrace_2087889 : CollatzResearch.WordTrace tailWord_2087889 prefixEnd_2087889 1072090610235286858385479 := by
  unfold tailWord_2087889
  simp only [CollatzResearch.WordTrace]
  refine ⟨76151567932942210897282721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50767711955294807264855147 76151567932942210897282721)
  ·
    refine ⟨57113675949706658172962041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76151567932942210897282721 57113675949706658172962041)
    ·
      refine ⟨42835256962279993629721531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57113675949706658172962041 42835256962279993629721531)
      ·
        refine ⟨64252885443419990444582297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42835256962279993629721531 64252885443419990444582297)
        ·
          refine ⟨48189664082564992833436723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64252885443419990444582297 48189664082564992833436723)
          ·
            refine ⟨72284496123847489250155085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48189664082564992833436723 72284496123847489250155085)
            ·
              refine ⟨27106686046442808468808157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72284496123847489250155085 27106686046442808468808157)
              ·
                refine ⟨10165007267416053175803059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27106686046442808468808157 10165007267416053175803059)
                ·
                  refine ⟨15247510901124079763704589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10165007267416053175803059 15247510901124079763704589)
                  ·
                    refine ⟨5717816587921529911389221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15247510901124079763704589 5717816587921529911389221)
                    ·
                      refine ⟨1072090610235286858385479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5717816587921529911389221 1072090610235286858385479)
                      ·
                        rfl

theorem cell23_2087889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_2087889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087889 prefixEnd_2087889 := by exact prefixLift 2087889
  have htrace : WordTrace (prefixWord ++ tailWord_2087889) baseStart_2087889 baseEnd_2087889 := by
    simpa [prefixWord, tailWord_2087889, baseEnd_2087889] using wordTrace_append hprefix tailTrace_2087889
  have hstable : (prefixWord ++ tailWord_2087889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087889).length < 2 ^ (prefixWord ++ tailWord_2087889).sum := by decide
  have hdescent : baseEnd_2087889 < baseStart_2087889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087890 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_2087890 : Nat := 118140960795 + 2087890 * 2 ^ 59
def prefixEnd_2087890 : Nat := 4983230072969 + 3 ^ 40 * 2087890 * 2
def baseEnd_2087890 : Nat := 119121235968437928274775

theorem tailTrace_2087890 : CollatzResearch.WordTrace tailWord_2087890 prefixEnd_2087890 119121235968437928274775 := by
  unfold tailWord_2087890
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037901101484647017017281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50767736270625725378712749 19037901101484647017017281)
  ·
    refine ⟨14278425826113485262762961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19037901101484647017017281 14278425826113485262762961)
    ·
      refine ⟨10708819369585113947072221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14278425826113485262762961 10708819369585113947072221)
      ·
        refine ⟨4015807263594417730152083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10708819369585113947072221 4015807263594417730152083)
        ·
          refine ⟨6023710895391626595228125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015807263594417730152083 6023710895391626595228125)
          ·
            refine ⟨2258891585771859973210547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6023710895391626595228125 2258891585771859973210547)
            ·
              refine ⟨3388337378657789959815821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258891585771859973210547 3388337378657789959815821)
              ·
                refine ⟨1270626516996671234930933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3388337378657789959815821 1270626516996671234930933)
                ·
                  refine ⟨119121235968437928274775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1270626516996671234930933 119121235968437928274775)
                  ·
                    rfl

theorem cell23_2087890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_2087890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087890 prefixEnd_2087890 := by exact prefixLift 2087890
  have htrace : WordTrace (prefixWord ++ tailWord_2087890) baseStart_2087890 baseEnd_2087890 := by
    simpa [prefixWord, tailWord_2087890, baseEnd_2087890] using wordTrace_append hprefix tailTrace_2087890
  have hstable : (prefixWord ++ tailWord_2087890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087890).length < 2 ^ (prefixWord ++ tailWord_2087890).sum := by decide
  have hdescent : baseEnd_2087890 < baseStart_2087890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087943 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2087943 : Nat := 118140960795 + 2087943 * 2 ^ 59
def prefixEnd_2087943 : Nat := 4983230072969 + 3 ^ 40 * 2087943 * 2
def baseEnd_2087943 : Nat := 1072118338190629647110231

theorem tailTrace_2087943 : CollatzResearch.WordTrace tailWord_2087943 prefixEnd_2087943 1072118338190629647110231 := by
  unfold tailWord_2087943
  simp only [CollatzResearch.WordTrace]
  refine ⟨76153537474746578119748483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50769024983164385413165655 76153537474746578119748483)
  ·
    refine ⟨114230306212119867179622725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76153537474746578119748483 114230306212119867179622725)
    ·
      refine ⟨21418182414772475096179261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114230306212119867179622725 21418182414772475096179261)
      ·
        refine ⟨8031818405539678161067223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21418182414772475096179261 8031818405539678161067223)
        ·
          refine ⟨12047727608309517241600835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031818405539678161067223 12047727608309517241600835)
          ·
            refine ⟨18071591412464275862401253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12047727608309517241600835 18071591412464275862401253)
            ·
              refine ⟨3388423389837051724200235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18071591412464275862401253 3388423389837051724200235)
              ·
                refine ⟨5082635084755577586300353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388423389837051724200235 5082635084755577586300353)
                ·
                  refine ⟨3811976313566683189725265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5082635084755577586300353 3811976313566683189725265)
                  ·
                    refine ⟨2858982235175012392293949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3811976313566683189725265 2858982235175012392293949)
                    ·
                      refine ⟨1072118338190629647110231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2858982235175012392293949 1072118338190629647110231)
                      ·
                        rfl

theorem cell23_2087943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2087943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087943 prefixEnd_2087943 := by exact prefixLift 2087943
  have htrace : WordTrace (prefixWord ++ tailWord_2087943) baseStart_2087943 baseEnd_2087943 := by
    simpa [prefixWord, tailWord_2087943, baseEnd_2087943] using wordTrace_append hprefix tailTrace_2087943
  have hstable : (prefixWord ++ tailWord_2087943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087943).length < 2 ^ (prefixWord ++ tailWord_2087943).sum := by decide
  have hdescent : baseEnd_2087943 < baseStart_2087943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087967 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 1, 4]
def baseStart_2087967 : Nat := 118140960795 + 2087967 * 2 ^ 59
def prefixEnd_2087967 : Nat := 4983230072969 + 3 ^ 40 * 2087967 * 2
def baseEnd_2087967 : Nat := 357376887242112517736707

theorem tailTrace_2087967 : CollatzResearch.WordTrace tailWord_2087967 prefixEnd_2087967 357376887242112517736707 := by
  unfold tailWord_2087967
  simp only [CollatzResearch.WordTrace]
  refine ⟨76154412826659630218622155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50769608551106420145748103 76154412826659630218622155)
  ·
    refine ⟨114231619239989445327933233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76154412826659630218622155 114231619239989445327933233)
    ·
      refine ⟨85673714429992083995949925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114231619239989445327933233 85673714429992083995949925)
      ·
        refine ⟨16063821455623515749240611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85673714429992083995949925 16063821455623515749240611)
        ·
          refine ⟨24095732183435273623860917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16063821455623515749240611 24095732183435273623860917)
          ·
            refine ⟨2258974892197056902236961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24095732183435273623860917 2258974892197056902236961)
            ·
              refine ⟨1694231169147792676677721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258974892197056902236961 1694231169147792676677721)
              ·
                refine ⟨1270673376860844507508291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694231169147792676677721 1270673376860844507508291)
                ·
                  refine ⟨1906010065291266761262437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270673376860844507508291 1906010065291266761262437)
                  ·
                    refine ⟨357376887242112517736707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906010065291266761262437 357376887242112517736707)
                    ·
                      rfl

theorem cell23_2087967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 4].length) (baseStart_2087967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087967 prefixEnd_2087967 := by exact prefixLift 2087967
  have htrace : WordTrace (prefixWord ++ tailWord_2087967) baseStart_2087967 baseEnd_2087967 := by
    simpa [prefixWord, tailWord_2087967, baseEnd_2087967] using wordTrace_append hprefix tailTrace_2087967
  have hstable : (prefixWord ++ tailWord_2087967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087967).length < 2 ^ (prefixWord ++ tailWord_2087967).sum := by decide
  have hdescent : baseEnd_2087967 < baseStart_2087967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087973 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_2087973 : Nat := 118140960795 + 2087973 * 2 ^ 59
def prefixEnd_2087973 : Nat := 4983230072969 + 3 ^ 40 * 2087973 * 2
def baseEnd_2087973 : Nat := 1072133742610264529735093

theorem tailTrace_2087973 : CollatzResearch.WordTrace tailWord_2087973 prefixEnd_2087973 1072133742610264529735093 := by
  unfold tailWord_2087973
  simp only [CollatzResearch.WordTrace]
  refine ⟨76154631664637893243340573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50769754443091928828893715 76154631664637893243340573)
  ·
    refine ⟨28557986874239209966252715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76154631664637893243340573 28557986874239209966252715)
    ·
      refine ⟨42836980311358814949379073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28557986874239209966252715 42836980311358814949379073)
      ·
        refine ⟨32127735233519111212034305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42836980311358814949379073 32127735233519111212034305)
        ·
          refine ⟨24095801425139333409025729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32127735233519111212034305 24095801425139333409025729)
          ·
            refine ⟨18071851068854500056769297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24095801425139333409025729 18071851068854500056769297)
            ·
              refine ⟨13553888301640875042576973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18071851068854500056769297 13553888301640875042576973)
              ·
                refine ⟨5082708113115328140966365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13553888301640875042576973 5082708113115328140966365)
                ·
                  refine ⟨1906015542418248052862387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5082708113115328140966365 1906015542418248052862387)
                  ·
                    refine ⟨2859023313627372079293581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1906015542418248052862387 2859023313627372079293581)
                    ·
                      refine ⟨1072133742610264529735093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859023313627372079293581 1072133742610264529735093)
                      ·
                        rfl

theorem cell23_2087973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_2087973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087973 prefixEnd_2087973 := by exact prefixLift 2087973
  have htrace : WordTrace (prefixWord ++ tailWord_2087973) baseStart_2087973 baseEnd_2087973 := by
    simpa [prefixWord, tailWord_2087973, baseEnd_2087973] using wordTrace_append hprefix tailTrace_2087973
  have hstable : (prefixWord ++ tailWord_2087973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087973).length < 2 ^ (prefixWord ++ tailWord_2087973).sum := by decide
  have hdescent : baseEnd_2087973 < baseStart_2087973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087990 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2087990 : Nat := 118140960795 + 2087990 * 2 ^ 59
def prefixEnd_2087990 : Nat := 4983230072969 + 3 ^ 40 * 2087990 * 2
def baseEnd_2087990 : Nat := 1072142471781390963222515

theorem tailTrace_2087990 : CollatzResearch.WordTrace tailWord_2087990 prefixEnd_2087990 1072142471781390963222515 := by
  unfold tailWord_2087990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759703231598519071669339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50770167803717536764472949 4759703231598519071669339)
  ·
    refine ⟨7139554847397778607504009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4759703231598519071669339 7139554847397778607504009)
    ·
      refine ⟨5354666135548333955628007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7139554847397778607504009 5354666135548333955628007)
      ·
        refine ⟨8031999203322500933442011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354666135548333955628007 8031999203322500933442011)
        ·
          refine ⟨12047998804983751400163017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031999203322500933442011 12047998804983751400163017)
          ·
            refine ⟨9035999103737813550122263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12047998804983751400163017 9035999103737813550122263)
            ·
              refine ⟨13553998655606720325183395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035999103737813550122263 13553998655606720325183395)
              ·
                refine ⟨20330997983410080487775093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13553998655606720325183395 20330997983410080487775093)
                ·
                  refine ⟨1906031060944695045728915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20330997983410080487775093 1906031060944695045728915)
                  ·
                    refine ⟨2859046591417042568593373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1906031060944695045728915 2859046591417042568593373)
                    ·
                      refine ⟨1072142471781390963222515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859046591417042568593373 1072142471781390963222515)
                      ·
                        rfl

theorem cell23_2087990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2087990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2087990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2087990 prefixEnd_2087990 := by exact prefixLift 2087990
  have htrace : WordTrace (prefixWord ++ tailWord_2087990) baseStart_2087990 baseEnd_2087990 := by
    simpa [prefixWord, tailWord_2087990, baseEnd_2087990] using wordTrace_append hprefix tailTrace_2087990
  have hstable : (prefixWord ++ tailWord_2087990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087990).length < 2 ^ (prefixWord ++ tailWord_2087990).sum := by decide
  have hdescent : baseEnd_2087990 < baseStart_2087990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088007 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_2088007 : Nat := 118140960795 + 2088007 * 2 ^ 59
def prefixEnd_2088007 : Nat := 4983230072969 + 3 ^ 40 * 2088007 * 2
def baseEnd_2088007 : Nat := 1072151200952517396709937

theorem tailTrace_2088007 : CollatzResearch.WordTrace tailWord_2088007 prefixEnd_2088007 1072151200952517396709937 := by
  unfold tailWord_2088007
  simp only [CollatzResearch.WordTrace]
  refine ⟨76155871746514717050078275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50770581164343144700052183 76155871746514717050078275)
  ·
    refine ⟨114233807619772075575117413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76155871746514717050078275 114233807619772075575117413)
    ·
      refine ⟨21418838928707264170334515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114233807619772075575117413 21418838928707264170334515)
      ·
        refine ⟨32128258393060896255501773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21418838928707264170334515 32128258393060896255501773)
        ·
          refine ⟨12048096897397836095813165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32128258393060896255501773 12048096897397836095813165)
          ·
            refine ⟨4518036336524188535929937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12048096897397836095813165 4518036336524188535929937)
            ·
              refine ⟨3388527252393141401947453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4518036336524188535929937 3388527252393141401947453)
              ·
                refine ⟨1270697719647428025730295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3388527252393141401947453 1270697719647428025730295)
                ·
                  refine ⟨1906046579471142038595443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270697719647428025730295 1906046579471142038595443)
                  ·
                    refine ⟨2859069869206713057893165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1906046579471142038595443 2859069869206713057893165)
                    ·
                      refine ⟨1072151200952517396709937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859069869206713057893165 1072151200952517396709937)
                      ·
                        rfl

theorem cell23_2088007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_2088007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088007 prefixEnd_2088007 := by exact prefixLift 2088007
  have htrace : WordTrace (prefixWord ++ tailWord_2088007) baseStart_2088007 baseEnd_2088007 := by
    simpa [prefixWord, tailWord_2088007, baseEnd_2088007] using wordTrace_append hprefix tailTrace_2088007
  have hstable : (prefixWord ++ tailWord_2088007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088007).length < 2 ^ (prefixWord ++ tailWord_2088007).sum := by decide
  have hdescent : baseEnd_2088007 < baseStart_2088007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088050 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2088050 : Nat := 118140960795 + 2088050 * 2 ^ 59
def prefixEnd_2088050 : Nat := 4983230072969 + 3 ^ 40 * 2088050 * 2
def baseEnd_2088050 : Nat := 1072173280620660728472239

theorem tailTrace_2088050 : CollatzResearch.WordTrace tailWord_2088050 prefixEnd_2088050 1072173280620660728472239 := by
  unfold tailWord_2088050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039360021339733848473401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50771626723572623595929069 19039360021339733848473401)
  ·
    refine ⟨14279520016004800386355051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19039360021339733848473401 14279520016004800386355051)
    ·
      refine ⟨21419280024007200579532577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279520016004800386355051 21419280024007200579532577)
      ·
        refine ⟨16064460018005400434649433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21419280024007200579532577 16064460018005400434649433)
        ·
          refine ⟨12048345013504050325987075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16064460018005400434649433 12048345013504050325987075)
          ·
            refine ⟨18072517520256075488980613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048345013504050325987075 18072517520256075488980613)
            ·
              refine ⟨3388597035048014154183865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18072517520256075488980613 3388597035048014154183865)
              ·
                refine ⟨2541447776286010615637899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388597035048014154183865 2541447776286010615637899)
                ·
                  refine ⟨3812171664429015923456849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541447776286010615637899 3812171664429015923456849)
                  ·
                    refine ⟨2859128748321761942592637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812171664429015923456849 2859128748321761942592637)
                    ·
                      refine ⟨1072173280620660728472239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859128748321761942592637 1072173280620660728472239)
                      ·
                        rfl

theorem cell23_2088050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2088050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088050 prefixEnd_2088050 := by exact prefixLift 2088050
  have htrace : WordTrace (prefixWord ++ tailWord_2088050) baseStart_2088050 baseEnd_2088050 := by
    simpa [prefixWord, tailWord_2088050, baseEnd_2088050] using wordTrace_append hprefix tailTrace_2088050
  have hstable : (prefixWord ++ tailWord_2088050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088050).length < 2 ^ (prefixWord ++ tailWord_2088050).sum := by decide
  have hdescent : baseEnd_2088050 < baseStart_2088050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088096 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_2088096 : Nat := 118140960795 + 2088096 * 2 ^ 59
def prefixEnd_2088096 : Nat := 4983230072969 + 3 ^ 40 * 2088096 * 2
def baseEnd_2088096 : Nat := 357398966910255849499009

theorem tailTrace_2088096 : CollatzResearch.WordTrace tailWord_2088096 prefixEnd_2088096 357398966910255849499009 := by
  unfold tailWord_2088096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38079558921596142625034071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50772745228794856833378761 38079558921596142625034071)
  ·
    refine ⟨57119338382394213937551107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38079558921596142625034071 57119338382394213937551107)
    ·
      refine ⟨85679007573591320906326661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57119338382394213937551107 85679007573591320906326661)
      ·
        refine ⟨16064813920048372669936249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85679007573591320906326661 16064813920048372669936249)
        ·
          refine ⟨12048610440036279502452187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16064813920048372669936249 12048610440036279502452187)
          ·
            refine ⟨18072915660054419253678281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048610440036279502452187 18072915660054419253678281)
            ·
              refine ⟨13554686745040814440258711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18072915660054419253678281 13554686745040814440258711)
              ·
                refine ⟨20332030117561221660388067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13554686745040814440258711 20332030117561221660388067)
                ·
                  refine ⟨30498045176341832490582101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20332030117561221660388067 30498045176341832490582101)
                  ·
                    refine ⟨357398966910255849499009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30498045176341832490582101 357398966910255849499009)
                    ·
                      rfl

theorem cell23_2088096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_2088096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088096 prefixEnd_2088096 := by exact prefixLift 2088096
  have htrace : WordTrace (prefixWord ++ tailWord_2088096) baseStart_2088096 baseEnd_2088096 := by
    simpa [prefixWord, tailWord_2088096, baseEnd_2088096] using wordTrace_append hprefix tailTrace_2088096
  have hstable : (prefixWord ++ tailWord_2088096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088096).length < 2 ^ (prefixWord ++ tailWord_2088096).sum := by decide
  have hdescent : baseEnd_2088096 < baseStart_2088096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088120 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 4, 2, 2]
def baseStart_2088120 : Nat := 118140960795 + 2088120 * 2 ^ 59
def prefixEnd_2088120 : Nat := 4983230072969 + 3 ^ 40 * 2088120 * 2
def baseEnd_2088120 : Nat := 1072209224266475454596917

theorem tailTrace_2088120 : CollatzResearch.WordTrace tailWord_2088120 prefixEnd_2088120 1072209224266475454596917 := by
  unfold tailWord_2088120
  simp only [CollatzResearch.WordTrace]
  refine ⟨38079996597552668674470907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50773328796736891565961209 38079996597552668674470907)
  ·
    refine ⟨57119994896329003011706361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38079996597552668674470907 57119994896329003011706361)
    ·
      refine ⟨42839996172246752258779771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57119994896329003011706361 42839996172246752258779771)
      ·
        refine ⟨64259994258370128388169657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42839996172246752258779771 64259994258370128388169657)
        ·
          refine ⟨48194995693777596291127243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64259994258370128388169657 48194995693777596291127243)
          ·
            refine ⟨72292493540666394436690865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48194995693777596291127243 72292493540666394436690865)
            ·
              refine ⟨54219370155499795827518149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72292493540666394436690865 54219370155499795827518149)
              ·
                refine ⟨10166131904156211717659653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54219370155499795827518149 10166131904156211717659653)
                ·
                  refine ⟨1906149732029289697061185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10166131904156211717659653 1906149732029289697061185)
                  ·
                    refine ⟨1429612299021967272795889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1906149732029289697061185 1429612299021967272795889)
                    ·
                      refine ⟨1072209224266475454596917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429612299021967272795889 1072209224266475454596917)
                      ·
                        rfl

theorem cell23_2088120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_2088120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088120 prefixEnd_2088120 := by exact prefixLift 2088120
  have htrace : WordTrace (prefixWord ++ tailWord_2088120) baseStart_2088120 baseEnd_2088120 := by
    simpa [prefixWord, tailWord_2088120, baseEnd_2088120] using wordTrace_append hprefix tailTrace_2088120
  have hstable : (prefixWord ++ tailWord_2088120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088120).length < 2 ^ (prefixWord ++ tailWord_2088120).sum := by decide
  have hdescent : baseEnd_2088120 < baseStart_2088120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088124 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_2088124 : Nat := 118140960795 + 2088124 * 2 ^ 59
def prefixEnd_2088124 : Nat := 4983230072969 + 3 ^ 40 * 2088124 * 2
def baseEnd_2088124 : Nat := 1072211278189093438946899

theorem tailTrace_2088124 : CollatzResearch.WordTrace tailWord_2088124 prefixEnd_2088124 1072211278189093438946899 := by
  unfold tailWord_2088124
  simp only [CollatzResearch.WordTrace]
  refine ⟨38080069543545423016043713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50773426058060564021391617 38080069543545423016043713)
  ·
    refine ⟨28560052157659067262032785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38080069543545423016043713 28560052157659067262032785)
    ·
      refine ⟨21420039118244300446524589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28560052157659067262032785 21420039118244300446524589)
      ·
        refine ⟨8032514669341612667446721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21420039118244300446524589 8032514669341612667446721)
        ·
          refine ⟨6024386002006209500585041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8032514669341612667446721 6024386002006209500585041)
          ·
            refine ⟨4518289501504657125438781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6024386002006209500585041 4518289501504657125438781)
            ·
              refine ⟨1694358563064246422039543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4518289501504657125438781 1694358563064246422039543)
              ·
                refine ⟨2541537844596369633059315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694358563064246422039543 2541537844596369633059315)
                ·
                  refine ⟨3812306766894554449588973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541537844596369633059315 3812306766894554449588973)
                  ·
                    refine ⟨1429615037585457918595865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812306766894554449588973 1429615037585457918595865)
                    ·
                      refine ⟨1072211278189093438946899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429615037585457918595865 1072211278189093438946899)
                      ·
                        rfl

theorem cell23_2088124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_2088124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088124 prefixEnd_2088124 := by exact prefixLift 2088124
  have htrace : WordTrace (prefixWord ++ tailWord_2088124) baseStart_2088124 baseEnd_2088124 := by
    simpa [prefixWord, tailWord_2088124, baseEnd_2088124] using wordTrace_append hprefix tailTrace_2088124
  have hstable : (prefixWord ++ tailWord_2088124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088124).length < 2 ^ (prefixWord ++ tailWord_2088124).sum := by decide
  have hdescent : baseEnd_2088124 < baseStart_2088124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088136 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2088136 : Nat := 118140960795 + 2088136 * 2 ^ 59
def prefixEnd_2088136 : Nat := 4983230072969 + 3 ^ 40 * 2088136 * 2
def baseEnd_2088136 : Nat := 1072217439956947391996843

theorem tailTrace_2088136 : CollatzResearch.WordTrace tailWord_2088136 prefixEnd_2088136 1072217439956947391996843 := by
  unfold tailWord_2088136
  simp only [CollatzResearch.WordTrace]
  refine ⟨38080288381523686040762131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50773717842031581387682841 38080288381523686040762131)
  ·
    refine ⟨57120432572285529061143197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38080288381523686040762131 57120432572285529061143197)
    ·
      refine ⟨21420162214607073397928699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57120432572285529061143197 21420162214607073397928699)
      ·
        refine ⟨32130243321910610096893049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21420162214607073397928699 32130243321910610096893049)
        ·
          refine ⟨24097682491432957572669787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32130243321910610096893049 24097682491432957572669787)
          ·
            refine ⟨36146523737149436359004681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24097682491432957572669787 36146523737149436359004681)
            ·
              refine ⟨27109892802862077269253511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36146523737149436359004681 27109892802862077269253511)
              ·
                refine ⟨40664839204293115903880267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27109892802862077269253511 40664839204293115903880267)
                ·
                  refine ⟨60997258806439673855820401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40664839204293115903880267 60997258806439673855820401)
                  ·
                    refine ⟨45747944104829755391865301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60997258806439673855820401 45747944104829755391865301)
                    ·
                      refine ⟨1072217439956947391996843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45747944104829755391865301 1072217439956947391996843)
                      ·
                        rfl

theorem cell23_2088136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2088136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088136 prefixEnd_2088136 := by exact prefixLift 2088136
  have htrace : WordTrace (prefixWord ++ tailWord_2088136) baseStart_2088136 baseEnd_2088136 := by
    simpa [prefixWord, tailWord_2088136, baseEnd_2088136] using wordTrace_append hprefix tailTrace_2088136
  have hstable : (prefixWord ++ tailWord_2088136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088136).length < 2 ^ (prefixWord ++ tailWord_2088136).sum := by decide
  have hdescent : baseEnd_2088136 < baseStart_2088136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088220 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_2088220 : Nat := 118140960795 + 2088220 * 2 ^ 59
def prefixEnd_2088220 : Nat := 4983230072969 + 3 ^ 40 * 2088220 * 2
def baseEnd_2088220 : Nat := 357420190777308354448819

theorem tailTrace_2088220 : CollatzResearch.WordTrace tailWord_2088220 prefixEnd_2088220 357420190777308354448819 := by
  unfold tailWord_2088220
  simp only [CollatzResearch.WordTrace]
  refine ⟨38081820247371527213791057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50775760329828702951721409 38081820247371527213791057)
  ·
    refine ⟨28561365185528645410343293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38081820247371527213791057 28561365185528645410343293)
    ·
      refine ⟨10710511944573242028878735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28561365185528645410343293 10710511944573242028878735)
      ·
        refine ⟨16065767916859863043318103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710511944573242028878735 16065767916859863043318103)
        ·
          refine ⟨24098651875289794564977155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16065767916859863043318103 24098651875289794564977155)
          ·
            refine ⟨36147977812934691847465733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24098651875289794564977155 36147977812934691847465733)
            ·
              refine ⟨6777745839925254721399825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36147977812934691847465733 6777745839925254721399825)
              ·
                refine ⟨5083309379943941041049869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6777745839925254721399825 5083309379943941041049869)
                ·
                  refine ⟨1906241017478977890393701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5083309379943941041049869 1906241017478977890393701)
                  ·
                    refine ⟨357420190777308354448819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906241017478977890393701 357420190777308354448819)
                    ·
                      rfl

theorem cell23_2088220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_2088220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088220 prefixEnd_2088220 := by exact prefixLift 2088220
  have htrace : WordTrace (prefixWord ++ tailWord_2088220) baseStart_2088220 baseEnd_2088220 := by
    simpa [prefixWord, tailWord_2088220, baseEnd_2088220] using wordTrace_append hprefix tailTrace_2088220
  have hstable : (prefixWord ++ tailWord_2088220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088220).length < 2 ^ (prefixWord ++ tailWord_2088220).sum := by decide
  have hdescent : baseEnd_2088220 < baseStart_2088220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088278 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2088278 : Nat := 118140960795 + 2088278 * 2 ^ 59
def prefixEnd_2088278 : Nat := 4983230072969 + 3 ^ 40 * 2088278 * 2
def baseEnd_2088278 : Nat := 1072290354209885836421191

theorem tailTrace_2088278 : CollatzResearch.WordTrace tailWord_2088278 prefixEnd_2088278 1072290354209885836421191 := by
  unfold tailWord_2088278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760359745533308145824593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50777170619021953555462325 4760359745533308145824593)
  ·
    refine ⟨3570269809149981109368445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4760359745533308145824593 3570269809149981109368445)
    ·
      refine ⟨1338851178431242916013167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3570269809149981109368445 1338851178431242916013167)
      ·
        refine ⟨2008276767646864374019751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338851178431242916013167 2008276767646864374019751)
        ·
          refine ⟨3012415151470296561029627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008276767646864374019751 3012415151470296561029627)
          ·
            refine ⟨4518622727205444841544441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012415151470296561029627 4518622727205444841544441)
            ·
              refine ⟨3388967045404083631158331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4518622727205444841544441 3388967045404083631158331)
              ·
                refine ⟨5083450568106125446737497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388967045404083631158331 5083450568106125446737497)
                ·
                  refine ⟨3812587926079594085053123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083450568106125446737497 3812587926079594085053123)
                  ·
                    refine ⟨5718881889119391127579685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3812587926079594085053123 5718881889119391127579685)
                    ·
                      refine ⟨1072290354209885836421191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5718881889119391127579685 1072290354209885836421191)
                      ·
                        rfl

theorem cell23_2088278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2088278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088278 prefixEnd_2088278 := by exact prefixLift 2088278
  have htrace : WordTrace (prefixWord ++ tailWord_2088278) baseStart_2088278 baseEnd_2088278 := by
    simpa [prefixWord, tailWord_2088278, baseEnd_2088278] using wordTrace_append hprefix tailTrace_2088278
  have hstable : (prefixWord ++ tailWord_2088278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088278).length < 2 ^ (prefixWord ++ tailWord_2088278).sum := by decide
  have hdescent : baseEnd_2088278 < baseStart_2088278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088313 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2088313 : Nat := 118140960795 + 2088313 * 2 ^ 59
def prefixEnd_2088313 : Nat := 4983230072969 + 3 ^ 40 * 2088313 * 2
def baseEnd_2088313 : Nat := 1072308326032793199483529

theorem tailTrace_2088313 : CollatzResearch.WordTrace tailWord_2088313 prefixEnd_2088313 1072308326032793199483529 := by
  unfold tailWord_2088313
  simp only [CollatzResearch.WordTrace]
  refine ⟨76167032483406131310717593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50778021655604087540478395 76167032483406131310717593)
  ·
    refine ⟨57125274362554598483038195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76167032483406131310717593 57125274362554598483038195)
    ·
      refine ⟨85687911543831897724557293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57125274362554598483038195 85687911543831897724557293)
      ·
        refine ⟨32132966828936961646708985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85687911543831897724557293 32132966828936961646708985)
        ·
          refine ⟨24099725121702721235031739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32132966828936961646708985 24099725121702721235031739)
          ·
            refine ⟨36149587682554081852547609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099725121702721235031739 36149587682554081852547609)
            ·
              refine ⟨27112190761915561389410707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36149587682554081852547609 27112190761915561389410707)
              ·
                refine ⟨40668286142873342084116061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27112190761915561389410707 40668286142873342084116061)
                ·
                  refine ⟨15250607303577503281543523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40668286142873342084116061 15250607303577503281543523)
                  ·
                    refine ⟨22875910955366254922315285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15250607303577503281543523 22875910955366254922315285)
                    ·
                      refine ⟨1072308326032793199483529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22875910955366254922315285 1072308326032793199483529)
                      ·
                        rfl

theorem cell23_2088313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2088313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088313 prefixEnd_2088313 := by exact prefixLift 2088313
  have htrace : WordTrace (prefixWord ++ tailWord_2088313) baseStart_2088313 baseEnd_2088313 := by
    simpa [prefixWord, tailWord_2088313, baseEnd_2088313] using wordTrace_append hprefix tailTrace_2088313
  have hstable : (prefixWord ++ tailWord_2088313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088313).length < 2 ^ (prefixWord ++ tailWord_2088313).sum := by decide
  have hdescent : baseEnd_2088313 < baseStart_2088313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088327 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 2, 4]
def baseStart_2088327 : Nat := 118140960795 + 2088327 * 2 ^ 59
def prefixEnd_2088327 : Nat := 4983230072969 + 3 ^ 40 * 2088327 * 2
def baseEnd_2088327 : Nat := 357438504920652048236155

theorem tailTrace_2088327 : CollatzResearch.WordTrace tailWord_2088327 prefixEnd_2088327 357438504920652048236155 := by
  unfold tailWord_2088327
  simp only [CollatzResearch.WordTrace]
  refine ⟨76167543105355411701727235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50778362070236941134484823 76167543105355411701727235)
  ·
    refine ⟨114251314658033117552590853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76167543105355411701727235 114251314658033117552590853)
    ·
      refine ⟨21422121498381209541110785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114251314658033117552590853 21422121498381209541110785)
      ·
        refine ⟨16066591123785907155833089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21422121498381209541110785 16066591123785907155833089)
        ·
          refine ⟨12049943342839430366874817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16066591123785907155833089 12049943342839430366874817)
          ·
            refine ⟨9037457507129572775156113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12049943342839430366874817 9037457507129572775156113)
            ·
              refine ⟨6778093130347179581367085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9037457507129572775156113 6778093130347179581367085)
              ·
                refine ⟨2541784923880192343012657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6778093130347179581367085 2541784923880192343012657)
                ·
                  refine ⟨1906338692910144257259493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541784923880192343012657 1906338692910144257259493)
                  ·
                    refine ⟨357438504920652048236155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906338692910144257259493 357438504920652048236155)
                    ·
                      rfl

theorem cell23_2088327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_2088327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088327 prefixEnd_2088327 := by exact prefixLift 2088327
  have htrace : WordTrace (prefixWord ++ tailWord_2088327) baseStart_2088327 baseEnd_2088327 := by
    simpa [prefixWord, tailWord_2088327, baseEnd_2088327] using wordTrace_append hprefix tailTrace_2088327
  have hstable : (prefixWord ++ tailWord_2088327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088327).length < 2 ^ (prefixWord ++ tailWord_2088327).sum := by decide
  have hdescent : baseEnd_2088327 < baseStart_2088327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
