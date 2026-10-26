import V185TrunkScan23Chunk1050

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6222624 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 6]
def baseStart_6222624 : Nat := 118140960795 + 6222624 * 2 ^ 59
def prefixEnd_6222624 : Nat := 4983230072969 + 3 ^ 40 * 6222624 * 2
def baseEnd_6222624 : Nat := 355021893800351909853631

theorem tailTrace_6222624 : CollatzResearch.WordTrace tailWord_6222624 prefixEnd_6222624 355021893800351909853631 := by
  unfold tailWord_6222624
  simp only [CollatzResearch.WordTrace]
  refine ⟨113478871304251731207645463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151305161739002308276860617 113478871304251731207645463)
  ·
    refine ⟨170218306956377596811468195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113478871304251731207645463 170218306956377596811468195)
    ·
      refine ⟨255327460434566395217202293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170218306956377596811468195 255327460434566395217202293)
      ·
        refine ⟨23936949415740599551612715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255327460434566395217202293 23936949415740599551612715)
        ·
          refine ⟨35905424123610899327419073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23936949415740599551612715 35905424123610899327419073)
          ·
            refine ⟨26929068092708174495564305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35905424123610899327419073 26929068092708174495564305)
            ·
              refine ⟨20196801069531130871673229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26929068092708174495564305 20196801069531130871673229)
              ·
                refine ⟨7573800401074174076877461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20196801069531130871673229 7573800401074174076877461)
                ·
                  refine ⟨355021893800351909853631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7573800401074174076877461 355021893800351909853631)
                  ·
                    rfl

theorem cell23_6222624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_6222624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222624 prefixEnd_6222624 := by exact prefixLift 6222624
  have htrace : WordTrace (prefixWord ++ tailWord_6222624) baseStart_6222624 baseEnd_6222624 := by
    simpa [prefixWord, tailWord_6222624, baseEnd_6222624] using wordTrace_append hprefix tailTrace_6222624
  have hstable : (prefixWord ++ tailWord_6222624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222624).length < 2 ^ (prefixWord ++ tailWord_6222624).sum := by decide
  have hdescent : baseEnd_6222624 < baseStart_6222624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222638 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6222638 : Nat := 118140960795 + 6222638 * 2 ^ 59
def prefixEnd_6222638 : Nat := 4983230072969 + 3 ^ 40 * 6222638 * 2
def baseEnd_6222638 : Nat := 3195204232932330133907615

theorem tailTrace_6222638 : CollatzResearch.WordTrace tailWord_6222638 prefixEnd_6222638 3195204232932330133907615 := by
  unfold tailWord_6222638
  simp only [CollatzResearch.WordTrace]
  refine ⟨28369781653806592850787571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151305502153635161870867045 28369781653806592850787571)
  ·
    refine ⟨42554672480709889276181357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28369781653806592850787571 42554672480709889276181357)
    ·
      refine ⟨15958002180266208478568009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42554672480709889276181357 15958002180266208478568009)
      ·
        refine ⟨11968501635199656358926007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15958002180266208478568009 11968501635199656358926007)
        ·
          refine ⟨17952752452799484538389011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11968501635199656358926007 17952752452799484538389011)
          ·
            refine ⟨26929128679199226807583517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17952752452799484538389011 26929128679199226807583517)
            ·
              refine ⟨10098423254699710052843819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26929128679199226807583517 10098423254699710052843819)
              ·
                refine ⟨15147634882049565079265729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098423254699710052843819 15147634882049565079265729)
                ·
                  refine ⟨11360726161537173809449297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15147634882049565079265729 11360726161537173809449297)
                  ·
                    refine ⟨8520544621152880357086973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11360726161537173809449297 8520544621152880357086973)
                    ·
                      refine ⟨3195204232932330133907615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8520544621152880357086973 3195204232932330133907615)
                      ·
                        rfl

theorem cell23_6222638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6222638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222638 prefixEnd_6222638 := by exact prefixLift 6222638
  have htrace : WordTrace (prefixWord ++ tailWord_6222638) baseStart_6222638 baseEnd_6222638 := by
    simpa [prefixWord, tailWord_6222638, baseEnd_6222638] using wordTrace_append hprefix tailTrace_6222638
  have hstable : (prefixWord ++ tailWord_6222638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222638).length < 2 ^ (prefixWord ++ tailWord_6222638).sum := by decide
  have hdescent : baseEnd_6222638 < baseStart_6222638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222668 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6222668 : Nat := 118140960795 + 6222668 * 2 ^ 59
def prefixEnd_6222668 : Nat := 4983230072969 + 3 ^ 40 * 6222668 * 2
def baseEnd_6222668 : Nat := 3195219637351965016532477

theorem tailTrace_6222668 : CollatzResearch.WordTrace tailWord_6222668 prefixEnd_6222668 3195219637351965016532477 := by
  unfold tailWord_6222668
  simp only [CollatzResearch.WordTrace]
  refine ⟨113479673710172028964946329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151306231613562705286595105 113479673710172028964946329)
  ·
    refine ⟨85109755282629021723709747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113479673710172028964946329 85109755282629021723709747)
    ·
      refine ⟨127664632923943532585564621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85109755282629021723709747 127664632923943532585564621)
      ·
        refine ⟨47874237346478824719586733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127664632923943532585564621 47874237346478824719586733)
        ·
          refine ⟨17952839004929559269845025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47874237346478824719586733 17952839004929559269845025)
          ·
            refine ⟨13464629253697169452383769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17952839004929559269845025 13464629253697169452383769)
            ·
              refine ⟨10098471940272877089287827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13464629253697169452383769 10098471940272877089287827)
              ·
                refine ⟨15147707910409315633931741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098471940272877089287827 15147707910409315633931741)
                ·
                  refine ⟨5680390466403493362724403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15147707910409315633931741 5680390466403493362724403)
                  ·
                    refine ⟨8520585699605240044086605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5680390466403493362724403 8520585699605240044086605)
                    ·
                      refine ⟨3195219637351965016532477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8520585699605240044086605 3195219637351965016532477)
                      ·
                        rfl

theorem cell23_6222668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6222668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222668 prefixEnd_6222668 := by exact prefixLift 6222668
  have htrace : WordTrace (prefixWord ++ tailWord_6222668) baseStart_6222668 baseEnd_6222668 := by
    simpa [prefixWord, tailWord_6222668, baseEnd_6222668] using wordTrace_append hprefix tailTrace_6222668
  have hstable : (prefixWord ++ tailWord_6222668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222668).length < 2 ^ (prefixWord ++ tailWord_6222668).sum := by decide
  have hdescent : baseEnd_6222668 < baseStart_6222668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222691 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 4]
def baseStart_6222691 : Nat := 118140960795 + 6222691 * 2 ^ 59
def prefixEnd_6222691 : Nat := 4983230072969 + 3 ^ 40 * 6222691 * 2
def baseEnd_6222691 : Nat := 3195231447407018426544871

theorem tailTrace_6222691 : CollatzResearch.WordTrace tailWord_6222691 prefixEnd_6222691 3195231447407018426544871 := by
  unfold tailWord_6222691
  simp only [CollatzResearch.WordTrace]
  refine ⟨226960186299260732857979927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151306790866173821905319951 226960186299260732857979927)
  ·
    refine ⟨340440279448891099286969891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226960186299260732857979927 340440279448891099286969891)
    ·
      refine ⟨510660419173336648930454837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340440279448891099286969891 510660419173336648930454837)
      ·
        refine ⟨47874414297500310837230141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 510660419173336648930454837 47874414297500310837230141)
        ·
          refine ⟨17952905361562616563961303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47874414297500310837230141 17952905361562616563961303)
          ·
            refine ⟨26929358042343924845941955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17952905361562616563961303 26929358042343924845941955)
            ·
              refine ⟨40394037063515887268912933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26929358042343924845941955 40394037063515887268912933)
              ·
                refine ⟨7573881949409228862921175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40394037063515887268912933 7573881949409228862921175)
                ·
                  refine ⟨11360822924113843294381763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7573881949409228862921175 11360822924113843294381763)
                  ·
                    refine ⟨17041234386170764941572645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11360822924113843294381763 17041234386170764941572645)
                    ·
                      refine ⟨3195231447407018426544871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17041234386170764941572645 3195231447407018426544871)
                      ·
                        rfl

theorem cell23_6222691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_6222691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222691 prefixEnd_6222691 := by exact prefixLift 6222691
  have htrace : WordTrace (prefixWord ++ tailWord_6222691) baseStart_6222691 baseEnd_6222691 := by
    simpa [prefixWord, tailWord_6222691, baseEnd_6222691] using wordTrace_append hprefix tailTrace_6222691
  have hstable : (prefixWord ++ tailWord_6222691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222691).length < 2 ^ (prefixWord ++ tailWord_6222691).sum := by decide
  have hdescent : baseEnd_6222691 < baseStart_6222691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222704 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_6222704 : Nat := 118140960795 + 6222704 * 2 ^ 59
def prefixEnd_6222704 : Nat := 4983230072969 + 3 ^ 40 * 6222704 * 2
def baseEnd_6222704 : Nat := 3195238122655526875682311

theorem tailTrace_6222704 : CollatzResearch.WordTrace tailWord_6222704 prefixEnd_6222704 3195238122655526875682311 := by
  unfold tailWord_6222704
  simp only [CollatzResearch.WordTrace]
  refine ⟨113480330224106818039101583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151307106965475757385468777 113480330224106818039101583)
  ·
    refine ⟨170220495336160227058652375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113480330224106818039101583 170220495336160227058652375)
    ·
      refine ⟨255330743004240340587978563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170220495336160227058652375 255330743004240340587978563)
      ·
        refine ⟨382996114506360510881967845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255330743004240340587978563 382996114506360510881967845)
        ·
          refine ⟨71811771469942595790368971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382996114506360510881967845 71811771469942595790368971)
          ·
            refine ⟨107717657204913893685553457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71811771469942595790368971 107717657204913893685553457)
            ·
              refine ⟨80788242903685420264165093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107717657204913893685553457 80788242903685420264165093)
              ·
                refine ⟨15147795544441016299530955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80788242903685420264165093 15147795544441016299530955)
                ·
                  refine ⟨22721693316661524449296433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15147795544441016299530955 22721693316661524449296433)
                  ·
                    refine ⟨17041269987496143336972325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22721693316661524449296433 17041269987496143336972325)
                    ·
                      refine ⟨3195238122655526875682311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17041269987496143336972325 3195238122655526875682311)
                      ·
                        rfl

theorem cell23_6222704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_6222704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222704 prefixEnd_6222704 := by exact prefixLift 6222704
  have htrace : WordTrace (prefixWord ++ tailWord_6222704) baseStart_6222704 baseEnd_6222704 := by
    simpa [prefixWord, tailWord_6222704, baseEnd_6222704] using wordTrace_append hprefix tailTrace_6222704
  have hstable : (prefixWord ++ tailWord_6222704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222704).length < 2 ^ (prefixWord ++ tailWord_6222704).sum := by decide
  have hdescent : baseEnd_6222704 < baseStart_6222704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222725 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 3, 2, 2]
def baseStart_6222725 : Nat := 118140960795 + 6222725 * 2 ^ 59
def prefixEnd_6222725 : Nat := 4983230072969 + 3 ^ 40 * 6222725 * 2
def baseEnd_6222725 : Nat := 3195248905749271293519715

theorem tailTrace_6222725 : CollatzResearch.WordTrace tailWord_6222725 prefixEnd_6222725 3195248905749271293519715 := by
  unfold tailWord_6222725
  simp only [CollatzResearch.WordTrace]
  refine ⟨226961426381137556664717629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151307617587425037776478419 226961426381137556664717629)
  ·
    refine ⟨85110534892926583749269111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226961426381137556664717629 85110534892926583749269111)
    ·
      refine ⟨127665802339389875623903667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85110534892926583749269111 127665802339389875623903667)
      ·
        refine ⟨191498703509084813435855501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127665802339389875623903667 191498703509084813435855501)
        ·
          refine ⟨71812013815906805038445813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191498703509084813435855501 71812013815906805038445813)
          ·
            refine ⟨6732376295241262972354295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71812013815906805038445813 6732376295241262972354295)
            ·
              refine ⟨10098564442861894458531443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6732376295241262972354295 10098564442861894458531443)
              ·
                refine ⟨15147846664292841687797165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098564442861894458531443 15147846664292841687797165)
                ·
                  refine ⟨5680442499109815632923937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15147846664292841687797165 5680442499109815632923937)
                  ·
                    refine ⟨4260331874332361724692953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5680442499109815632923937 4260331874332361724692953)
                    ·
                      refine ⟨3195248905749271293519715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260331874332361724692953 3195248905749271293519715)
                      ·
                        rfl

theorem cell23_6222725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_6222725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222725 prefixEnd_6222725 := by exact prefixLift 6222725
  have htrace : WordTrace (prefixWord ++ tailWord_6222725) baseStart_6222725 baseEnd_6222725 := by
    simpa [prefixWord, tailWord_6222725, baseEnd_6222725] using wordTrace_append hprefix tailTrace_6222725
  have hstable : (prefixWord ++ tailWord_6222725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222725).length < 2 ^ (prefixWord ++ tailWord_6222725).sum := by decide
  have hdescent : baseEnd_6222725 < baseStart_6222725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222742 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6222742 : Nat := 118140960795 + 6222742 * 2 ^ 59
def prefixEnd_6222742 : Nat := 4983230072969 + 3 ^ 40 * 6222742 * 2
def baseEnd_6222742 : Nat := 3195257634920397727007137

theorem tailTrace_6222742 : CollatzResearch.WordTrace tailWord_6222742 prefixEnd_6222742 3195257634920397727007137 := by
  unfold tailWord_6222742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185127901379748035505405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151308030948050645712057653 14185127901379748035505405)
  ·
    refine ⟨5319422963017405513314527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14185127901379748035505405 5319422963017405513314527)
    ·
      refine ⟨7979134444526108269971791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319422963017405513314527 7979134444526108269971791)
      ·
        refine ⟨11968701666789162404957687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979134444526108269971791 11968701666789162404957687)
        ·
          refine ⟨17953052500183743607436531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11968701666789162404957687 17953052500183743607436531)
          ·
            refine ⟨26929578750275615411154797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17953052500183743607436531 26929578750275615411154797)
            ·
              refine ⟨10098592031353355779183049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26929578750275615411154797 10098592031353355779183049)
              ·
                refine ⟨7573944023515016834387287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10098592031353355779183049 7573944023515016834387287)
                ·
                  refine ⟨11360916035272525251580931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7573944023515016834387287 11360916035272525251580931)
                  ·
                    refine ⟨17041374052908787877371397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11360916035272525251580931 17041374052908787877371397)
                    ·
                      refine ⟨3195257634920397727007137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17041374052908787877371397 3195257634920397727007137)
                      ·
                        rfl

theorem cell23_6222742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6222742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222742 prefixEnd_6222742 := by exact prefixLift 6222742
  have htrace : WordTrace (prefixWord ++ tailWord_6222742) baseStart_6222742 baseEnd_6222742 := by
    simpa [prefixWord, tailWord_6222742, baseEnd_6222742] using wordTrace_append hprefix tailTrace_6222742
  have hstable : (prefixWord ++ tailWord_6222742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222742).length < 2 ^ (prefixWord ++ tailWord_6222742).sum := by decide
  have hdescent : baseEnd_6222742 < baseStart_6222742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222798 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_6222798 : Nat := 118140960795 + 6222798 * 2 ^ 59
def prefixEnd_6222798 : Nat := 4983230072969 + 3 ^ 40 * 6222798 * 2
def baseEnd_6222798 : Nat := 3195286389837049507906879

theorem tailTrace_6222798 : CollatzResearch.WordTrace tailWord_6222798 prefixEnd_6222798 3195286389837049507906879 := by
  unfold tailWord_6222798
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370511113734136266515631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151309392606582060088083365 28370511113734136266515631)
  ·
    refine ⟨42555766670601204399773447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28370511113734136266515631 42555766670601204399773447)
    ·
      refine ⟨63833650005901806599660171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42555766670601204399773447 63833650005901806599660171)
      ·
        refine ⟨95750475008852709899490257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63833650005901806599660171 95750475008852709899490257)
        ·
          refine ⟨71812856256639532424617693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95750475008852709899490257 71812856256639532424617693)
          ·
            refine ⟨26929821096239824659231635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71812856256639532424617693 26929821096239824659231635)
            ·
              refine ⟨40394731644359736988847453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26929821096239824659231635 40394731644359736988847453)
              ·
                refine ⟨15148024366634901370817795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40394731644359736988847453 15148024366634901370817795)
                ·
                  refine ⟨22722036549952352056226693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15148024366634901370817795 22722036549952352056226693)
                  ·
                    refine ⟨4260381853116066010542505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22722036549952352056226693 4260381853116066010542505)
                    ·
                      refine ⟨3195286389837049507906879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260381853116066010542505 3195286389837049507906879)
                      ·
                        rfl

theorem cell23_6222798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_6222798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222798 prefixEnd_6222798 := by exact prefixLift 6222798
  have htrace : WordTrace (prefixWord ++ tailWord_6222798) baseStart_6222798 baseEnd_6222798 := by
    simpa [prefixWord, tailWord_6222798, baseEnd_6222798] using wordTrace_append hprefix tailTrace_6222798
  have hstable : (prefixWord ++ tailWord_6222798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222798).length < 2 ^ (prefixWord ++ tailWord_6222798).sum := by decide
  have hdescent : baseEnd_6222798 < baseStart_6222798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222831 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_6222831 : Nat := 118140960795 + 6222831 * 2 ^ 59
def prefixEnd_6222831 : Nat := 4983230072969 + 3 ^ 40 * 6222831 * 2
def baseEnd_6222831 : Nat := 3195303334698647878794227

theorem tailTrace_6222831 : CollatzResearch.WordTrace tailWord_6222831 prefixEnd_6222831 3195303334698647878794227 := by
  unfold tailWord_6222831
  simp only [CollatzResearch.WordTrace]
  refine ⟨226965292518753536768076347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151310195012502357845384231 226965292518753536768076347)
  ·
    refine ⟨340447938778130305152114521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226965292518753536768076347 340447938778130305152114521)
    ·
      refine ⟨255335954083597728864085891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340447938778130305152114521 255335954083597728864085891)
      ·
        refine ⟨383003931125396593296128837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255335954083597728864085891 383003931125396593296128837)
        ·
          refine ⟨71813237086011861243024157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 383003931125396593296128837 71813237086011861243024157)
          ·
            refine ⟨26929963907254447966134059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71813237086011861243024157 26929963907254447966134059)
            ·
              refine ⟨40394945860881671949201089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26929963907254447966134059 40394945860881671949201089)
              ·
                refine ⟨30296209395661253961900817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40394945860881671949201089 30296209395661253961900817)
                ·
                  refine ⟨22722157046745940471425613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30296209395661253961900817 22722157046745940471425613)
                  ·
                    refine ⟨8520808892529727676784605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22722157046745940471425613 8520808892529727676784605)
                    ·
                      refine ⟨3195303334698647878794227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8520808892529727676784605 3195303334698647878794227)
                      ·
                        rfl

theorem cell23_6222831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_6222831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222831 prefixEnd_6222831 := by exact prefixLift 6222831
  have htrace : WordTrace (prefixWord ++ tailWord_6222831) baseStart_6222831 baseEnd_6222831 := by
    simpa [prefixWord, tailWord_6222831, baseEnd_6222831] using wordTrace_append hprefix tailTrace_6222831
  have hstable : (prefixWord ++ tailWord_6222831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222831).length < 2 ^ (prefixWord ++ tailWord_6222831).sum := by decide
  have hdescent : baseEnd_6222831 < baseStart_6222831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222838 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_6222838 : Nat := 118140960795 + 6222838 * 2 ^ 59
def prefixEnd_6222838 : Nat := 4983230072969 + 3 ^ 40 * 6222838 * 2
def baseEnd_6222838 : Nat := 355034103229247705711855

theorem tailTrace_6222838 : CollatzResearch.WordTrace tailWord_6222838 prefixEnd_6222838 355034103229247705711855 := by
  unfold tailWord_6222838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185346739358011060223823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151310365219818784642387445 14185346739358011060223823)
  ·
    refine ⟨21278020109037016590335735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14185346739358011060223823 21278020109037016590335735)
    ·
      refine ⟨31917030163555524885503603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21278020109037016590335735 31917030163555524885503603)
      ·
        refine ⟨47875545245333287328255405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31917030163555524885503603 47875545245333287328255405)
        ·
          refine ⟨17953329466999982748095777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47875545245333287328255405 17953329466999982748095777)
          ·
            refine ⟨13464997100249987061071833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17953329466999982748095777 13464997100249987061071833)
            ·
              refine ⟨10098747825187490295803875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13464997100249987061071833 10098747825187490295803875)
              ·
                refine ⟨15148121737781235443705813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098747825187490295803875 15148121737781235443705813)
                ·
                  refine ⟨355034103229247705711855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15148121737781235443705813 355034103229247705711855)
                  ·
                    rfl

theorem cell23_6222838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_6222838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222838 prefixEnd_6222838 := by exact prefixLift 6222838
  have htrace : WordTrace (prefixWord ++ tailWord_6222838) baseStart_6222838 baseEnd_6222838 := by
    simpa [prefixWord, tailWord_6222838, baseEnd_6222838] using wordTrace_append hprefix tailTrace_6222838
  have hstable : (prefixWord ++ tailWord_6222838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222838).length < 2 ^ (prefixWord ++ tailWord_6222838).sum := by decide
  have hdescent : baseEnd_6222838 < baseStart_6222838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222925 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_6222925 : Nat := 118140960795 + 6222925 * 2 ^ 59
def prefixEnd_6222925 : Nat := 4983230072969 + 3 ^ 40 * 6222925 * 2
def baseEnd_6222925 : Nat := 3195351601880170511018795

theorem tailTrace_6222925 : CollatzResearch.WordTrace tailWord_6222925 prefixEnd_6222925 3195351601880170511018795 := by
  unfold tailWord_6222925
  simp only [CollatzResearch.WordTrace]
  refine ⟨226968720980412990821998229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151312480653608660547998819 226968720980412990821998229)
  ·
    refine ⟨10639158795956858944781167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 226968720980412990821998229 10639158795956858944781167)
    ·
      refine ⟨15958738193935288417171751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10639158795956858944781167 15958738193935288417171751)
      ·
        refine ⟨23938107290902932625757627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15958738193935288417171751 23938107290902932625757627)
        ·
          refine ⟨35907160936354398938636441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23938107290902932625757627 35907160936354398938636441)
          ·
            refine ⟨26930370702265799203977331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35907160936354398938636441 26930370702265799203977331)
            ·
              refine ⟨40395556053398698805965997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26930370702265799203977331 40395556053398698805965997)
              ·
                refine ⟨15148333520024512052237249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40395556053398698805965997 15148333520024512052237249)
                ·
                  refine ⟨11361250140018384039177937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15148333520024512052237249 11361250140018384039177937)
                  ·
                    refine ⟨8520937605013788029383453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11361250140018384039177937 8520937605013788029383453)
                    ·
                      refine ⟨3195351601880170511018795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8520937605013788029383453 3195351601880170511018795)
                      ·
                        rfl

theorem cell23_6222925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_6222925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222925 prefixEnd_6222925 := by exact prefixLift 6222925
  have htrace : WordTrace (prefixWord ++ tailWord_6222925) baseStart_6222925 baseEnd_6222925 := by
    simpa [prefixWord, tailWord_6222925, baseEnd_6222925] using wordTrace_append hprefix tailTrace_6222925
  have hstable : (prefixWord ++ tailWord_6222925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222925).length < 2 ^ (prefixWord ++ tailWord_6222925).sum := by decide
  have hdescent : baseEnd_6222925 < baseStart_6222925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222938 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_6222938 : Nat := 118140960795 + 6222938 * 2 ^ 59
def prefixEnd_6222938 : Nat := 4983230072969 + 3 ^ 40 * 6222938 * 2
def baseEnd_6222938 : Nat := 3195358277128678960156235

theorem tailTrace_6222938 : CollatzResearch.WordTrace tailWord_6222938 prefixEnd_6222938 3195358277128678960156235 := by
  unfold tailWord_6222938
  simp only [CollatzResearch.WordTrace]
  refine ⟨56742298782341473510555367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151312796752910596028147645 56742298782341473510555367)
  ·
    refine ⟨85113448173512210265833051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56742298782341473510555367 85113448173512210265833051)
    ·
      refine ⟨127670172260268315398749577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85113448173512210265833051 127670172260268315398749577)
      ·
        refine ⟨95752629195201236549062183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127670172260268315398749577 95752629195201236549062183)
        ·
          refine ⟨143628943792801854823593275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95752629195201236549062183 143628943792801854823593275)
          ·
            refine ⟨215443415689202782235389913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143628943792801854823593275 215443415689202782235389913)
            ·
              refine ⟨161582561766902086676542435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215443415689202782235389913 161582561766902086676542435)
              ·
                refine ⟨242373842650353130014813653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161582561766902086676542435 242373842650353130014813653)
                ·
                  refine ⟨5680636937117651484722195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 242373842650353130014813653 5680636937117651484722195)
                  ·
                    refine ⟨8520955405676477227083293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5680636937117651484722195 8520955405676477227083293)
                    ·
                      refine ⟨3195358277128678960156235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8520955405676477227083293 3195358277128678960156235)
                      ·
                        rfl

theorem cell23_6222938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_6222938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222938 prefixEnd_6222938 := by exact prefixLift 6222938
  have htrace : WordTrace (prefixWord ++ tailWord_6222938) baseStart_6222938 baseEnd_6222938 := by
    simpa [prefixWord, tailWord_6222938, baseEnd_6222938] using wordTrace_append hprefix tailTrace_6222938
  have hstable : (prefixWord ++ tailWord_6222938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222938).length < 2 ^ (prefixWord ++ tailWord_6222938).sum := by decide
  have hdescent : baseEnd_6222938 < baseStart_6222938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222948 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_6222948 : Nat := 118140960795 + 6222948 * 2 ^ 59
def prefixEnd_6222948 : Nat := 4983230072969 + 3 ^ 40 * 6222948 * 2
def baseEnd_6222948 : Nat := 3195363411935223921031189

theorem tailTrace_6222948 : CollatzResearch.WordTrace tailWord_6222948 prefixEnd_6222948 3195363411935223921031189 := by
  unfold tailWord_6222948
  simp only [CollatzResearch.WordTrace]
  refine ⟨113484779929664832875042749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151313039906219777166723665 113484779929664832875042749)
  ·
    refine ⟨42556792473624312328141031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113484779929664832875042749 42556792473624312328141031)
    ·
      refine ⟨63835188710436468492211547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42556792473624312328141031 63835188710436468492211547)
      ·
        refine ⟨95752783065654702738317321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63835188710436468492211547 95752783065654702738317321)
        ·
          refine ⟨71814587299241027053737991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95752783065654702738317321 71814587299241027053737991)
          ·
            refine ⟨107721880948861540580606987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71814587299241027053737991 107721880948861540580606987)
            ·
              refine ⟨161582821423292310870910481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107721880948861540580606987 161582821423292310870910481)
              ·
                refine ⟨121187116067469233153182861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161582821423292310870910481 121187116067469233153182861)
                ·
                  refine ⟨45445168525300962432443573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121187116067469233153182861 45445168525300962432443573)
                  ·
                    refine ⟨4260484549246965228041585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45445168525300962432443573 4260484549246965228041585)
                    ·
                      refine ⟨3195363411935223921031189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260484549246965228041585 3195363411935223921031189)
                      ·
                        rfl

theorem cell23_6222948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_6222948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222948 prefixEnd_6222948 := by exact prefixLift 6222948
  have htrace : WordTrace (prefixWord ++ tailWord_6222948) baseStart_6222948 baseEnd_6222948 := by
    simpa [prefixWord, tailWord_6222948, baseEnd_6222948] using wordTrace_append hprefix tailTrace_6222948
  have hstable : (prefixWord ++ tailWord_6222948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222948).length < 2 ^ (prefixWord ++ tailWord_6222948).sum := by decide
  have hdescent : baseEnd_6222948 < baseStart_6222948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222958 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6222958 : Nat := 118140960795 + 6222958 * 2 ^ 59
def prefixEnd_6222958 : Nat := 4983230072969 + 3 ^ 40 * 6222958 * 2
def baseEnd_6222958 : Nat := 1065122848913922960635381

theorem tailTrace_6222958 : CollatzResearch.WordTrace tailWord_6222958 prefixEnd_6222958 1065122848913922960635381 := by
  unfold tailWord_6222958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28371240573661679682243691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151313283059528958305299685 28371240573661679682243691)
  ·
    refine ⟨42556860860492519523365537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28371240573661679682243691 42556860860492519523365537)
    ·
      refine ⟨31917645645369389642524153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42556860860492519523365537 31917645645369389642524153)
      ·
        refine ⟨23938234234027042231893115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31917645645369389642524153 23938234234027042231893115)
        ·
          refine ⟨35907351351040563347839673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23938234234027042231893115 35907351351040563347839673)
          ·
            refine ⟨26930513513280422510879755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35907351351040563347839673 26930513513280422510879755)
            ·
              refine ⟨40395770269920633766319633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26930513513280422510879755 40395770269920633766319633)
              ·
                refine ⟨30296827702440475324739725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40395770269920633766319633 30296827702440475324739725)
                ·
                  refine ⟨11361310388415178246777397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30296827702440475324739725 11361310388415178246777397)
                  ·
                    refine ⟨1065122848913922960635381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11361310388415178246777397 1065122848913922960635381)
                    ·
                      rfl

theorem cell23_6222958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6222958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222958 prefixEnd_6222958 := by exact prefixLift 6222958
  have htrace : WordTrace (prefixWord ++ tailWord_6222958) baseStart_6222958 baseEnd_6222958 := by
    simpa [prefixWord, tailWord_6222958, baseEnd_6222958] using wordTrace_append hprefix tailTrace_6222958
  have hstable : (prefixWord ++ tailWord_6222958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222958).length < 2 ^ (prefixWord ++ tailWord_6222958).sum := by decide
  have hdescent : baseEnd_6222958 < baseStart_6222958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222991 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_6222991 : Nat := 118140960795 + 6222991 * 2 ^ 59
def prefixEnd_6222991 : Nat := 4983230072969 + 3 ^ 40 * 6222991 * 2
def baseEnd_6222991 : Nat := 3195385491603367252793491

theorem tailTrace_6222991 : CollatzResearch.WordTrace tailWord_6222991 prefixEnd_6222991 3195385491603367252793491 := by
  unfold tailWord_6222991
  simp only [CollatzResearch.WordTrace]
  refine ⟨226971128198173884093900827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151314085465449256062600551 226971128198173884093900827)
  ·
    refine ⟨340456692297260826140851241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226971128198173884093900827 340456692297260826140851241)
    ·
      refine ⟨255342519222945619605638431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340456692297260826140851241 255342519222945619605638431)
      ·
        refine ⟨383013778834418429408457647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255342519222945619605638431 383013778834418429408457647)
        ·
          refine ⟨574520668251627644112686471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383013778834418429408457647 574520668251627644112686471)
          ·
            refine ⟨861781002377441466169029707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574520668251627644112686471 861781002377441466169029707)
            ·
              refine ⟨1292671503566162199253544561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861781002377441466169029707 1292671503566162199253544561)
              ·
                refine ⟨969503627674621649440158421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292671503566162199253544561 969503627674621649440158421)
                ·
                  refine ⟨22722741273623944908753713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 969503627674621649440158421 22722741273623944908753713)
                  ·
                    refine ⟨17042055955217958681565285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22722741273623944908753713 17042055955217958681565285)
                    ·
                      refine ⟨3195385491603367252793491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17042055955217958681565285 3195385491603367252793491)
                      ·
                        rfl

theorem cell23_6222991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_6222991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222991 prefixEnd_6222991 := by exact prefixLift 6222991
  have htrace : WordTrace (prefixWord ++ tailWord_6222991) baseStart_6222991 baseEnd_6222991 := by
    simpa [prefixWord, tailWord_6222991, baseEnd_6222991] using wordTrace_append hprefix tailTrace_6222991
  have hstable : (prefixWord ++ tailWord_6222991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222991).length < 2 ^ (prefixWord ++ tailWord_6222991).sum := by decide
  have hdescent : baseEnd_6222991 < baseStart_6222991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222995 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 1, 1, 4]
def baseStart_6222995 : Nat := 118140960795 + 6222995 * 2 ^ 59
def prefixEnd_6222995 : Nat := 4983230072969 + 3 ^ 40 * 6222995 * 2
def baseEnd_6222995 : Nat := 3195387545525985237143473

theorem tailTrace_6222995 : CollatzResearch.WordTrace tailWord_6222995 prefixEnd_6222995 3195387545525985237143473 := by
  unfold tailWord_6222995
  simp only [CollatzResearch.WordTrace]
  refine ⟨226971274090159392777046439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151314182726772928518030959 226971274090159392777046439)
  ·
    refine ⟨340456911135239089165569659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226971274090159392777046439 340456911135239089165569659)
    ·
      refine ⟨510685366702858633748354489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340456911135239089165569659 510685366702858633748354489)
      ·
        refine ⟨383014025027143975311265867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510685366702858633748354489 383014025027143975311265867)
        ·
          refine ⟨574521037540715962966898801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383014025027143975311265867 574521037540715962966898801)
          ·
            refine ⟨430890778155536972225174101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574521037540715962966898801 430890778155536972225174101)
            ·
              refine ⟨5049501306510198893263759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 430890778155536972225174101 5049501306510198893263759)
              ·
                refine ⟨7574251959765298339895639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049501306510198893263759 7574251959765298339895639)
                ·
                  refine ⟨11361377939647947509843459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7574251959765298339895639 11361377939647947509843459)
                  ·
                    refine ⟨17042066909471921264765189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11361377939647947509843459 17042066909471921264765189)
                    ·
                      refine ⟨3195387545525985237143473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17042066909471921264765189 3195387545525985237143473)
                      ·
                        rfl

theorem cell23_6222995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 1, 4].length) (baseStart_6222995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222995 prefixEnd_6222995 := by exact prefixLift 6222995
  have htrace : WordTrace (prefixWord ++ tailWord_6222995) baseStart_6222995 baseEnd_6222995 := by
    simpa [prefixWord, tailWord_6222995, baseEnd_6222995] using wordTrace_append hprefix tailTrace_6222995
  have hstable : (prefixWord ++ tailWord_6222995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222995).length < 2 ^ (prefixWord ++ tailWord_6222995).sum := by decide
  have hdescent : baseEnd_6222995 < baseStart_6222995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223012 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_6223012 : Nat := 118140960795 + 6223012 * 2 ^ 59
def prefixEnd_6223012 : Nat := 4983230072969 + 3 ^ 40 * 6223012 * 2
def baseEnd_6223012 : Nat := 3195396274697111670630895

theorem tailTrace_6223012 : CollatzResearch.WordTrace tailWord_6223012 prefixEnd_6223012 3195396274697111670630895 := by
  unfold tailWord_6223012
  simp only [CollatzResearch.WordTrace]
  refine ⟨113485947065548902340207645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151314596087398536453610193 113485947065548902340207645)
  ·
    refine ⟨42557230149580838377577867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113485947065548902340207645 42557230149580838377577867)
    ·
      refine ⟨63835845224371257566366801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42557230149580838377577867 63835845224371257566366801)
      ·
        refine ⟨47876883918278443174775101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63835845224371257566366801 47876883918278443174775101)
        ·
          refine ⟨17953831469354416190540663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47876883918278443174775101 17953831469354416190540663)
          ·
            refine ⟨26930747204031624285810995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17953831469354416190540663 26930747204031624285810995)
            ·
              refine ⟨40396120806047436428716493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26930747204031624285810995 40396120806047436428716493)
              ·
                refine ⟨15148545302267788660768685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40396120806047436428716493 15148545302267788660768685)
                ·
                  refine ⟨5680704488350420747788257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15148545302267788660768685 5680704488350420747788257)
                  ·
                    refine ⟨4260528366262815560841193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5680704488350420747788257 4260528366262815560841193)
                    ·
                      refine ⟨3195396274697111670630895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260528366262815560841193 3195396274697111670630895)
                      ·
                        rfl

theorem cell23_6223012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_6223012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223012 prefixEnd_6223012 := by exact prefixLift 6223012
  have htrace : WordTrace (prefixWord ++ tailWord_6223012) baseStart_6223012 baseEnd_6223012 := by
    simpa [prefixWord, tailWord_6223012, baseEnd_6223012] using wordTrace_append hprefix tailTrace_6223012
  have hstable : (prefixWord ++ tailWord_6223012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223012).length < 2 ^ (prefixWord ++ tailWord_6223012).sum := by decide
  have hdescent : baseEnd_6223012 < baseStart_6223012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223015 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_6223015 : Nat := 118140960795 + 6223015 * 2 ^ 59
def prefixEnd_6223015 : Nat := 4983230072969 + 3 ^ 40 * 6223015 * 2
def baseEnd_6223015 : Nat := 3195397815139075158893381

theorem tailTrace_6223015 : CollatzResearch.WordTrace tailWord_6223015 prefixEnd_6223015 3195397815139075158893381 := by
  unfold tailWord_6223015
  simp only [CollatzResearch.WordTrace]
  refine ⟨226972003550086936192774499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151314669033391290795182999 226972003550086936192774499)
  ·
    refine ⟨340458005325130404289161749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226972003550086936192774499 340458005325130404289161749)
    ·
      refine ⟨15958968999615487701054457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 340458005325130404289161749 15958968999615487701054457)
      ·
        refine ⟨11969226749711615775790843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15958968999615487701054457 11969226749711615775790843)
        ·
          refine ⟨17953840124567423663686265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969226749711615775790843 17953840124567423663686265)
          ·
            refine ⟨13465380093425567747764699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17953840124567423663686265 13465380093425567747764699)
            ·
              refine ⟨20198070140138351621647049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13465380093425567747764699 20198070140138351621647049)
              ·
                refine ⟨15148552605103763716235287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20198070140138351621647049 15148552605103763716235287)
                ·
                  refine ⟨22722828907655645574352931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15148552605103763716235287 22722828907655645574352931)
                  ·
                    refine ⟨34084243361483468361529397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22722828907655645574352931 34084243361483468361529397)
                    ·
                      refine ⟨3195397815139075158893381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34084243361483468361529397 3195397815139075158893381)
                      ·
                        rfl

theorem cell23_6223015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_6223015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223015 prefixEnd_6223015 := by exact prefixLift 6223015
  have htrace : WordTrace (prefixWord ++ tailWord_6223015) baseStart_6223015 baseEnd_6223015 := by
    simpa [prefixWord, tailWord_6223015, baseEnd_6223015] using wordTrace_append hprefix tailTrace_6223015
  have hstable : (prefixWord ++ tailWord_6223015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223015).length < 2 ^ (prefixWord ++ tailWord_6223015).sum := by decide
  have hdescent : baseEnd_6223015 < baseStart_6223015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223025 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6223025 : Nat := 118140960795 + 6223025 * 2 ^ 59
def prefixEnd_6223025 : Nat := 4983230072969 + 3 ^ 40 * 6223025 * 2
def baseEnd_6223025 : Nat := 3195402949945620119768335

theorem tailTrace_6223025 : CollatzResearch.WordTrace tailWord_6223025 prefixEnd_6223025 3195402949945620119768335 := by
  unfold tailWord_6223025
  simp only [CollatzResearch.WordTrace]
  refine ⟨226972368280050707900638529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151314912186700471933759019 226972368280050707900638529)
  ·
    refine ⟨170229276210038030925478897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226972368280050707900638529 170229276210038030925478897)
    ·
      refine ⟨127671957157528523194109173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170229276210038030925478897 127671957157528523194109173)
      ·
        refine ⟨11969245983518299049447735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127671957157528523194109173 11969245983518299049447735)
        ·
          refine ⟨17953868975277448574171603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969245983518299049447735 17953868975277448574171603)
          ·
            refine ⟨26930803462916172861257405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17953868975277448574171603 26930803462916172861257405)
            ·
              refine ⟨10099051298593564822971527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26930803462916172861257405 10099051298593564822971527)
              ·
                refine ⟨15148576947890347234457291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10099051298593564822971527 15148576947890347234457291)
                ·
                  refine ⟨22722865421835520851685937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15148576947890347234457291 22722865421835520851685937)
                  ·
                    refine ⟨17042149066376640638764453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22722865421835520851685937 17042149066376640638764453)
                    ·
                      refine ⟨3195402949945620119768335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17042149066376640638764453 3195402949945620119768335)
                      ·
                        rfl

theorem cell23_6223025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6223025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223025 prefixEnd_6223025 := by exact prefixLift 6223025
  have htrace : WordTrace (prefixWord ++ tailWord_6223025) baseStart_6223025 baseEnd_6223025 := by
    simpa [prefixWord, tailWord_6223025, baseEnd_6223025] using wordTrace_append hprefix tailTrace_6223025
  have hstable : (prefixWord ++ tailWord_6223025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223025).length < 2 ^ (prefixWord ++ tailWord_6223025).sum := by decide
  have hdescent : baseEnd_6223025 < baseStart_6223025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223058 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6223058 : Nat := 118140960795 + 6223058 * 2 ^ 59
def prefixEnd_6223058 : Nat := 4983230072969 + 3 ^ 40 * 6223058 * 2
def baseEnd_6223058 : Nat := 3195419894807218490655683

theorem tailTrace_6223058 : CollatzResearch.WordTrace tailWord_6223058 prefixEnd_6223058 3195419894807218490655683 := by
  unfold tailWord_6223058
  simp only [CollatzResearch.WordTrace]
  refine ⟨56743392972232788634147457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151315714592620769691059885 56743392972232788634147457)
  ·
    refine ⟨42557544729174591475610593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56743392972232788634147457 42557544729174591475610593)
    ·
      refine ⟨31918158546880943606707945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42557544729174591475610593 31918158546880943606707945)
      ·
        refine ⟨23938618910160707705030959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31918158546880943606707945 23938618910160707705030959)
        ·
          refine ⟨35907928365241061557546439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23938618910160707705030959 35907928365241061557546439)
          ·
            refine ⟨53861892547861592336319659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35907928365241061557546439 53861892547861592336319659)
            ·
              refine ⟨80792838821792388504479489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53861892547861592336319659 80792838821792388504479489)
              ·
                refine ⟨60594629116344291378359617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80792838821792388504479489 60594629116344291378359617)
                ·
                  refine ⟨45445971837258218533769713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60594629116344291378359617 45445971837258218533769713)
                  ·
                    refine ⟨34084478877943663900327285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45445971837258218533769713 34084478877943663900327285)
                    ·
                      refine ⟨3195419894807218490655683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34084478877943663900327285 3195419894807218490655683)
                      ·
                        rfl

theorem cell23_6223058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6223058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223058 prefixEnd_6223058 := by exact prefixLift 6223058
  have htrace : WordTrace (prefixWord ++ tailWord_6223058) baseStart_6223058 baseEnd_6223058 := by
    simpa [prefixWord, tailWord_6223058, baseEnd_6223058] using wordTrace_append hprefix tailTrace_6223058
  have hstable : (prefixWord ++ tailWord_6223058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223058).length < 2 ^ (prefixWord ++ tailWord_6223058).sum := by decide
  have hdescent : baseEnd_6223058 < baseStart_6223058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223079 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6223079 : Nat := 118140960795 + 6223079 * 2 ^ 59
def prefixEnd_6223079 : Nat := 4983230072969 + 3 ^ 40 * 6223079 * 2
def baseEnd_6223079 : Nat := 3195430677900962908493087

theorem tailTrace_6223079 : CollatzResearch.WordTrace tailWord_6223079 prefixEnd_6223079 3195430677900962908493087 := by
  unfold tailWord_6223079
  simp only [CollatzResearch.WordTrace]
  refine ⟨226974337821855075123104291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151316225214570050082069527 226974337821855075123104291)
  ·
    refine ⟨340461506732782612684656437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226974337821855075123104291 340461506732782612684656437)
    ·
      refine ⟨31918266256198369939186541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340461506732782612684656437 31918266256198369939186541)
      ·
        refine ⟨11969349846074388727194953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31918266256198369939186541 11969349846074388727194953)
        ·
          refine ⟨8977012384555791545396215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11969349846074388727194953 8977012384555791545396215)
          ·
            refine ⟨13465518576833687318094323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8977012384555791545396215 13465518576833687318094323)
            ·
              refine ⟨20198277865250530977141485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13465518576833687318094323 20198277865250530977141485)
              ·
                refine ⟨7574354199468949116428057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20198277865250530977141485 7574354199468949116428057)
                ·
                  refine ⟨5680765649601711837321043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7574354199468949116428057 5680765649601711837321043)
                  ·
                    refine ⟨8521148474402567755981565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5680765649601711837321043 8521148474402567755981565)
                    ·
                      refine ⟨3195430677900962908493087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8521148474402567755981565 3195430677900962908493087)
                      ·
                        rfl

theorem cell23_6223079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6223079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223079 prefixEnd_6223079 := by exact prefixLift 6223079
  have htrace : WordTrace (prefixWord ++ tailWord_6223079) baseStart_6223079 baseEnd_6223079 := by
    simpa [prefixWord, tailWord_6223079, baseEnd_6223079] using wordTrace_append hprefix tailTrace_6223079
  have hstable : (prefixWord ++ tailWord_6223079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223079).length < 2 ^ (prefixWord ++ tailWord_6223079).sum := by decide
  have hdescent : baseEnd_6223079 < baseStart_6223079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223102 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_6223102 : Nat := 118140960795 + 6223102 * 2 ^ 59
def prefixEnd_6223102 : Nat := 4983230072969 + 3 ^ 40 * 6223102 * 2
def baseEnd_6223102 : Nat := 3195442487956016318505481

theorem tailTrace_6223102 : CollatzResearch.WordTrace tailWord_6223102 prefixEnd_6223102 3195442487956016318505481 := by
  unfold tailWord_6223102
  simp only [CollatzResearch.WordTrace]
  refine ⟨28371897087596468756398945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151316784467181166700794373 28371897087596468756398945)
  ·
    refine ⟨21278922815697351567299209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28371897087596468756398945 21278922815697351567299209)
    ·
      refine ⟨15959192111773013675474407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21278922815697351567299209 15959192111773013675474407)
      ·
        refine ⟨23938788167659520513211611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15959192111773013675474407 23938788167659520513211611)
        ·
          refine ⟨35908182251489280769817417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23938788167659520513211611 35908182251489280769817417)
          ·
            refine ⟨26931136688616960577363063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35908182251489280769817417 26931136688616960577363063)
            ·
              refine ⟨40396705032925440866044595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26931136688616960577363063 40396705032925440866044595)
              ·
                refine ⟨60595057549388161299066893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40396705032925440866044595 60595057549388161299066893)
                ·
                  refine ⟨22723146581020560487150085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60595057549388161299066893 22723146581020560487150085)
                  ·
                    refine ⟨4260589983941355091340641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22723146581020560487150085 4260589983941355091340641)
                    ·
                      refine ⟨3195442487956016318505481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260589983941355091340641 3195442487956016318505481)
                      ·
                        rfl

theorem cell23_6223102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_6223102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223102 prefixEnd_6223102 := by exact prefixLift 6223102
  have htrace : WordTrace (prefixWord ++ tailWord_6223102) baseStart_6223102 baseEnd_6223102 := by
    simpa [prefixWord, tailWord_6223102, baseEnd_6223102] using wordTrace_append hprefix tailTrace_6223102
  have hstable : (prefixWord ++ tailWord_6223102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223102).length < 2 ^ (prefixWord ++ tailWord_6223102).sum := by decide
  have hdescent : baseEnd_6223102 < baseStart_6223102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223155 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 2, 5]
def baseStart_6223155 : Nat := 118140960795 + 6223155 * 2 ^ 59
def prefixEnd_6223155 : Nat := 4983230072969 + 3 ^ 40 * 6223155 * 2
def baseEnd_6223155 : Nat := 1065156567476901537047579

theorem tailTrace_6223155 : CollatzResearch.WordTrace tailWord_6223155 prefixEnd_6223155 1065156567476901537047579 := by
  unfold tailWord_6223155
  simp only [CollatzResearch.WordTrace]
  refine ⟨226977109769579740102870919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151318073179719826735247279 226977109769579740102870919)
  ·
    refine ⟨340465664654369610154306379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226977109769579740102870919 340465664654369610154306379)
    ·
      refine ⟨510698496981554415231459569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340465664654369610154306379 510698496981554415231459569)
      ·
        refine ⟨383023872736165811423594677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510698496981554415231459569 383023872736165811423594677)
        ·
          refine ⟨35908488069015544820962001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 383023872736165811423594677 35908488069015544820962001)
          ·
            refine ⟨26931366051761658615721501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35908488069015544820962001 26931366051761658615721501)
            ·
              refine ⟨10099262269410621980895563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26931366051761658615721501 10099262269410621980895563)
              ·
                refine ⟨15148893404115932971343345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10099262269410621980895563 15148893404115932971343345)
                ·
                  refine ⟨11361670053086949728507509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15148893404115932971343345 11361670053086949728507509)
                  ·
                    refine ⟨1065156567476901537047579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11361670053086949728507509 1065156567476901537047579)
                    ·
                      rfl

theorem cell23_6223155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 5].length) (baseStart_6223155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223155 prefixEnd_6223155 := by exact prefixLift 6223155
  have htrace : WordTrace (prefixWord ++ tailWord_6223155) baseStart_6223155 baseEnd_6223155 := by
    simpa [prefixWord, tailWord_6223155, baseEnd_6223155] using wordTrace_append hprefix tailTrace_6223155
  have hstable : (prefixWord ++ tailWord_6223155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223155).length < 2 ^ (prefixWord ++ tailWord_6223155).sum := by decide
  have hdescent : baseEnd_6223155 < baseStart_6223155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223178 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_6223178 : Nat := 118140960795 + 6223178 * 2 ^ 59
def prefixEnd_6223178 : Nat := 4983230072969 + 3 ^ 40 * 6223178 * 2
def baseEnd_6223178 : Nat := 3195481512485758021155131

theorem tailTrace_6223178 : CollatzResearch.WordTrace tailWord_6223178 prefixEnd_6223178 3195481512485758021155131 := by
  unfold tailWord_6223178
  simp only [CollatzResearch.WordTrace]
  refine ⟨56744487162124103757739547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151318632432330943353972125 56744487162124103757739547)
  ·
    refine ⟨85116730743186155636609321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56744487162124103757739547 85116730743186155636609321)
    ·
      refine ⟨63837548057389616727456991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85116730743186155636609321 63837548057389616727456991)
      ·
        refine ⟨95756322086084425091185487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63837548057389616727456991 95756322086084425091185487)
        ·
          refine ⟨143634483129126637636778231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95756322086084425091185487 143634483129126637636778231)
          ·
            refine ⟨215451724693689956455167347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143634483129126637636778231 215451724693689956455167347)
            ·
              refine ⟨323177587040534934682751021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215451724693689956455167347 323177587040534934682751021)
              ·
                refine ⟨121191595140200600506031633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323177587040534934682751021 121191595140200600506031633)
                ·
                  refine ⟨90893696355150450379523725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121191595140200600506031633 90893696355150450379523725)
                  ·
                    refine ⟨34085136133181418892321397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90893696355150450379523725 34085136133181418892321397)
                    ·
                      refine ⟨3195481512485758021155131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34085136133181418892321397 3195481512485758021155131)
                      ·
                        rfl

theorem cell23_6223178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_6223178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223178 prefixEnd_6223178 := by exact prefixLift 6223178
  have htrace : WordTrace (prefixWord ++ tailWord_6223178) baseStart_6223178 baseEnd_6223178 := by
    simpa [prefixWord, tailWord_6223178, baseEnd_6223178] using wordTrace_append hprefix tailTrace_6223178
  have hstable : (prefixWord ++ tailWord_6223178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223178).length < 2 ^ (prefixWord ++ tailWord_6223178).sum := by decide
  have hdescent : baseEnd_6223178 < baseStart_6223178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223202 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6223202 : Nat := 118140960795 + 6223202 * 2 ^ 59
def prefixEnd_6223202 : Nat := 4983230072969 + 3 ^ 40 * 6223202 * 2
def baseEnd_6223202 : Nat := 1065164612007155309085007

theorem tailTrace_6223202 : CollatzResearch.WordTrace tailWord_6223202 prefixEnd_6223202 1065164612007155309085007 := by
  unfold tailWord_6223202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56744706000102366782457965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151319216000272978086554573 56744706000102366782457965)
  ·
    refine ⟨21279264750038387543421737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56744706000102366782457965 21279264750038387543421737)
    ·
      refine ⟨15959448562528790657566303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21279264750038387543421737 15959448562528790657566303)
      ·
        refine ⟨23939172843793185986349455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15959448562528790657566303 23939172843793185986349455)
        ·
          refine ⟨35908759265689778979524183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23939172843793185986349455 35908759265689778979524183)
          ·
            refine ⟨53863138898534668469286275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35908759265689778979524183 53863138898534668469286275)
            ·
              refine ⟨80794708347802002703929413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53863138898534668469286275 80794708347802002703929413)
              ·
                refine ⟨15149007815212875506986765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80794708347802002703929413 15149007815212875506986765)
                ·
                  refine ⟨5680877930704828315120037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15149007815212875506986765 5680877930704828315120037)
                  ·
                    refine ⟨1065164612007155309085007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680877930704828315120037 1065164612007155309085007)
                    ·
                      rfl

theorem cell23_6223202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6223202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223202 prefixEnd_6223202 := by exact prefixLift 6223202
  have htrace : WordTrace (prefixWord ++ tailWord_6223202) baseStart_6223202 baseEnd_6223202 := by
    simpa [prefixWord, tailWord_6223202, baseEnd_6223202] using wordTrace_append hprefix tailTrace_6223202
  have hstable : (prefixWord ++ tailWord_6223202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223202).length < 2 ^ (prefixWord ++ tailWord_6223202).sum := by decide
  have hdescent : baseEnd_6223202 < baseStart_6223202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223236 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_6223236 : Nat := 118140960795 + 6223236 * 2 ^ 59
def prefixEnd_6223236 : Nat := 4983230072969 + 3 ^ 40 * 6223236 * 2
def baseEnd_6223236 : Nat := 1065170431454572931409955

theorem tailTrace_6223236 : CollatzResearch.WordTrace tailWord_6223236 prefixEnd_6223236 1065170431454572931409955 := by
  unfold tailWord_6223236
  simp only [CollatzResearch.WordTrace]
  refine ⟨113490032041143145468284781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151320042721524193957713041 113490032041143145468284781)
  ·
    refine ⟨42558762015428679550606793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113490032041143145468284781 42558762015428679550606793)
    ·
      refine ⟨31919071511571509662955095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42558762015428679550606793 31919071511571509662955095)
      ·
        refine ⟨47878607267357264494432643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31919071511571509662955095 47878607267357264494432643)
        ·
          refine ⟨71817910901035896741648965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47878607267357264494432643 71817910901035896741648965)
          ·
            refine ⟨13465858293944230639059181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71817910901035896741648965 13465858293944230639059181)
            ·
              refine ⟨5049696860229086489647193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13465858293944230639059181 5049696860229086489647193)
              ·
                refine ⟨3787272645171814867235395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5049696860229086489647193 3787272645171814867235395)
                ·
                  refine ⟨5680908967757722300853093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787272645171814867235395 5680908967757722300853093)
                  ·
                    refine ⟨1065170431454572931409955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680908967757722300853093 1065170431454572931409955)
                    ·
                      rfl

theorem cell23_6223236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_6223236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223236 prefixEnd_6223236 := by exact prefixLift 6223236
  have htrace : WordTrace (prefixWord ++ tailWord_6223236) baseStart_6223236 baseEnd_6223236 := by
    simpa [prefixWord, tailWord_6223236, baseEnd_6223236] using wordTrace_append hprefix tailTrace_6223236
  have hstable : (prefixWord ++ tailWord_6223236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223236).length < 2 ^ (prefixWord ++ tailWord_6223236).sum := by decide
  have hdescent : baseEnd_6223236 < baseStart_6223236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223322 : List Nat := [3, 1, 1, 2, 3, 3, 3, 7]
def baseStart_6223322 : Nat := 118140960795 + 6223322 * 2 ^ 59
def prefixEnd_6223322 : Nat := 4983230072969 + 3 ^ 40 * 6223322 * 2
def baseEnd_6223322 : Nat := 118353905692592794731647

theorem tailTrace_6223322 : CollatzResearch.WordTrace tailWord_6223322 prefixEnd_6223322 118353905692592794731647 := by
  unfold tailWord_6223322
  simp only [CollatzResearch.WordTrace]
  refine ⟨56745800189993681906050055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151322133839983151749466813 56745800189993681906050055)
  ·
    refine ⟨85118700284990522859075083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56745800189993681906050055 85118700284990522859075083)
    ·
      refine ⟨127678050427485784288612625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85118700284990522859075083 127678050427485784288612625)
      ·
        refine ⟨95758537820614338216459469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127678050427485784288612625 95758537820614338216459469)
        ·
          refine ⟨35909451682730376831172301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95758537820614338216459469 35909451682730376831172301)
          ·
            refine ⟨13466044381023891311689613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35909451682730376831172301 13466044381023891311689613)
            ·
              refine ⟨5049766642883959241883605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13466044381023891311689613 5049766642883959241883605)
              ·
                refine ⟨118353905692592794731647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5049766642883959241883605 118353905692592794731647)
                ·
                  rfl

theorem cell23_6223322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_6223322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223322 prefixEnd_6223322 := by exact prefixLift 6223322
  have htrace : WordTrace (prefixWord ++ tailWord_6223322) baseStart_6223322 baseEnd_6223322 := by
    simpa [prefixWord, tailWord_6223322, baseEnd_6223322] using wordTrace_append hprefix tailTrace_6223322
  have hstable : (prefixWord ++ tailWord_6223322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223322).length < 2 ^ (prefixWord ++ tailWord_6223322).sum := by decide
  have hdescent : baseEnd_6223322 < baseStart_6223322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223333 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6223333 : Nat := 118140960795 + 6223333 * 2 ^ 59
def prefixEnd_6223333 : Nat := 4983230072969 + 3 ^ 40 * 6223333 * 2
def baseEnd_6223333 : Nat := 3195561101987204914716919

theorem tailTrace_6223333 : CollatzResearch.WordTrace tailWord_6223333 prefixEnd_6223333 3195561101987204914716919 := by
  unfold tailWord_6223333
  simp only [CollatzResearch.WordTrace]
  refine ⟨226983601962934876502850653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151322401308623251001900435 226983601962934876502850653)
  ·
    refine ⟨85118850736100578688568995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226983601962934876502850653 85118850736100578688568995)
    ·
      refine ⟨127678276104150868032853493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85118850736100578688568995 127678276104150868032853493)
      ·
        refine ⟨11969838384764143878080015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127678276104150868032853493 11969838384764143878080015)
        ·
          refine ⟨17954757577146215817120023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969838384764143878080015 17954757577146215817120023)
          ·
            refine ⟨26932136365719323725680035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17954757577146215817120023 26932136365719323725680035)
            ·
              refine ⟨40398204548578985588520053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26932136365719323725680035 40398204548578985588520053)
              ·
                refine ⟨3787331676429279898923755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40398204548578985588520053 3787331676429279898923755)
                ·
                  refine ⟨5680997514643919848385633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787331676429279898923755 5680997514643919848385633)
                  ·
                    refine ⟨4260748135982939886289225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5680997514643919848385633 4260748135982939886289225)
                    ·
                      refine ⟨3195561101987204914716919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260748135982939886289225 3195561101987204914716919)
                      ·
                        rfl

theorem cell23_6223333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6223333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223333 prefixEnd_6223333 := by exact prefixLift 6223333
  have htrace : WordTrace (prefixWord ++ tailWord_6223333) baseStart_6223333 baseEnd_6223333 := by
    simpa [prefixWord, tailWord_6223333, baseEnd_6223333] using wordTrace_append hprefix tailTrace_6223333
  have hstable : (prefixWord ++ tailWord_6223333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223333).length < 2 ^ (prefixWord ++ tailWord_6223333).sum := by decide
  have hdescent : baseEnd_6223333 < baseStart_6223333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223373 : List Nat := [1, 7, 1, 1, 2, 2, 2, 7]
def baseStart_6223373 : Nat := 118140960795 + 6223373 * 2 ^ 59
def prefixEnd_6223373 : Nat := 4983230072969 + 3 ^ 40 * 6223373 * 2
def baseEnd_6223373 : Nat := 118354875600495731785805

theorem tailTrace_6223373 : CollatzResearch.WordTrace tailWord_6223373 prefixEnd_6223373 118354875600495731785805 := by
  unfold tailWord_6223373
  simp only [CollatzResearch.WordTrace]
  refine ⟨226985060882789963334306773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151323373921859975556204515 226985060882789963334306773)
  ·
    refine ⟨5319962364440389765647815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 226985060882789963334306773 5319962364440389765647815)
    ·
      refine ⟨7979943546660584648471723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319962364440389765647815 7979943546660584648471723)
      ·
        refine ⟨11969915319990876972707585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979943546660584648471723 11969915319990876972707585)
        ·
          refine ⟨8977436489993157729530689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11969915319990876972707585 8977436489993157729530689)
          ·
            refine ⟨6733077367494868297148017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8977436489993157729530689 6733077367494868297148017)
            ·
              refine ⟨5049808025621151222861013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6733077367494868297148017 5049808025621151222861013)
              ·
                refine ⟨118354875600495731785805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5049808025621151222861013 118354875600495731785805)
                ·
                  rfl

theorem cell23_6223373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 7].length) (baseStart_6223373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223373 prefixEnd_6223373 := by exact prefixLift 6223373
  have htrace : WordTrace (prefixWord ++ tailWord_6223373) baseStart_6223373 baseEnd_6223373 := by
    simpa [prefixWord, tailWord_6223373, baseEnd_6223373] using wordTrace_append hprefix tailTrace_6223373
  have hstable : (prefixWord ++ tailWord_6223373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223373).length < 2 ^ (prefixWord ++ tailWord_6223373).sum := by decide
  have hdescent : baseEnd_6223373 < baseStart_6223373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223389 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_6223389 : Nat := 118140960795 + 6223389 * 2 ^ 59
def prefixEnd_6223389 : Nat := 4983230072969 + 3 ^ 40 * 6223389 * 2
def baseEnd_6223389 : Nat := 3195589856903856695616661

theorem tailTrace_6223389 : CollatzResearch.WordTrace tailWord_6223389 prefixEnd_6223389 3195589856903856695616661 := by
  unfold tailWord_6223389
  simp only [CollatzResearch.WordTrace]
  refine ⟨226985644450731998066889221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151323762967154665377926147 226985644450731998066889221)
  ·
    refine ⟨42559808334512249637541729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226985644450731998066889221 42559808334512249637541729)
    ·
      refine ⟨31919856250884187228156297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42559808334512249637541729 31919856250884187228156297)
      ·
        refine ⟨23939892188163140421117223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31919856250884187228156297 23939892188163140421117223)
        ·
          refine ⟨35909838282244710631675835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23939892188163140421117223 35909838282244710631675835)
          ·
            refine ⟨53864757423367065947513753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35909838282244710631675835 53864757423367065947513753)
            ·
              refine ⟨40398568067525299460635315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53864757423367065947513753 40398568067525299460635315)
              ·
                refine ⟨60597852101287949190952973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40398568067525299460635315 60597852101287949190952973)
                ·
                  refine ⟨22724194537982980946607365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60597852101287949190952973 22724194537982980946607365)
                  ·
                    refine ⟨4260786475871808927488881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22724194537982980946607365 4260786475871808927488881)
                    ·
                      refine ⟨3195589856903856695616661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260786475871808927488881 3195589856903856695616661)
                      ·
                        rfl

theorem cell23_6223389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_6223389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223389 prefixEnd_6223389 := by exact prefixLift 6223389
  have htrace : WordTrace (prefixWord ++ tailWord_6223389) baseStart_6223389 baseEnd_6223389 := by
    simpa [prefixWord, tailWord_6223389, baseEnd_6223389] using wordTrace_append hprefix tailTrace_6223389
  have hstable : (prefixWord ++ tailWord_6223389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223389).length < 2 ^ (prefixWord ++ tailWord_6223389).sum := by decide
  have hdescent : baseEnd_6223389 < baseStart_6223389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223392 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6223392 : Nat := 118140960795 + 6223392 * 2 ^ 59
def prefixEnd_6223392 : Nat := 4983230072969 + 3 ^ 40 * 6223392 * 2
def baseEnd_6223392 : Nat := 3195591397345820183879147

theorem tailTrace_6223392 : CollatzResearch.WordTrace tailWord_6223392 prefixEnd_6223392 3195591397345820183879147 := by
  unfold tailWord_6223392
  simp only [CollatzResearch.WordTrace]
  refine ⟨113492876934860564789624215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151323835913147419719498953 113492876934860564789624215)
  ·
    refine ⟨170239315402290847184436323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113492876934860564789624215 170239315402290847184436323)
    ·
      refine ⟨255358973103436270776654485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170239315402290847184436323 255358973103436270776654485)
      ·
        refine ⟨11969951864223575192655679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255358973103436270776654485 11969951864223575192655679)
        ·
          refine ⟨17954927796335362788983519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969951864223575192655679 17954927796335362788983519)
          ·
            refine ⟨26932391694503044183475279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17954927796335362788983519 26932391694503044183475279)
            ·
              refine ⟨40398587541754566275212919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26932391694503044183475279 40398587541754566275212919)
              ·
                refine ⟨60597881312631849412819379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40398587541754566275212919 60597881312631849412819379)
                ·
                  refine ⟨90896821968947774119229069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60597881312631849412819379 90896821968947774119229069)
                  ·
                    refine ⟨34086308238355415294710901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90896821968947774119229069 34086308238355415294710901)
                    ·
                      refine ⟨3195591397345820183879147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34086308238355415294710901 3195591397345820183879147)
                      ·
                        rfl

theorem cell23_6223392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6223392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223392 prefixEnd_6223392 := by exact prefixLift 6223392
  have htrace : WordTrace (prefixWord ++ tailWord_6223392) baseStart_6223392 baseEnd_6223392 := by
    simpa [prefixWord, tailWord_6223392, baseEnd_6223392] using wordTrace_append hprefix tailTrace_6223392
  have hstable : (prefixWord ++ tailWord_6223392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223392).length < 2 ^ (prefixWord ++ tailWord_6223392).sum := by decide
  have hdescent : baseEnd_6223392 < baseStart_6223392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223423 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 2, 2, 2]
def baseStart_6223423 : Nat := 118140960795 + 6223423 * 2 ^ 59
def prefixEnd_6223423 : Nat := 4983230072969 + 3 ^ 40 * 6223423 * 2
def baseEnd_6223423 : Nat := 3195607315246109562591505

theorem tailTrace_6223423 : CollatzResearch.WordTrace tailWord_6223423 prefixEnd_6223423 3195607315246109562591505 := by
  unfold tailWord_6223423
  simp only [CollatzResearch.WordTrace]
  refine ⟨226986884532608821873626923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151324589688405881249084615 226986884532608821873626923)
  ·
    refine ⟨340480326798913232810440385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226986884532608821873626923 340480326798913232810440385)
    ·
      refine ⟨255360245099184924607830289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340480326798913232810440385 255360245099184924607830289)
      ·
        refine ⟨191520183824388693455872717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255360245099184924607830289 191520183824388693455872717)
        ·
          refine ⟨71820068934145760045952269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191520183824388693455872717 71820068934145760045952269)
          ·
            refine ⟨26932525850304660017232101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71820068934145760045952269 26932525850304660017232101)
            ·
              refine ⟨5049848596932123753231019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26932525850304660017232101 5049848596932123753231019)
              ·
                refine ⟨7574772895398185629846529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049848596932123753231019 7574772895398185629846529)
                ·
                  refine ⟨5681079671548639222384897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7574772895398185629846529 5681079671548639222384897)
                  ·
                    refine ⟨4260809753661479416788673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681079671548639222384897 4260809753661479416788673)
                    ·
                      refine ⟨3195607315246109562591505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260809753661479416788673 3195607315246109562591505)
                      ·
                        rfl

theorem cell23_6223423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_6223423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223423 prefixEnd_6223423 := by exact prefixLift 6223423
  have htrace : WordTrace (prefixWord ++ tailWord_6223423) baseStart_6223423 baseEnd_6223423 := by
    simpa [prefixWord, tailWord_6223423, baseEnd_6223423] using wordTrace_append hprefix tailTrace_6223423
  have hstable : (prefixWord ++ tailWord_6223423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223423).length < 2 ^ (prefixWord ++ tailWord_6223423).sum := by decide
  have hdescent : baseEnd_6223423 < baseStart_6223423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223435 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_6223435 : Nat := 118140960795 + 6223435 * 2 ^ 59
def prefixEnd_6223435 : Nat := 4983230072969 + 3 ^ 40 * 6223435 * 2
def baseEnd_6223435 : Nat := 3195613477013963515641449

theorem tailTrace_6223435 : CollatzResearch.WordTrace tailWord_6223435 prefixEnd_6223435 3195613477013963515641449 := by
  unfold tailWord_6223435
  simp only [CollatzResearch.WordTrace]
  refine ⟨226987322208565347923063759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151324881472376898615375839 226987322208565347923063759)
  ·
    refine ⟨340480983312848021884595639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226987322208565347923063759 340480983312848021884595639)
    ·
      refine ⟨510721474969272032826893459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340480983312848021884595639 510721474969272032826893459)
      ·
        refine ⟨766082212453908049240340189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510721474969272032826893459 766082212453908049240340189)
        ·
          refine ⟨287280829670215518465127571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 766082212453908049240340189 287280829670215518465127571)
          ·
            refine ⟨430921244505323277697691357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287280829670215518465127571 430921244505323277697691357)
            ·
              refine ⟨161595466689496229136634259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430921244505323277697691357 161595466689496229136634259)
              ·
                refine ⟨242393200034244343704951389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161595466689496229136634259 242393200034244343704951389)
                ·
                  refine ⟨90897450012841628889356771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242393200034244343704951389 90897450012841628889356771)
                  ·
                    refine ⟨136346175019262443334035157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90897450012841628889356771 136346175019262443334035157)
                    ·
                      refine ⟨3195613477013963515641449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136346175019262443334035157 3195613477013963515641449)
                      ·
                        rfl

theorem cell23_6223435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_6223435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223435 prefixEnd_6223435 := by exact prefixLift 6223435
  have htrace : WordTrace (prefixWord ++ tailWord_6223435) baseStart_6223435 baseEnd_6223435 := by
    simpa [prefixWord, tailWord_6223435, baseEnd_6223435] using wordTrace_append hprefix tailTrace_6223435
  have hstable : (prefixWord ++ tailWord_6223435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223435).length < 2 ^ (prefixWord ++ tailWord_6223435).sum := by decide
  have hdescent : baseEnd_6223435 < baseStart_6223435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223489 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 5, 4]
def baseStart_6223489 : Nat := 118140960795 + 6223489 * 2 ^ 59
def prefixEnd_6223489 : Nat := 4983230072969 + 3 ^ 40 * 6223489 * 2
def baseEnd_6223489 : Nat := 1065213734989768768122067

theorem tailTrace_6223489 : CollatzResearch.WordTrace tailWord_6223489 prefixEnd_6223489 1065213734989768768122067 := by
  unfold tailWord_6223489
  simp only [CollatzResearch.WordTrace]
  refine ⟨226989291750369715145529521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151326194500246476763686347 226989291750369715145529521)
  ·
    refine ⟨170241968812777286359147141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226989291750369715145529521 170241968812777286359147141)
    ·
      refine ⟨31920369152395741192340089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170241968812777286359147141 31920369152395741192340089)
      ·
        refine ⟨23940276864296805894255067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31920369152395741192340089 23940276864296805894255067)
        ·
          refine ⟨35910415296445208841382601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23940276864296805894255067 35910415296445208841382601)
          ·
            refine ⟨26932811472333906631036951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35910415296445208841382601 26932811472333906631036951)
            ·
              refine ⟨40399217208500859946555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26932811472333906631036951 40399217208500859946555427)
              ·
                refine ⟨60598825812751289919833141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40399217208500859946555427 60598825812751289919833141)
                ·
                  refine ⟨5681139919945433429984357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60598825812751289919833141 5681139919945433429984357)
                  ·
                    refine ⟨1065213734989768768122067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5681139919945433429984357 1065213734989768768122067)
                    ·
                      rfl

theorem cell23_6223489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_6223489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223489 prefixEnd_6223489 := by exact prefixLift 6223489
  have htrace : WordTrace (prefixWord ++ tailWord_6223489) baseStart_6223489 baseEnd_6223489 := by
    simpa [prefixWord, tailWord_6223489, baseEnd_6223489] using wordTrace_append hprefix tailTrace_6223489
  have hstable : (prefixWord ++ tailWord_6223489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223489).length < 2 ^ (prefixWord ++ tailWord_6223489).sum := by decide
  have hdescent : baseEnd_6223489 < baseStart_6223489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223496 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6223496 : Nat := 118140960795 + 6223496 * 2 ^ 59
def prefixEnd_6223496 : Nat := 4983230072969 + 3 ^ 40 * 6223496 * 2
def baseEnd_6223496 : Nat := 3195644799333887776978669

theorem tailTrace_6223496 : CollatzResearch.WordTrace tailWord_6223496 prefixEnd_6223496 3195644799333887776978669 := by
  unfold tailWord_6223496
  simp only [CollatzResearch.WordTrace]
  refine ⟨113494773530672177670517171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151326364707562903560689561 113494773530672177670517171)
  ·
    refine ⟨170242160296008266505775757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113494773530672177670517171 170242160296008266505775757)
    ·
      refine ⟨63840810111003099939665909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170242160296008266505775757 63840810111003099939665909)
      ·
        refine ⟨5985075947906540619343679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63840810111003099939665909 5985075947906540619343679)
        ·
          refine ⟨8977613921859810929015519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985075947906540619343679 8977613921859810929015519)
          ·
            refine ⟨13466420882789716393523279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8977613921859810929015519 13466420882789716393523279)
            ·
              refine ⟨20199631324184574590284919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13466420882789716393523279 20199631324184574590284919)
              ·
                refine ⟨30299446986276861885427379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20199631324184574590284919 30299446986276861885427379)
                ·
                  refine ⟨45449170479415292828141069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30299446986276861885427379 45449170479415292828141069)
                  ·
                    refine ⟨17043438929780734810552901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45449170479415292828141069 17043438929780734810552901)
                    ·
                      refine ⟨3195644799333887776978669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17043438929780734810552901 3195644799333887776978669)
                      ·
                        rfl

theorem cell23_6223496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6223496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223496 prefixEnd_6223496 := by exact prefixLift 6223496
  have htrace : WordTrace (prefixWord ++ tailWord_6223496) baseStart_6223496 baseEnd_6223496 := by
    simpa [prefixWord, tailWord_6223496, baseEnd_6223496] using wordTrace_append hprefix tailTrace_6223496
  have hstable : (prefixWord ++ tailWord_6223496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223496).length < 2 ^ (prefixWord ++ tailWord_6223496).sum := by decide
  have hdescent : baseEnd_6223496 < baseStart_6223496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223539 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 3, 5, 2]
def baseStart_6223539 : Nat := 118140960795 + 6223539 * 2 ^ 59
def prefixEnd_6223539 : Nat := 4983230072969 + 3 ^ 40 * 6223539 * 2
def baseEnd_6223539 : Nat := 3195666879002031108740971

theorem tailTrace_6223539 : CollatzResearch.WordTrace tailWord_6223539 prefixEnd_6223539 3195666879002031108740971 := by
  unfold tailWord_6223539
  simp only [CollatzResearch.WordTrace]
  refine ⟨226991115400188573684849671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151327410266792382456566447 226991115400188573684849671)
  ·
    refine ⟨340486673100282860527274507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226991115400188573684849671 340486673100282860527274507)
    ·
      refine ⟨510730009650424290790911761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340486673100282860527274507 510730009650424290790911761)
      ·
        refine ⟨383047507237818218093183821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510730009650424290790911761 383047507237818218093183821)
        ·
          refine ⟨143642815214181831784943933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383047507237818218093183821 143642815214181831784943933)
          ·
            refine ⟨53866055705318186919353975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143642815214181831784943933 53866055705318186919353975)
            ·
              refine ⟨80799083557977280379030963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53866055705318186919353975 80799083557977280379030963)
              ·
                refine ⟨121198625336965920568546445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80799083557977280379030963 121198625336965920568546445)
                ·
                  refine ⟨45449484501362220213204917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121198625336965920568546445 45449484501362220213204917)
                  ·
                    refine ⟨4260889172002708144987961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45449484501362220213204917 4260889172002708144987961)
                    ·
                      refine ⟨3195666879002031108740971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260889172002708144987961 3195666879002031108740971)
                      ·
                        rfl

theorem cell23_6223539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5, 2].length) (baseStart_6223539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223539 prefixEnd_6223539 := by exact prefixLift 6223539
  have htrace : WordTrace (prefixWord ++ tailWord_6223539) baseStart_6223539 baseEnd_6223539 := by
    simpa [prefixWord, tailWord_6223539, baseEnd_6223539] using wordTrace_append hprefix tailTrace_6223539
  have hstable : (prefixWord ++ tailWord_6223539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223539).length < 2 ^ (prefixWord ++ tailWord_6223539).sum := by decide
  have hdescent : baseEnd_6223539 < baseStart_6223539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223546 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_6223546 : Nat := 118140960795 + 6223546 * 2 ^ 59
def prefixEnd_6223546 : Nat := 4983230072969 + 3 ^ 40 * 6223546 * 2
def baseEnd_6223546 : Nat := 3195670473366612581353439

theorem tailTrace_6223546 : CollatzResearch.WordTrace tailWord_6223546 prefixEnd_6223546 3195670473366612581353439 := by
  unfold tailWord_6223546
  simp only [CollatzResearch.WordTrace]
  refine ⟨56747842677790803470088623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151327580474108809253569661 56747842677790803470088623)
  ·
    refine ⟨85121764016686205205132935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56747842677790803470088623 85121764016686205205132935)
    ·
      refine ⟨127682646025029307807699403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85121764016686205205132935 127682646025029307807699403)
      ·
        refine ⟨191523969037543961711549105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127682646025029307807699403 191523969037543961711549105)
        ·
          refine ⟨143642976778157971283661829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191523969037543961711549105 143642976778157971283661829)
          ·
            refine ⟨26933058145904619615686593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143642976778157971283661829 26933058145904619615686593)
            ·
              refine ⟨20199793609428464711764945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26933058145904619615686593 20199793609428464711764945)
              ·
                refine ⟨15149845207071348533823709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20199793609428464711764945 15149845207071348533823709)
                ·
                  refine ⟨5681191952651755700183891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15149845207071348533823709 5681191952651755700183891)
                  ·
                    refine ⟨8521787928977633550275837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5681191952651755700183891 8521787928977633550275837)
                    ·
                      refine ⟨3195670473366612581353439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8521787928977633550275837 3195670473366612581353439)
                      ·
                        rfl

theorem cell23_6223546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_6223546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223546 prefixEnd_6223546 := by exact prefixLift 6223546
  have htrace : WordTrace (prefixWord ++ tailWord_6223546) baseStart_6223546 baseEnd_6223546 := by
    simpa [prefixWord, tailWord_6223546, baseEnd_6223546] using wordTrace_append hprefix tailTrace_6223546
  have hstable : (prefixWord ++ tailWord_6223546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223546).length < 2 ^ (prefixWord ++ tailWord_6223546).sum := by decide
  have hdescent : baseEnd_6223546 < baseStart_6223546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223556 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_6223556 : Nat := 118140960795 + 6223556 * 2 ^ 59
def prefixEnd_6223556 : Nat := 4983230072969 + 3 ^ 40 * 6223556 * 2
def baseEnd_6223556 : Nat := 3195675608173157542228393

theorem tailTrace_6223556 : CollatzResearch.WordTrace tailWord_6223556 prefixEnd_6223556 3195675608173157542228393 := by
  unfold tailWord_6223556
  simp only [CollatzResearch.WordTrace]
  refine ⟨113495867720563492794109261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151327823627417990392145681 113495867720563492794109261)
  ·
    refine ⟨42560950395211309797790973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113495867720563492794109261 42560950395211309797790973)
    ·
      refine ⟨15960356398204241174171615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42560950395211309797790973 15960356398204241174171615)
      ·
        refine ⟨23940534597306361761257423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15960356398204241174171615 23940534597306361761257423)
        ·
          refine ⟨35910801895959542641886135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23940534597306361761257423 35910801895959542641886135)
          ·
            refine ⟨53866202843939313962829203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35910801895959542641886135 53866202843939313962829203)
            ·
              refine ⟨80799304265908970944243805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53866202843939313962829203 80799304265908970944243805)
              ·
                refine ⟨30299739099715864104091427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80799304265908970944243805 30299739099715864104091427)
                ·
                  refine ⟨45449608649573796156137141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30299739099715864104091427 45449608649573796156137141)
                  ·
                    refine ⟨4260900810897543389637857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45449608649573796156137141 4260900810897543389637857)
                    ·
                      refine ⟨3195675608173157542228393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260900810897543389637857 3195675608173157542228393)
                      ·
                        rfl

theorem cell23_6223556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_6223556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223556 prefixEnd_6223556 := by exact prefixLift 6223556
  have htrace : WordTrace (prefixWord ++ tailWord_6223556) baseStart_6223556 baseEnd_6223556 := by
    simpa [prefixWord, tailWord_6223556, baseEnd_6223556] using wordTrace_append hprefix tailTrace_6223556
  have hstable : (prefixWord ++ tailWord_6223556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223556).length < 2 ^ (prefixWord ++ tailWord_6223556).sum := by decide
  have hdescent : baseEnd_6223556 < baseStart_6223556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223574 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6223574 : Nat := 118140960795 + 6223574 * 2 ^ 59
def prefixEnd_6223574 : Nat := 4983230072969 + 3 ^ 40 * 6223574 * 2
def baseEnd_6223574 : Nat := 1065228283608312823934437

theorem tailTrace_6223574 : CollatzResearch.WordTrace tailWord_6223574 prefixEnd_6223574 1065228283608312823934437 := by
  unfold tailWord_6223574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187024497191360916398361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151328261303374516441582517 14187024497191360916398361)
  ·
    refine ⟨10640268372893520687298771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14187024497191360916398361 10640268372893520687298771)
    ·
      refine ⟨15960402559340281030948157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10640268372893520687298771 15960402559340281030948157)
      ·
        refine ⟨5985150959752605386605559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15960402559340281030948157 5985150959752605386605559)
        ·
          refine ⟨8977726439628908079908339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985150959752605386605559 8977726439628908079908339)
          ·
            refine ⟨13466589659443362119862509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8977726439628908079908339 13466589659443362119862509)
            ·
              refine ⟨5049971122291260794948441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13466589659443362119862509 5049971122291260794948441)
              ·
                refine ⟨3787478341718445596211331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5049971122291260794948441 3787478341718445596211331)
                ·
                  refine ⟨5681217512577668394316997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787478341718445596211331 5681217512577668394316997)
                  ·
                    refine ⟨1065228283608312823934437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5681217512577668394316997 1065228283608312823934437)
                    ·
                      rfl

theorem cell23_6223574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6223574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223574 prefixEnd_6223574 := by exact prefixLift 6223574
  have htrace : WordTrace (prefixWord ++ tailWord_6223574) baseStart_6223574 baseEnd_6223574 := by
    simpa [prefixWord, tailWord_6223574, baseEnd_6223574] using wordTrace_append hprefix tailTrace_6223574
  have hstable : (prefixWord ++ tailWord_6223574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223574).length < 2 ^ (prefixWord ++ tailWord_6223574).sum := by decide
  have hdescent : baseEnd_6223574 < baseStart_6223574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223589 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6223589 : Nat := 118140960795 + 6223589 * 2 ^ 59
def prefixEnd_6223589 : Nat := 4983230072969 + 3 ^ 40 * 6223589 * 2
def baseEnd_6223589 : Nat := 3195692553034755913115741

theorem tailTrace_6223589 : CollatzResearch.WordTrace tailWord_6223589 prefixEnd_6223589 3195692553034755913115741 := by
  unfold tailWord_6223589
  simp only [CollatzResearch.WordTrace]
  refine ⟨226992939050007432224169821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151328626033338288149446547 226992939050007432224169821)
  ·
    refine ⟨85122352143752787084063683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226992939050007432224169821 85122352143752787084063683)
    ·
      refine ⟨127683528215629180626095525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85122352143752787084063683 127683528215629180626095525)
      ·
        refine ⟨23940661540430471367392911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127683528215629180626095525 23940661540430471367392911)
        ·
          refine ⟨35910992310645707051089367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23940661540430471367392911 35910992310645707051089367)
          ·
            refine ⟨53866488465968560576634051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35910992310645707051089367 53866488465968560576634051)
            ·
              refine ⟨80799732698952840864951077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53866488465968560576634051 80799732698952840864951077)
              ·
                refine ⟨15149949881053657662178327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80799732698952840864951077 15149949881053657662178327)
                ·
                  refine ⟨22724924821580486493267491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15149949881053657662178327 22724924821580486493267491)
                  ·
                    refine ⟨34087387232370729739901237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22724924821580486493267491 34087387232370729739901237)
                    ·
                      refine ⟨3195692553034755913115741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34087387232370729739901237 3195692553034755913115741)
                      ·
                        rfl

theorem cell23_6223589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6223589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223589 prefixEnd_6223589 := by exact prefixLift 6223589
  have htrace : WordTrace (prefixWord ++ tailWord_6223589) baseStart_6223589 baseEnd_6223589 := by
    simpa [prefixWord, tailWord_6223589, baseEnd_6223589] using wordTrace_append hprefix tailTrace_6223589
  have hstable : (prefixWord ++ tailWord_6223589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223589).length < 2 ^ (prefixWord ++ tailWord_6223589).sum := by decide
  have hdescent : baseEnd_6223589 < baseStart_6223589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223599 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_6223599 : Nat := 118140960795 + 6223599 * 2 ^ 59
def prefixEnd_6223599 : Nat := 4983230072969 + 3 ^ 40 * 6223599 * 2
def baseEnd_6223599 : Nat := 3195697687841300873990695

theorem tailTrace_6223599 : CollatzResearch.WordTrace tailWord_6223599 prefixEnd_6223599 3195697687841300873990695 := by
  unfold tailWord_6223599
  simp only [CollatzResearch.WordTrace]
  refine ⟨226993303779971203932033851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151328869186647469288022567 226993303779971203932033851)
  ·
    refine ⟨340489955669956805898050777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226993303779971203932033851 340489955669956805898050777)
    ·
      refine ⟨255367466752467604423538083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340489955669956805898050777 255367466752467604423538083)
      ·
        refine ⟨383051200128701406635307125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255367466752467604423538083 383051200128701406635307125)
        ·
          refine ⟨35911050012065756872060043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 383051200128701406635307125 35911050012065756872060043)
          ·
            refine ⟨53866575018098635308090065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35911050012065756872060043 53866575018098635308090065)
            ·
              refine ⟨40399931263573976481067549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53866575018098635308090065 40399931263573976481067549)
              ·
                refine ⟨15149974223840241180400331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40399931263573976481067549 15149974223840241180400331)
                ·
                  refine ⟨22724961335760361770600497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15149974223840241180400331 22724961335760361770600497)
                  ·
                    refine ⟨17043721001820271327950373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22724961335760361770600497 17043721001820271327950373)
                    ·
                      refine ⟨3195697687841300873990695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17043721001820271327950373 3195697687841300873990695)
                      ·
                        rfl

theorem cell23_6223599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_6223599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223599 prefixEnd_6223599 := by exact prefixLift 6223599
  have htrace : WordTrace (prefixWord ++ tailWord_6223599) baseStart_6223599 baseEnd_6223599 := by
    simpa [prefixWord, tailWord_6223599, baseEnd_6223599] using wordTrace_append hprefix tailTrace_6223599
  have hstable : (prefixWord ++ tailWord_6223599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223599).length < 2 ^ (prefixWord ++ tailWord_6223599).sum := by decide
  have hdescent : baseEnd_6223599 < baseStart_6223599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223619 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 3]
def baseStart_6223619 : Nat := 118140960795 + 6223619 * 2 ^ 59
def prefixEnd_6223619 : Nat := 4983230072969 + 3 ^ 40 * 6223619 * 2
def baseEnd_6223619 : Nat := 3195707957454390795740603

theorem tailTrace_6223619 : CollatzResearch.WordTrace tailWord_6223619 prefixEnd_6223619 3195707957454390795740603 := by
  unfold tailWord_6223619
  simp only [CollatzResearch.WordTrace]
  refine ⟨226994033239898747347761911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151329355493265831565174607 226994033239898747347761911)
  ·
    refine ⟨340491049859848121021642867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226994033239898747347761911 340491049859848121021642867)
    ·
      refine ⟨510736574789772181532464301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340491049859848121021642867 510736574789772181532464301)
      ·
        refine ⟨191526215546164568074674113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510736574789772181532464301 191526215546164568074674113)
        ·
          refine ⟨143644661659623426056005585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191526215546164568074674113 143644661659623426056005585)
          ·
            refine ⟨107733496244717569542004189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143644661659623426056005585 107733496244717569542004189)
            ·
              refine ⟨40400061091769088578251571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107733496244717569542004189 40400061091769088578251571)
              ·
                refine ⟨60600091637653632867377357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40400061091769088578251571 60600091637653632867377357)
                ·
                  refine ⟨22725034364120112325266509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60600091637653632867377357 22725034364120112325266509)
                  ·
                    refine ⟨8521887886545042121974941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22725034364120112325266509 8521887886545042121974941)
                    ·
                      refine ⟨3195707957454390795740603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8521887886545042121974941 3195707957454390795740603)
                      ·
                        rfl

theorem cell23_6223619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_6223619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223619 prefixEnd_6223619 := by exact prefixLift 6223619
  have htrace : WordTrace (prefixWord ++ tailWord_6223619) baseStart_6223619 baseEnd_6223619 := by
    simpa [prefixWord, tailWord_6223619, baseEnd_6223619] using wordTrace_append hprefix tailTrace_6223619
  have hstable : (prefixWord ++ tailWord_6223619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223619).length < 2 ^ (prefixWord ++ tailWord_6223619).sum := by decide
  have hdescent : baseEnd_6223619 < baseStart_6223619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223623 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6223623 : Nat := 118140960795 + 6223623 * 2 ^ 59
def prefixEnd_6223623 : Nat := 4983230072969 + 3 ^ 40 * 6223623 * 2
def baseEnd_6223623 : Nat := 3195710011377008780090585

theorem tailTrace_6223623 : CollatzResearch.WordTrace tailWord_6223623 prefixEnd_6223623 3195710011377008780090585 := by
  unfold tailWord_6223623
  simp only [CollatzResearch.WordTrace]
  refine ⟨226994179131884256030907523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151329452754589504020605015 226994179131884256030907523)
  ·
    refine ⟨340491268697826384046361285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226994179131884256030907523 340491268697826384046361285)
    ·
      refine ⟨63842112880842447008692741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340491268697826384046361285 63842112880842447008692741)
      ·
        refine ⟨11970396165157958814129889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63842112880842447008692741 11970396165157958814129889)
        ·
          refine ⟨8977797123868469110597417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11970396165157958814129889 8977797123868469110597417)
          ·
            refine ⟨6733347842901351832948063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8977797123868469110597417 6733347842901351832948063)
            ·
              refine ⟨10100021764352027749422095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733347842901351832948063 10100021764352027749422095)
              ·
                refine ⟨15150032646528041624133143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10100021764352027749422095 15150032646528041624133143)
                ·
                  refine ⟨22725048969792062436199715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15150032646528041624133143 22725048969792062436199715)
                  ·
                    refine ⟨34087573454688093654299573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22725048969792062436199715 34087573454688093654299573)
                    ·
                      refine ⟨3195710011377008780090585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34087573454688093654299573 3195710011377008780090585)
                      ·
                        rfl

theorem cell23_6223623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6223623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223623 prefixEnd_6223623 := by exact prefixLift 6223623
  have htrace : WordTrace (prefixWord ++ tailWord_6223623) baseStart_6223623 baseEnd_6223623 := by
    simpa [prefixWord, tailWord_6223623, baseEnd_6223623] using wordTrace_append hprefix tailTrace_6223623
  have hstable : (prefixWord ++ tailWord_6223623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223623).length < 2 ^ (prefixWord ++ tailWord_6223623).sum := by decide
  have hdescent : baseEnd_6223623 < baseStart_6223623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223637 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_6223637 : Nat := 118140960795 + 6223637 * 2 ^ 59
def prefixEnd_6223637 : Nat := 4983230072969 + 3 ^ 40 * 6223637 * 2
def baseEnd_6223637 : Nat := 3195717200106171725315521

theorem tailTrace_6223637 : CollatzResearch.WordTrace tailWord_6223637 prefixEnd_6223637 3195717200106171725315521 := by
  unfold tailWord_6223637
  simp only [CollatzResearch.WordTrace]
  refine ⟨226994689753833536421917165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151329793169222357614611443 226994689753833536421917165)
  ·
    refine ⟨85123008657687576158218937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226994689753833536421917165 85123008657687576158218937)
    ·
      refine ⟨63842256493265682118664203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85123008657687576158218937 63842256493265682118664203)
      ·
        refine ⟨95763384739898523177996305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63842256493265682118664203 95763384739898523177996305)
        ·
          refine ⟨71822538554923892383497229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95763384739898523177996305 71822538554923892383497229)
          ·
            refine ⟨26933451958096459643811461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71822538554923892383497229 26933451958096459643811461)
            ·
              refine ⟨5050022242143086183214649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26933451958096459643811461 5050022242143086183214649)
              ·
                refine ⟨3787516681607314637410987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5050022242143086183214649 3787516681607314637410987)
                ·
                  refine ⟨5681275022410971956116481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787516681607314637410987 5681275022410971956116481)
                  ·
                    refine ⟨4260956266808228967087361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681275022410971956116481 4260956266808228967087361)
                    ·
                      refine ⟨3195717200106171725315521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260956266808228967087361 3195717200106171725315521)
                      ·
                        rfl

theorem cell23_6223637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_6223637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223637 prefixEnd_6223637 := by exact prefixLift 6223637
  have htrace : WordTrace (prefixWord ++ tailWord_6223637) baseStart_6223637 baseEnd_6223637 := by
    simpa [prefixWord, tailWord_6223637, baseEnd_6223637] using wordTrace_append hprefix tailTrace_6223637
  have hstable : (prefixWord ++ tailWord_6223637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223637).length < 2 ^ (prefixWord ++ tailWord_6223637).sum := by decide
  have hdescent : baseEnd_6223637 < baseStart_6223637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223639 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 2, 7]
def baseStart_6223639 : Nat := 118140960795 + 6223639 * 2 ^ 59
def prefixEnd_6223639 : Nat := 4983230072969 + 3 ^ 40 * 6223639 * 2
def baseEnd_6223639 : Nat := 1065239409022493572496837

theorem tailTrace_6223639 : CollatzResearch.WordTrace tailWord_6223639 prefixEnd_6223639 1065239409022493572496837 := by
  unfold tailWord_6223639
  simp only [CollatzResearch.WordTrace]
  refine ⟨226994762699826290763489971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151329841799884193842326647 226994762699826290763489971)
  ·
    refine ⟨340492144049739436145234957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226994762699826290763489971 340492144049739436145234957)
    ·
      refine ⟨127684554018652288554463109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340492144049739436145234957 127684554018652288554463109)
      ·
        refine ⟨23940853878497304103961833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127684554018652288554463109 23940853878497304103961833)
        ·
          refine ⟨17955640408872978077971375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23940853878497304103961833 17955640408872978077971375)
          ·
            refine ⟨26933460613309467116957063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17955640408872978077971375 26933460613309467116957063)
            ·
              refine ⟨40400190919964200675435595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26933460613309467116957063 40400190919964200675435595)
              ·
                refine ⟨60600286379946301013153393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40400190919964200675435595 60600286379946301013153393)
                ·
                  refine ⟨45450214784959725759865045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60600286379946301013153393 45450214784959725759865045)
                  ·
                    refine ⟨1065239409022493572496837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45450214784959725759865045 1065239409022493572496837)
                    ·
                      rfl

theorem cell23_6223639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_6223639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223639 prefixEnd_6223639 := by exact prefixLift 6223639
  have htrace : WordTrace (prefixWord ++ tailWord_6223639) baseStart_6223639 baseEnd_6223639 := by
    simpa [prefixWord, tailWord_6223639, baseEnd_6223639] using wordTrace_append hprefix tailTrace_6223639
  have hstable : (prefixWord ++ tailWord_6223639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223639).length < 2 ^ (prefixWord ++ tailWord_6223639).sum := by decide
  have hdescent : baseEnd_6223639 < baseStart_6223639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223653 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_6223653 : Nat := 118140960795 + 6223653 * 2 ^ 59
def prefixEnd_6223653 : Nat := 4983230072969 + 3 ^ 40 * 6223653 * 2
def baseEnd_6223653 : Nat := 3195725415796643662715447

theorem tailTrace_6223653 : CollatzResearch.WordTrace tailWord_6223653 prefixEnd_6223653 3195725415796643662715447 := by
  unfold tailWord_6223653
  simp only [CollatzResearch.WordTrace]
  refine ⟨226995273321775571154499613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151330182214517047436333075 226995273321775571154499613)
  ·
    refine ⟨85123227495665839182937355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226995273321775571154499613 85123227495665839182937355)
    ·
      refine ⟨127684841243498758774406033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85123227495665839182937355 127684841243498758774406033)
      ·
        refine ⟨95763630932624069080804525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127684841243498758774406033 95763630932624069080804525)
        ·
          refine ⟨35911361599734025905301697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95763630932624069080804525 35911361599734025905301697)
          ·
            refine ⟨26933521199800519428976273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35911361599734025905301697 26933521199800519428976273)
            ·
              refine ⟨20200140899850389571732205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26933521199800519428976273 20200140899850389571732205)
              ·
                refine ⟨7575052837443896089399577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20200140899850389571732205 7575052837443896089399577)
                ·
                  refine ⟨5681289628082922067049683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7575052837443896089399577 5681289628082922067049683)
                  ·
                    refine ⟨8521934442124383100574525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5681289628082922067049683 8521934442124383100574525)
                    ·
                      refine ⟨3195725415796643662715447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8521934442124383100574525 3195725415796643662715447)
                      ·
                        rfl

theorem cell23_6223653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_6223653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223653 prefixEnd_6223653 := by exact prefixLift 6223653
  have htrace : WordTrace (prefixWord ++ tailWord_6223653) baseStart_6223653 baseEnd_6223653 := by
    simpa [prefixWord, tailWord_6223653, baseEnd_6223653] using wordTrace_append hprefix tailTrace_6223653
  have hstable : (prefixWord ++ tailWord_6223653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223653).length < 2 ^ (prefixWord ++ tailWord_6223653).sum := by decide
  have hdescent : baseEnd_6223653 < baseStart_6223653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223689 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_6223689 : Nat := 118140960795 + 6223689 * 2 ^ 59
def prefixEnd_6223689 : Nat := 4983230072969 + 3 ^ 40 * 6223689 * 2
def baseEnd_6223689 : Nat := 3195743901100205521865281

theorem tailTrace_6223689 : CollatzResearch.WordTrace tailWord_6223689 prefixEnd_6223689 3195743901100205521865281 := by
  unfold tailWord_6223689
  simp only [CollatzResearch.WordTrace]
  refine ⟨226996586349645149302810121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151331057566430099535206747 226996586349645149302810121)
  ·
    refine ⟨170247439762233861977107591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226996586349645149302810121 170247439762233861977107591)
    ·
      refine ⟨255371159643350792965661387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170247439762233861977107591 255371159643350792965661387)
      ·
        refine ⟨383056739465026189448492081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255371159643350792965661387 383056739465026189448492081)
        ·
          refine ⟨287292554598769642086369061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383056739465026189448492081 287292554598769642086369061)
          ·
            refine ⟨53867353987269307891194199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287292554598769642086369061 53867353987269307891194199)
            ·
              refine ⟨80801030980903961836791299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53867353987269307891194199 80801030980903961836791299)
              ·
                refine ⟨121201546471355942755186949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80801030980903961836791299 121201546471355942755186949)
                ·
                  refine ⟨22725289963379239266597553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121201546471355942755186949 22725289963379239266597553)
                  ·
                    refine ⟨17043967472534429449948165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22725289963379239266597553 17043967472534429449948165)
                    ·
                      refine ⟨3195743901100205521865281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17043967472534429449948165 3195743901100205521865281)
                      ·
                        rfl

theorem cell23_6223689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_6223689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223689 prefixEnd_6223689 := by exact prefixLift 6223689
  have htrace : WordTrace (prefixWord ++ tailWord_6223689) baseStart_6223689 baseEnd_6223689 := by
    simpa [prefixWord, tailWord_6223689, baseEnd_6223689] using wordTrace_append hprefix tailTrace_6223689
  have hstable : (prefixWord ++ tailWord_6223689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223689).length < 2 ^ (prefixWord ++ tailWord_6223689).sum := by decide
  have hdescent : baseEnd_6223689 < baseStart_6223689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223729 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_6223729 : Nat := 118140960795 + 6223729 * 2 ^ 59
def prefixEnd_6223729 : Nat := 4983230072969 + 3 ^ 40 * 6223729 * 2
def baseEnd_6223729 : Nat := 1065254813442128455121699

theorem tailTrace_6223729 : CollatzResearch.WordTrace tailWord_6223729 prefixEnd_6223729 1065254813442128455121699 := by
  unfold tailWord_6223729
  simp only [CollatzResearch.WordTrace]
  refine ⟨226998045269500236134266241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151332030179666824089510827 226998045269500236134266241)
  ·
    refine ⟨170248533952125177100699681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226998045269500236134266241 170248533952125177100699681)
    ·
      refine ⟨127686400464093882825524761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170248533952125177100699681 127686400464093882825524761)
      ·
        refine ⟨95764800348070412119143571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127686400464093882825524761 95764800348070412119143571)
        ·
          refine ⟨143647200522105618178715357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95764800348070412119143571 143647200522105618178715357)
          ·
            refine ⟨53867700195789606817018259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143647200522105618178715357 53867700195789606817018259)
            ·
              refine ⟨80801550293684410225527389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53867700195789606817018259 80801550293684410225527389)
              ·
                refine ⟨30300581360131653834572771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80801550293684410225527389 30300581360131653834572771)
                ·
                  refine ⟨45450872040197480751859157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30300581360131653834572771 45450872040197480751859157)
                  ·
                    refine ⟨1065254813442128455121699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45450872040197480751859157 1065254813442128455121699)
                    ·
                      rfl

theorem cell23_6223729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_6223729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223729 prefixEnd_6223729 := by exact prefixLift 6223729
  have htrace : WordTrace (prefixWord ++ tailWord_6223729) baseStart_6223729 baseEnd_6223729 := by
    simpa [prefixWord, tailWord_6223729, baseEnd_6223729] using wordTrace_append hprefix tailTrace_6223729
  have hstable : (prefixWord ++ tailWord_6223729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223729).length < 2 ^ (prefixWord ++ tailWord_6223729).sum := by decide
  have hdescent : baseEnd_6223729 < baseStart_6223729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223739 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5]
def baseStart_6223739 : Nat := 118140960795 + 6223739 * 2 ^ 59
def prefixEnd_6223739 : Nat := 4983230072969 + 3 ^ 40 * 6223739 * 2
def baseEnd_6223739 : Nat := 3195769575132930326240051

theorem tailTrace_6223739 : CollatzResearch.WordTrace tailWord_6223739 prefixEnd_6223739 3195769575132930326240051 := by
  unfold tailWord_6223739
  simp only [CollatzResearch.WordTrace]
  refine ⟨226998409999464007842130271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151332273332976005228086847 226998409999464007842130271)
  ·
    refine ⟨340497614999196011763195407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226998409999464007842130271 340497614999196011763195407)
    ·
      refine ⟨510746422498794017644793111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340497614999196011763195407 510746422498794017644793111)
      ·
        refine ⟨766119633748191026467189667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510746422498794017644793111 766119633748191026467189667)
        ·
          refine ⟨1149179450622286539700784501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766119633748191026467189667 1149179450622286539700784501)
          ·
            refine ⟨107735573495839363096948547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1149179450622286539700784501 107735573495839363096948547)
            ·
              refine ⟨161603360243759044645422821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107735573495839363096948547 161603360243759044645422821)
              ·
                refine ⟨30300630045704820871016779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161603360243759044645422821 30300630045704820871016779)
                ·
                  refine ⟨45450945068557231306525169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30300630045704820871016779 45450945068557231306525169)
                  ·
                    refine ⟨34088208801417923479893877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45450945068557231306525169 34088208801417923479893877)
                    ·
                      refine ⟨3195769575132930326240051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34088208801417923479893877 3195769575132930326240051)
                      ·
                        rfl

theorem cell23_6223739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_6223739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223739 prefixEnd_6223739 := by exact prefixLift 6223739
  have htrace : WordTrace (prefixWord ++ tailWord_6223739) baseStart_6223739 baseEnd_6223739 := by
    simpa [prefixWord, tailWord_6223739, baseEnd_6223739] using wordTrace_append hprefix tailTrace_6223739
  have hstable : (prefixWord ++ tailWord_6223739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223739).length < 2 ^ (prefixWord ++ tailWord_6223739).sum := by decide
  have hdescent : baseEnd_6223739 < baseStart_6223739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223776 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 5, 4]
def baseStart_6223776 : Nat := 118140960795 + 6223776 * 2 ^ 59
def prefixEnd_6223776 : Nat := 4983230072969 + 3 ^ 40 * 6223776 * 2
def baseEnd_6223776 : Nat := 1065262857972382227159127

theorem tailTrace_6223776 : CollatzResearch.WordTrace tailWord_6223776 prefixEnd_6223776 1065262857972382227159127 := by
  unfold tailWord_6223776
  simp only [CollatzResearch.WordTrace]
  refine ⟨113499879750164981580613591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151333173000219975440818121 113499879750164981580613591)
  ·
    refine ⟨170249819625247472370920387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113499879750164981580613591 170249819625247472370920387)
    ·
      refine ⟨255374729437871208556380581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170249819625247472370920387 255374729437871208556380581)
      ·
        refine ⟨47882761769600851604321359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255374729437871208556380581 47882761769600851604321359)
        ·
          refine ⟨71824142654401277406482039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47882761769600851604321359 71824142654401277406482039)
          ·
            refine ⟨107736213981601916109723059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71824142654401277406482039 107736213981601916109723059)
            ·
              refine ⟨161604320972402874164584589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107736213981601916109723059 161604320972402874164584589)
              ·
                refine ⟨60601620364651077811719221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161604320972402874164584589 60601620364651077811719221)
                ·
                  refine ⟨5681401909186038544848677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60601620364651077811719221 5681401909186038544848677)
                  ·
                    refine ⟨1065262857972382227159127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5681401909186038544848677 1065262857972382227159127)
                    ·
                      rfl

theorem cell23_6223776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_6223776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223776 prefixEnd_6223776 := by exact prefixLift 6223776
  have htrace : WordTrace (prefixWord ++ tailWord_6223776) baseStart_6223776 baseEnd_6223776 := by
    simpa [prefixWord, tailWord_6223776, baseEnd_6223776] using wordTrace_append hprefix tailTrace_6223776
  have hstable : (prefixWord ++ tailWord_6223776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223776).length < 2 ^ (prefixWord ++ tailWord_6223776).sum := by decide
  have hdescent : baseEnd_6223776 < baseStart_6223776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223779 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_6223779 : Nat := 118140960795 + 6223779 * 2 ^ 59
def prefixEnd_6223779 : Nat := 4983230072969 + 3 ^ 40 * 6223779 * 2
def baseEnd_6223779 : Nat := 3195790114359110169739867

theorem tailTrace_6223779 : CollatzResearch.WordTrace tailWord_6223779 prefixEnd_6223779 3195790114359110169739867 := by
  unfold tailWord_6223779
  simp only [CollatzResearch.WordTrace]
  refine ⟨226999868919319094673586391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151333245946212729782390927 226999868919319094673586391)
  ·
    refine ⟨340499803378978642010379587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226999868919319094673586391 340499803378978642010379587)
    ·
      refine ⟨510749705068467963015569381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340499803378978642010379587 510749705068467963015569381)
      ·
        refine ⟨95765569700337743065419259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 510749705068467963015569381 95765569700337743065419259)
        ·
          refine ⟨143648354550506614598128889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95765569700337743065419259 143648354550506614598128889)
          ·
            refine ⟨107736265912879960948596667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143648354550506614598128889 107736265912879960948596667)
            ·
              refine ⟨161604398869319941422895001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107736265912879960948596667 161604398869319941422895001)
              ·
                refine ⟨121203299151989956067171251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161604398869319941422895001 121203299151989956067171251)
                ·
                  refine ⟨181804948727984934100756877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121203299151989956067171251 181804948727984934100756877)
                  ·
                    refine ⟨68176855772994350287783829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181804948727984934100756877 68176855772994350287783829)
                    ·
                      refine ⟨3195790114359110169739867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68176855772994350287783829 3195790114359110169739867)
                      ·
                        rfl

theorem cell23_6223779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_6223779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223779 prefixEnd_6223779 := by exact prefixLift 6223779
  have htrace : WordTrace (prefixWord ++ tailWord_6223779) baseStart_6223779 baseEnd_6223779 := by
    simpa [prefixWord, tailWord_6223779, baseEnd_6223779] using wordTrace_append hprefix tailTrace_6223779
  have hstable : (prefixWord ++ tailWord_6223779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223779).length < 2 ^ (prefixWord ++ tailWord_6223779).sum := by decide
  have hdescent : baseEnd_6223779 < baseStart_6223779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223783 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_6223783 : Nat := 118140960795 + 6223783 * 2 ^ 59
def prefixEnd_6223783 : Nat := 4983230072969 + 3 ^ 40 * 6223783 * 2
def baseEnd_6223783 : Nat := 3195792168281728154089849

theorem tailTrace_6223783 : CollatzResearch.WordTrace tailWord_6223783 prefixEnd_6223783 3195792168281728154089849 := by
  unfold tailWord_6223783
  simp only [CollatzResearch.WordTrace]
  refine ⟨227000014811304603356732003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151333343207536402237821335 227000014811304603356732003)
  ·
    refine ⟨340500022216956905035098005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227000014811304603356732003 340500022216956905035098005)
    ·
      refine ⟨15960938541419854923520219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 340500022216956905035098005 15960938541419854923520219)
      ·
        refine ⟨23941407812129782385280329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15960938541419854923520219 23941407812129782385280329)
        ·
          refine ⟨17956055859097336788960247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23941407812129782385280329 17956055859097336788960247)
          ·
            refine ⟨26934083788646005183440371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17956055859097336788960247 26934083788646005183440371)
            ·
              refine ⟨40401125682969007775160557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26934083788646005183440371 40401125682969007775160557)
              ·
                refine ⟨15150422131113377915685209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40401125682969007775160557 15150422131113377915685209)
                ·
                  refine ⟨11362816598335033436763907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15150422131113377915685209 11362816598335033436763907)
                  ·
                    refine ⟨17044224897502550155145861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11362816598335033436763907 17044224897502550155145861)
                    ·
                      refine ⟨3195792168281728154089849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17044224897502550155145861 3195792168281728154089849)
                      ·
                        rfl

theorem cell23_6223783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_6223783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223783 prefixEnd_6223783 := by exact prefixLift 6223783
  have htrace : WordTrace (prefixWord ++ tailWord_6223783) baseStart_6223783 baseEnd_6223783 := by
    simpa [prefixWord, tailWord_6223783, baseEnd_6223783] using wordTrace_append hprefix tailTrace_6223783
  have hstable : (prefixWord ++ tailWord_6223783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223783).length < 2 ^ (prefixWord ++ tailWord_6223783).sum := by decide
  have hdescent : baseEnd_6223783 < baseStart_6223783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223837 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_6223837 : Nat := 118140960795 + 6223837 * 2 ^ 59
def prefixEnd_6223837 : Nat := 4983230072969 + 3 ^ 40 * 6223837 * 2
def baseEnd_6223837 : Nat := 3195819896237070942814601

theorem tailTrace_6223837 : CollatzResearch.WordTrace tailWord_6223837 prefixEnd_6223837 3195819896237070942814601 := by
  unfold tailWord_6223837
  simp only [CollatzResearch.WordTrace]
  refine ⟨227001984353108970579197765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151334656235405980386131843 227001984353108970579197765)
  ·
    refine ⟨42562872066207931983599581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227001984353108970579197765 42562872066207931983599581)
    ·
      refine ⟨15961077024827974493849843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42562872066207931983599581 15961077024827974493849843)
      ·
        refine ⟨23941615537241961740774765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15961077024827974493849843 23941615537241961740774765)
        ·
          refine ⟨8978105826465735652790537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23941615537241961740774765 8978105826465735652790537)
          ·
            refine ⟨6733579369849301739592903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8978105826465735652790537 6733579369849301739592903)
            ·
              refine ⟨10100369054773952609389355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733579369849301739592903 10100369054773952609389355)
              ·
                refine ⟨15150553582160928914084033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10100369054773952609389355 15150553582160928914084033)
                ·
                  refine ⟨11362915186620696685563025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15150553582160928914084033 11362915186620696685563025)
                  ·
                    refine ⟨8522186389965522514172269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11362915186620696685563025 8522186389965522514172269)
                    ·
                      refine ⟨3195819896237070942814601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8522186389965522514172269 3195819896237070942814601)
                      ·
                        rfl

theorem cell23_6223837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_6223837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223837 prefixEnd_6223837 := by exact prefixLift 6223837
  have htrace : WordTrace (prefixWord ++ tailWord_6223837) baseStart_6223837 baseEnd_6223837 := by
    simpa [prefixWord, tailWord_6223837, baseEnd_6223837] using wordTrace_append hprefix tailTrace_6223837
  have hstable : (prefixWord ++ tailWord_6223837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223837).length < 2 ^ (prefixWord ++ tailWord_6223837).sum := by decide
  have hdescent : baseEnd_6223837 < baseStart_6223837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223896 : List Nat := [2, 1, 2, 3, 2, 1, 3, 9]
def baseStart_6223896 : Nat := 118140960795 + 6223896 * 2 ^ 59
def prefixEnd_6223896 : Nat := 4983230072969 + 3 ^ 40 * 6223896 * 2
def baseEnd_6223896 : Nat := 118364821910951341184327

theorem tailTrace_6223896 : CollatzResearch.WordTrace tailWord_6223896 prefixEnd_6223896 118364821910951341184327 := by
  unfold tailWord_6223896
  simp only [CollatzResearch.WordTrace]
  refine ⟨113502068129947611827797771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151336090839930149103730361 113502068129947611827797771)
  ·
    refine ⟨170253102194921417741696657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113502068129947611827797771 170253102194921417741696657)
    ·
      refine ⟨127689826646191063306272493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170253102194921417741696657 127689826646191063306272493)
      ·
        refine ⟨47883684992321648739852185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127689826646191063306272493 47883684992321648739852185)
        ·
          refine ⟨35912763744241236554889139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47883684992321648739852185 35912763744241236554889139)
          ·
            refine ⟨53869145616361854832333709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35912763744241236554889139 53869145616361854832333709)
            ·
              refine ⟨20200929606135695562125141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53869145616361854832333709 20200929606135695562125141)
              ·
                refine ⟨118364821910951341184327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20200929606135695562125141 118364821910951341184327)
                ·
                  rfl

theorem cell23_6223896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 9].length) (baseStart_6223896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223896 prefixEnd_6223896 := by exact prefixLift 6223896
  have htrace : WordTrace (prefixWord ++ tailWord_6223896) baseStart_6223896 baseEnd_6223896 := by
    simpa [prefixWord, tailWord_6223896, baseEnd_6223896] using wordTrace_append hprefix tailTrace_6223896
  have hstable : (prefixWord ++ tailWord_6223896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223896).length < 2 ^ (prefixWord ++ tailWord_6223896).sum := by decide
  have hdescent : baseEnd_6223896 < baseStart_6223896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223946 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_6223946 : Nat := 118140960795 + 6223946 * 2 ^ 59
def prefixEnd_6223946 : Nat := 4983230072969 + 3 ^ 40 * 6223946 * 2
def baseEnd_6223946 : Nat := 3195875865628411016351599

theorem tailTrace_6223946 : CollatzResearch.WordTrace tailWord_6223946 prefixEnd_6223946 3195875865628411016351599 := by
  unfold tailWord_6223946
  simp only [CollatzResearch.WordTrace]
  refine ⟨56751489977428520548728923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151337306606476054796610461 56751489977428520548728923)
  ·
    refine ⟨85127234966142780823093385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56751489977428520548728923 85127234966142780823093385)
    ·
      refine ⟨63845426224607085617320039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85127234966142780823093385 63845426224607085617320039)
      ·
        refine ⟨95768139336910628425980059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63845426224607085617320039 95768139336910628425980059)
        ·
          refine ⟨143652209005365942638970089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95768139336910628425980059 143652209005365942638970089)
          ·
            refine ⟨107739156754024456979227567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143652209005365942638970089 107739156754024456979227567)
            ·
              refine ⟨161608735131036685468841351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107739156754024456979227567 161608735131036685468841351)
              ·
                refine ⟨242413102696555028203262027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161608735131036685468841351 242413102696555028203262027)
                ·
                  refine ⟨363619654044832542304893041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242413102696555028203262027 363619654044832542304893041)
                  ·
                    refine ⟨272714740533624406728669781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 363619654044832542304893041 272714740533624406728669781)
                    ·
                      refine ⟨3195875865628411016351599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 272714740533624406728669781 3195875865628411016351599)
                      ·
                        rfl

theorem cell23_6223946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_6223946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223946 prefixEnd_6223946 := by exact prefixLift 6223946
  have htrace : WordTrace (prefixWord ++ tailWord_6223946) baseStart_6223946 baseEnd_6223946 := by
    simpa [prefixWord, tailWord_6223946, baseEnd_6223946] using wordTrace_append hprefix tailTrace_6223946
  have hstable : (prefixWord ++ tailWord_6223946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223946).length < 2 ^ (prefixWord ++ tailWord_6223946).sum := by decide
  have hdescent : baseEnd_6223946 < baseStart_6223946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223983 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_6223983 : Nat := 118140960795 + 6223983 * 2 ^ 59
def prefixEnd_6223983 : Nat := 4983230072969 + 3 ^ 40 * 6223983 * 2
def baseEnd_6223983 : Nat := 3195894864412627371588929

theorem tailTrace_6223983 : CollatzResearch.WordTrace tailWord_6223983 prefixEnd_6223983 3195894864412627371588929 := by
  unfold tailWord_6223983
  simp only [CollatzResearch.WordTrace]
  refine ⟨227007309410580037514012603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151338206273720025009341735 227007309410580037514012603)
  ·
    refine ⟨340510964115870056271018905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227007309410580037514012603 340510964115870056271018905)
    ·
      refine ⟨255383223086902542203264179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340510964115870056271018905 255383223086902542203264179)
      ·
        refine ⟨383074834630353813304896269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255383223086902542203264179 383074834630353813304896269)
        ·
          refine ⟨143653062986382679989336101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383074834630353813304896269 143653062986382679989336101)
          ·
            refine ⟨26934949309946752498000519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143653062986382679989336101 26934949309946752498000519)
            ·
              refine ⟨40402423964920128747000779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26934949309946752498000519 40402423964920128747000779)
              ·
                refine ⟨60603635947380193120501169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40402423964920128747000779 60603635947380193120501169)
                ·
                  refine ⟨45452726960535144840375877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60603635947380193120501169 45452726960535144840375877)
                  ·
                    refine ⟨8522386305100339657570477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45452726960535144840375877 8522386305100339657570477)
                    ·
                      refine ⟨3195894864412627371588929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8522386305100339657570477 3195894864412627371588929)
                      ·
                        rfl

theorem cell23_6223983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_6223983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223983 prefixEnd_6223983 := by exact prefixLift 6223983
  have htrace : WordTrace (prefixWord ++ tailWord_6223983) baseStart_6223983 baseEnd_6223983 := by
    simpa [prefixWord, tailWord_6223983, baseEnd_6223983] using wordTrace_append hprefix tailTrace_6223983
  have hstable : (prefixWord ++ tailWord_6223983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223983).length < 2 ^ (prefixWord ++ tailWord_6223983).sum := by decide
  have hdescent : baseEnd_6223983 < baseStart_6223983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223990 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_6223990 : Nat := 118140960795 + 6223990 * 2 ^ 59
def prefixEnd_6223990 : Nat := 4983230072969 + 3 ^ 40 * 6223990 * 2
def baseEnd_6223990 : Nat := 1065299486259069614733799

theorem tailTrace_6223990 : CollatzResearch.WordTrace tailWord_6223990 prefixEnd_6223990 1065299486259069614733799 := by
  unfold tailWord_6223990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187972795097167356844839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151338376481036451806344949 14187972795097167356844839)
  ·
    refine ⟨21281959192645751035267259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14187972795097167356844839 21281959192645751035267259)
    ·
      refine ⟨31922938788968626552900889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21281959192645751035267259 31922938788968626552900889)
      ·
        refine ⟨23942204091726469914675667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31922938788968626552900889 23942204091726469914675667)
        ·
          refine ⟨35913306137589704872013501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23942204091726469914675667 35913306137589704872013501)
          ·
            refine ⟨13467489801596139327005063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35913306137589704872013501 13467489801596139327005063)
            ·
              refine ⟨20201234702394208990507595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13467489801596139327005063 20201234702394208990507595)
              ·
                refine ⟨30301852053591313485761393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20201234702394208990507595 30301852053591313485761393)
                ·
                  refine ⟨22726389040193485114321045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30301852053591313485761393 22726389040193485114321045)
                  ·
                    refine ⟨1065299486259069614733799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22726389040193485114321045 1065299486259069614733799)
                    ·
                      rfl

theorem cell23_6223990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_6223990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223990 prefixEnd_6223990 := by exact prefixLift 6223990
  have htrace : WordTrace (prefixWord ++ tailWord_6223990) baseStart_6223990 baseEnd_6223990 := by
    simpa [prefixWord, tailWord_6223990, baseEnd_6223990] using wordTrace_append hprefix tailTrace_6223990
  have hstable : (prefixWord ++ tailWord_6223990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223990).length < 2 ^ (prefixWord ++ tailWord_6223990).sum := by decide
  have hdescent : baseEnd_6223990 < baseStart_6223990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223993 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6223993 : Nat := 118140960795 + 6223993 * 2 ^ 59
def prefixEnd_6223993 : Nat := 4983230072969 + 3 ^ 40 * 6223993 * 2
def baseEnd_6223993 : Nat := 3195899999219172332463883

theorem tailTrace_6223993 : CollatzResearch.WordTrace tailWord_6223993 prefixEnd_6223993 3195899999219172332463883 := by
  unfold tailWord_6223993
  simp only [CollatzResearch.WordTrace]
  refine ⟨227007674140543809221876633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151338449427029206147917755 227007674140543809221876633)
  ·
    refine ⟨170255755605407856916407475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227007674140543809221876633 170255755605407856916407475)
    ·
      refine ⟨255383633408111785374611213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170255755605407856916407475 255383633408111785374611213)
      ·
        refine ⟨95768862528041919515479205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255383633408111785374611213 95768862528041919515479205)
        ·
          refine ⟨17956661724007859909152351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95768862528041919515479205 17956661724007859909152351)
          ·
            refine ⟨26934992586011789863728527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17956661724007859909152351 26934992586011789863728527)
            ·
              refine ⟨40402488879017684795592791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26934992586011789863728527 40402488879017684795592791)
              ·
                refine ⟨60603733318526527193389187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40402488879017684795592791 60603733318526527193389187)
                ·
                  refine ⟨90905599977789790790083781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60603733318526527193389187 90905599977789790790083781)
                  ·
                    refine ⟨17044799995835585773140709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90905599977789790790083781 17044799995835585773140709)
                    ·
                      refine ⟨3195899999219172332463883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17044799995835585773140709 3195899999219172332463883)
                      ·
                        rfl

theorem cell23_6223993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6223993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223993 prefixEnd_6223993 := by exact prefixLift 6223993
  have htrace : WordTrace (prefixWord ++ tailWord_6223993) baseStart_6223993 baseEnd_6223993 := by
    simpa [prefixWord, tailWord_6223993, baseEnd_6223993] using wordTrace_append hprefix tailTrace_6223993
  have hstable : (prefixWord ++ tailWord_6223993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223993).length < 2 ^ (prefixWord ++ tailWord_6223993).sum := by decide
  have hdescent : baseEnd_6223993 < baseStart_6223993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6223997 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_6223997 : Nat := 118140960795 + 6223997 * 2 ^ 59
def prefixEnd_6223997 : Nat := 4983230072969 + 3 ^ 40 * 6223997 * 2
def baseEnd_6223997 : Nat := 3195902053141790316813865

theorem tailTrace_6223997 : CollatzResearch.WordTrace tailWord_6223997 prefixEnd_6223997 3195902053141790316813865 := by
  unfold tailWord_6223997
  simp only [CollatzResearch.WordTrace]
  refine ⟨227007820032529317905022245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151338546688352878603348163 227007820032529317905022245)
  ·
    refine ⟨42563966256099247107191671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227007820032529317905022245 42563966256099247107191671)
    ·
      refine ⟨63845949384148870660787507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42563966256099247107191671 63845949384148870660787507)
      ·
        refine ⟨95768924076223305991181261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63845949384148870660787507 95768924076223305991181261)
        ·
          refine ⟨35913346528583739746692973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95768924076223305991181261 35913346528583739746692973)
          ·
            refine ⟨13467504948218902405009865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35913346528583739746692973 13467504948218902405009865)
            ·
              refine ⟨10100628711164176803757399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13467504948218902405009865 10100628711164176803757399)
              ·
                refine ⟨15150943066746265205636099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10100628711164176803757399 15150943066746265205636099)
                ·
                  refine ⟨22726414600119397808454149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15150943066746265205636099 22726414600119397808454149)
                  ·
                    refine ⟨4261202737522387089085153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22726414600119397808454149 4261202737522387089085153)
                    ·
                      refine ⟨3195902053141790316813865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261202737522387089085153 3195902053141790316813865)
                      ·
                        rfl

theorem cell23_6223997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_6223997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6223997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6223997 prefixEnd_6223997 := by exact prefixLift 6223997
  have htrace : WordTrace (prefixWord ++ tailWord_6223997) baseStart_6223997 baseEnd_6223997 := by
    simpa [prefixWord, tailWord_6223997, baseEnd_6223997] using wordTrace_append hprefix tailTrace_6223997
  have hstable : (prefixWord ++ tailWord_6223997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6223997).length < 2 ^ (prefixWord ++ tailWord_6223997).sum := by decide
  have hdescent : baseEnd_6223997 < baseStart_6223997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6223997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224003 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 7]
def baseStart_6224003 : Nat := 118140960795 + 6224003 * 2 ^ 59
def prefixEnd_6224003 : Nat := 4983230072969 + 3 ^ 40 * 6224003 * 2
def baseEnd_6224003 : Nat := 355100570447301921482093

theorem tailTrace_6224003 : CollatzResearch.WordTrace tailWord_6224003 prefixEnd_6224003 355100570447301921482093 := by
  unfold tailWord_6224003
  simp only [CollatzResearch.WordTrace]
  refine ⟨227008038870507580929740663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151338692580338387286493775 227008038870507580929740663)
  ·
    refine ⟨340512058305761371394610995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227008038870507580929740663 340512058305761371394610995)
    ·
      refine ⟨510768087458642057091916493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340512058305761371394610995 510768087458642057091916493)
      ·
        refine ⟨191538032796990771409468685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510768087458642057091916493 191538032796990771409468685)
        ·
          refine ⟨71826762298871539278550757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191538032796990771409468685 71826762298871539278550757)
          ·
            refine ⟨13467517931038413614728267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71826762298871539278550757 13467517931038413614728267)
            ·
              refine ⟨20201276896557620422092401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13467517931038413614728267 20201276896557620422092401)
              ·
                refine ⟨15150957672418215316569301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20201276896557620422092401 15150957672418215316569301)
                ·
                  refine ⟨355100570447301921482093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15150957672418215316569301 355100570447301921482093)
                  ·
                    rfl

theorem cell23_6224003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 7].length) (baseStart_6224003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224003 prefixEnd_6224003 := by exact prefixLift 6224003
  have htrace : WordTrace (prefixWord ++ tailWord_6224003) baseStart_6224003 baseEnd_6224003 := by
    simpa [prefixWord, tailWord_6224003, baseEnd_6224003] using wordTrace_append hprefix tailTrace_6224003
  have hstable : (prefixWord ++ tailWord_6224003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224003).length < 2 ^ (prefixWord ++ tailWord_6224003).sum := by decide
  have hdescent : baseEnd_6224003 < baseStart_6224003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224031 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6224031 : Nat := 118140960795 + 6224031 * 2 ^ 59
def prefixEnd_6224031 : Nat := 4983230072969 + 3 ^ 40 * 6224031 * 2
def baseEnd_6224031 : Nat := 3195919511484043183788709

theorem tailTrace_6224031 : CollatzResearch.WordTrace tailWord_6224031 prefixEnd_6224031 3195919511484043183788709 := by
  unfold tailWord_6224031
  simp only [CollatzResearch.WordTrace]
  refine ⟨227009060114406141711759947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151339373409604094474506631 227009060114406141711759947)
  ·
    refine ⟨340513590171609212567639921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227009060114406141711759947 340513590171609212567639921)
    ·
      refine ⟨255385192628706909425729941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340513590171609212567639921 255385192628706909425729941)
      ·
        refine ⟨11971180904470636379331091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255385192628706909425729941 11971180904470636379331091)
        ·
          refine ⟨17956771356705954568996637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11971180904470636379331091 17956771356705954568996637)
          ·
            refine ⟨6733789258764732963373739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17956771356705954568996637 6733789258764732963373739)
            ·
              refine ⟨10100683888147099445060609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733789258764732963373739 10100683888147099445060609)
              ·
                refine ⟨7575512916110324583795457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10100683888147099445060609 7575512916110324583795457)
                ·
                  refine ⟨5681634687082743437846593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7575512916110324583795457 5681634687082743437846593)
                  ·
                    refine ⟨4261226015312057578384945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681634687082743437846593 4261226015312057578384945)
                    ·
                      refine ⟨3195919511484043183788709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261226015312057578384945 3195919511484043183788709)
                      ·
                        rfl

theorem cell23_6224031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6224031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224031 prefixEnd_6224031 := by exact prefixLift 6224031
  have htrace : WordTrace (prefixWord ++ tailWord_6224031) baseStart_6224031 baseEnd_6224031 := by
    simpa [prefixWord, tailWord_6224031, baseEnd_6224031] using wordTrace_append hprefix tailTrace_6224031
  have hstable : (prefixWord ++ tailWord_6224031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224031).length < 2 ^ (prefixWord ++ tailWord_6224031).sum := by decide
  have hdescent : baseEnd_6224031 < baseStart_6224031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224090 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_6224090 : Nat := 118140960795 + 6224090 * 2 ^ 59
def prefixEnd_6224090 : Nat := 4983230072969 + 3 ^ 40 * 6224090 * 2
def baseEnd_6224090 : Nat := 3195949806842658452950937

theorem tailTrace_6224090 : CollatzResearch.WordTrace tailWord_6224090 prefixEnd_6224090 3195949806842658452950937 := by
  unfold tailWord_6224090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56752803005298098697039431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151340808014128263192105149 56752803005298098697039431)
  ·
    refine ⟨85129204507947148045559147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56752803005298098697039431 85129204507947148045559147)
    ·
      refine ⟨127693806761920722068338721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85129204507947148045559147 127693806761920722068338721)
      ·
        refine ⟨95770355071440541551254041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127693806761920722068338721 95770355071440541551254041)
        ·
          refine ⟨71827766303580406163440531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95770355071440541551254041 71827766303580406163440531)
          ·
            refine ⟨107741649455370609245160797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71827766303580406163440531 107741649455370609245160797)
            ·
              refine ⟨40403118545763978466935299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107741649455370609245160797 40403118545763978466935299)
              ·
                refine ⟨60604677818645967700402949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40403118545763978466935299 60604677818645967700402949)
                ·
                  refine ⟨11363377090996118943825553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60604677818645967700402949 11363377090996118943825553)
                  ·
                    refine ⟨8522532818247089207869165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11363377090996118943825553 8522532818247089207869165)
                    ·
                      refine ⟨3195949806842658452950937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8522532818247089207869165 3195949806842658452950937)
                      ·
                        rfl

theorem cell23_6224090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_6224090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224090 prefixEnd_6224090 := by exact prefixLift 6224090
  have htrace : WordTrace (prefixWord ++ tailWord_6224090) baseStart_6224090 baseEnd_6224090 := by
    simpa [prefixWord, tailWord_6224090, baseEnd_6224090] using wordTrace_append hprefix tailTrace_6224090
  have hstable : (prefixWord ++ tailWord_6224090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224090).length < 2 ^ (prefixWord ++ tailWord_6224090).sum := by decide
  have hdescent : baseEnd_6224090 < baseStart_6224090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224113 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_6224113 : Nat := 118140960795 + 6224113 * 2 ^ 59
def prefixEnd_6224113 : Nat := 4983230072969 + 3 ^ 40 * 6224113 * 2
def baseEnd_6224113 : Nat := 3195961616897711862963331

theorem tailTrace_6224113 : CollatzResearch.WordTrace tailWord_6224113 prefixEnd_6224113 3195961616897711862963331 := by
  unfold tailWord_6224113
  simp only [CollatzResearch.WordTrace]
  refine ⟨227012050900109069716244993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151341367266739379810829995 227012050900109069716244993)
  ·
    refine ⟨170259038175081802287183745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227012050900109069716244993 170259038175081802287183745)
    ·
      refine ⟨127694278631311351715387809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170259038175081802287183745 127694278631311351715387809)
      ·
        refine ⟨95770708973483513786540857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127694278631311351715387809 95770708973483513786540857)
        ·
          refine ⟨71828031730112635339905643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95770708973483513786540857 71828031730112635339905643)
          ·
            refine ⟨107742047595168953009858465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71828031730112635339905643 107742047595168953009858465)
            ·
              refine ⟨80806535696376714757393849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107742047595168953009858465 80806535696376714757393849)
              ·
                refine ⟨60604901772282536068045387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80806535696376714757393849 60604901772282536068045387)
                ·
                  refine ⟨90907352658423804102068081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60604901772282536068045387 90907352658423804102068081)
                  ·
                    refine ⟨68180514493817853076551061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90907352658423804102068081 68180514493817853076551061)
                    ·
                      refine ⟨3195961616897711862963331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68180514493817853076551061 3195961616897711862963331)
                      ·
                        rfl

theorem cell23_6224113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_6224113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224113 prefixEnd_6224113 := by exact prefixLift 6224113
  have htrace : WordTrace (prefixWord ++ tailWord_6224113) baseStart_6224113 baseEnd_6224113 := by
    simpa [prefixWord, tailWord_6224113, baseEnd_6224113] using wordTrace_append hprefix tailTrace_6224113
  have hstable : (prefixWord ++ tailWord_6224113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224113).length < 2 ^ (prefixWord ++ tailWord_6224113).sum := by decide
  have hdescent : baseEnd_6224113 < baseStart_6224113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224133 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_6224133 : Nat := 118140960795 + 6224133 * 2 ^ 59
def prefixEnd_6224133 : Nat := 4983230072969 + 3 ^ 40 * 6224133 * 2
def baseEnd_6224133 : Nat := 3195971886510801784713239

theorem tailTrace_6224133 : CollatzResearch.WordTrace tailWord_6224133 prefixEnd_6224133 3195971886510801784713239 := by
  unfold tailWord_6224133
  simp only [CollatzResearch.WordTrace]
  refine ⟨227012780360036613131973053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151341853573357742087982035 227012780360036613131973053)
  ·
    refine ⟨85129792635013729924489895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227012780360036613131973053 85129792635013729924489895)
    ·
      refine ⟨127694688952520594886734843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85129792635013729924489895 127694688952520594886734843)
      ·
        refine ⟨191542033428780892330102265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127694688952520594886734843 191542033428780892330102265)
        ·
          refine ⟨143656525071585669247576699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191542033428780892330102265 143656525071585669247576699)
          ·
            refine ⟨215484787607378503871365049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143656525071585669247576699 215484787607378503871365049)
            ·
              refine ⟨161613590705533877903523787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215484787607378503871365049 161613590705533877903523787)
              ·
                refine ⟨242420386058300816855285681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161613590705533877903523787 242420386058300816855285681)
                ·
                  refine ⟨181815289543725612641464261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242420386058300816855285681 181815289543725612641464261)
                  ·
                    refine ⟨34090366789448552370274549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181815289543725612641464261 34090366789448552370274549)
                    ·
                      refine ⟨3195971886510801784713239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34090366789448552370274549 3195971886510801784713239)
                      ·
                        rfl

theorem cell23_6224133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_6224133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224133 prefixEnd_6224133 := by exact prefixLift 6224133
  have htrace : WordTrace (prefixWord ++ tailWord_6224133) baseStart_6224133 baseEnd_6224133 := by
    simpa [prefixWord, tailWord_6224133, baseEnd_6224133] using wordTrace_append hprefix tailTrace_6224133
  have hstable : (prefixWord ++ tailWord_6224133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224133).length < 2 ^ (prefixWord ++ tailWord_6224133).sum := by decide
  have hdescent : baseEnd_6224133 < baseStart_6224133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224183 : List Nat := [1, 1, 3, 1, 2, 1, 1, 13]
def baseStart_6224183 : Nat := 118140960795 + 6224183 * 2 ^ 59
def prefixEnd_6224183 : Nat := 4983230072969 + 3 ^ 40 * 6224183 * 2
def baseEnd_6224183 : Nat := 118370280020130614410667

theorem tailTrace_6224183 : CollatzResearch.WordTrace tailWord_6224183 prefixEnd_6224183 118370280020130614410667 := by
  unfold tailWord_6224183
  simp only [CollatzResearch.WordTrace]
  refine ⟨227014604009855471671293203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151343069339903647780862135 227014604009855471671293203)
  ·
    refine ⟨340521906014783207506939805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227014604009855471671293203 340521906014783207506939805)
    ·
      refine ⟨127695714755543702815102427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340521906014783207506939805 127695714755543702815102427)
      ·
        refine ⟨191543572133315554222653641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127695714755543702815102427 191543572133315554222653641)
        ·
          refine ⟨143657679099986665666990231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191543572133315554222653641 143657679099986665666990231)
          ·
            refine ⟨215486518649979998500485347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143657679099986665666990231 215486518649979998500485347)
            ·
              refine ⟨323229777974969997750728021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215486518649979998500485347 323229777974969997750728021)
              ·
                refine ⟨118370280020130614410667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 323229777974969997750728021 118370280020130614410667)
                ·
                  rfl

theorem cell23_6224183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 13].length) (baseStart_6224183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224183 prefixEnd_6224183 := by exact prefixLift 6224183
  have htrace : WordTrace (prefixWord ++ tailWord_6224183) baseStart_6224183 baseEnd_6224183 := by
    simpa [prefixWord, tailWord_6224183, baseEnd_6224183] using wordTrace_append hprefix tailTrace_6224183
  have hstable : (prefixWord ++ tailWord_6224183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224183).length < 2 ^ (prefixWord ++ tailWord_6224183).sum := by decide
  have hdescent : baseEnd_6224183 < baseStart_6224183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224224 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4]
def baseStart_6224224 : Nat := 118140960795 + 6224224 * 2 ^ 59
def prefixEnd_6224224 : Nat := 4983230072969 + 3 ^ 40 * 6224224 * 2
def baseEnd_6224224 : Nat := 3196018613250360928675321

theorem tailTrace_6224224 : CollatzResearch.WordTrace tailWord_6224224 prefixEnd_6224224 3196018613250360928675321 := by
  unfold tailWord_6224224
  simp only [CollatzResearch.WordTrace]
  refine ⟨113508049701353467836767863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151344066268471290449023817 113508049701353467836767863)
  ·
    refine ⟨170262074552030201755151795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113508049701353467836767863 170262074552030201755151795)
    ·
      refine ⟨255393111828045302632727693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170262074552030201755151795 255393111828045302632727693)
      ·
        refine ⟨95772416935516988487272885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255393111828045302632727693 95772416935516988487272885)
        ·
          refine ⟨8978664087704717670681833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95772416935516988487272885 8978664087704717670681833)
          ·
            refine ⟨6733998065778538253011375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8978664087704717670681833 6733998065778538253011375)
            ·
              refine ⟨10100997098667807379517063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733998065778538253011375 10100997098667807379517063)
              ·
                refine ⟨15151495648001711069275595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10100997098667807379517063 15151495648001711069275595)
                ·
                  refine ⟨22727243472002566603913393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15151495648001711069275595 22727243472002566603913393)
                  ·
                    refine ⟨17045432604001924952935045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22727243472002566603913393 17045432604001924952935045)
                    ·
                      refine ⟨3196018613250360928675321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17045432604001924952935045 3196018613250360928675321)
                      ·
                        rfl

theorem cell23_6224224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_6224224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224224 prefixEnd_6224224 := by exact prefixLift 6224224
  have htrace : WordTrace (prefixWord ++ tailWord_6224224) baseStart_6224224 baseEnd_6224224 := by
    simpa [prefixWord, tailWord_6224224, baseEnd_6224224] using wordTrace_append hprefix tailTrace_6224224
  have hstable : (prefixWord ++ tailWord_6224224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224224).length < 2 ^ (prefixWord ++ tailWord_6224224).sum := by decide
  have hdescent : baseEnd_6224224 < baseStart_6224224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224234 : List Nat := [3, 1, 3, 3, 1, 3, 2, 7]
def baseStart_6224234 : Nat := 118140960795 + 6224234 * 2 ^ 59
def prefixEnd_6224234 : Nat := 4983230072969 + 3 ^ 40 * 6224234 * 2
def baseEnd_6224234 : Nat := 118371249928033551464825

theorem tailTrace_6224234 : CollatzResearch.WordTrace tailWord_6224234 prefixEnd_6224234 118371249928033551464825 := by
  unfold tailWord_6224234
  simp only [CollatzResearch.WordTrace]
  refine ⟨56754116033167676845349939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151344309421780471587599837 56754116033167676845349939)
  ·
    refine ⟨85131174049751515268024909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56754116033167676845349939 85131174049751515268024909)
    ·
      refine ⟨31924190268656818225509341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85131174049751515268024909 31924190268656818225509341)
      ·
        refine ⟨11971571350746306834566003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31924190268656818225509341 11971571350746306834566003)
        ·
          refine ⟨17957357026119460251849005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11971571350746306834566003 17957357026119460251849005)
          ·
            refine ⟨6734008884794797594443377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17957357026119460251849005 6734008884794797594443377)
            ·
              refine ⟨5050506663596098195832533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6734008884794797594443377 5050506663596098195832533)
              ·
                refine ⟨118371249928033551464825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5050506663596098195832533 118371249928033551464825)
                ·
                  rfl

theorem cell23_6224234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_6224234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224234 prefixEnd_6224234 := by exact prefixLift 6224234
  have htrace : WordTrace (prefixWord ++ tailWord_6224234) baseStart_6224234 baseEnd_6224234 := by
    simpa [prefixWord, tailWord_6224234, baseEnd_6224234] using wordTrace_append hprefix tailTrace_6224234
  have hstable : (prefixWord ++ tailWord_6224234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224234).length < 2 ^ (prefixWord ++ tailWord_6224234).sum := by decide
  have hdescent : baseEnd_6224234 < baseStart_6224234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224240 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_6224240 : Nat := 118140960795 + 6224240 * 2 ^ 59
def prefixEnd_6224240 : Nat := 4983230072969 + 3 ^ 40 * 6224240 * 2
def baseEnd_6224240 : Nat := 3196026828940832866075247

theorem tailTrace_6224240 : CollatzResearch.WordTrace tailWord_6224240 prefixEnd_6224240 3196026828940832866075247 := by
  unfold tailWord_6224240
  simp only [CollatzResearch.WordTrace]
  refine ⟨113508341485324485203059087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151344455313765980270745449 113508341485324485203059087)
  ·
    refine ⟨170262512227986727804588631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113508341485324485203059087 170262512227986727804588631)
    ·
      refine ⟨255393768341980091706882947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170262512227986727804588631 255393768341980091706882947)
      ·
        refine ⟨383090652512970137560324421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255393768341980091706882947 383090652512970137560324421)
        ·
          refine ⟨71829497346181900792560829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 383090652512970137560324421 71829497346181900792560829)
          ·
            refine ⟨26936061504818212797210311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71829497346181900792560829 26936061504818212797210311)
            ·
              refine ⟨40404092257227319195815467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26936061504818212797210311 40404092257227319195815467)
              ·
                refine ⟨60606138385840978793723201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40404092257227319195815467 60606138385840978793723201)
                ·
                  refine ⟨45454603789380734095292401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60606138385840978793723201 45454603789380734095292401)
                  ·
                    refine ⟨34090952842035550571469301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45454603789380734095292401 34090952842035550571469301)
                    ·
                      refine ⟨3196026828940832866075247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34090952842035550571469301 3196026828940832866075247)
                      ·
                        rfl

theorem cell23_6224240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_6224240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224240 prefixEnd_6224240 := by exact prefixLift 6224240
  have htrace : WordTrace (prefixWord ++ tailWord_6224240) baseStart_6224240 baseEnd_6224240 := by
    simpa [prefixWord, tailWord_6224240, baseEnd_6224240] using wordTrace_append hprefix tailTrace_6224240
  have hstable : (prefixWord ++ tailWord_6224240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224240).length < 2 ^ (prefixWord ++ tailWord_6224240).sum := by decide
  have hdescent : baseEnd_6224240 < baseStart_6224240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224245 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6224245 : Nat := 118140960795 + 6224245 * 2 ^ 59
def prefixEnd_6224245 : Nat := 4983230072969 + 3 ^ 40 * 6224245 * 2
def baseEnd_6224245 : Nat := 3196029396344105346512725

theorem tailTrace_6224245 : CollatzResearch.WordTrace tailWord_6224245 prefixEnd_6224245 3196029396344105346512725 := by
  unfold tailWord_6224245
  simp only [CollatzResearch.WordTrace]
  refine ⟨227016865335630856260050189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151344576890420570840033459 227016865335630856260050189)
  ·
    refine ⟨85131324500861571097518821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227016865335630856260050189 85131324500861571097518821)
    ·
      refine ⟨15962123343911544580784779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85131324500861571097518821 15962123343911544580784779)
      ·
        refine ⟨23943185015867316871177169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15962123343911544580784779 23943185015867316871177169)
        ·
          refine ⟨17957388761900487653382877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23943185015867316871177169 17957388761900487653382877)
          ·
            refine ⟨6734020785712682870018579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17957388761900487653382877 6734020785712682870018579)
            ·
              refine ⟨10101031178569024305027869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6734020785712682870018579 10101031178569024305027869)
              ·
                refine ⟨3787886691963384114385451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10101031178569024305027869 3787886691963384114385451)
                ·
                  refine ⟨5681830037945076171578177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787886691963384114385451 5681830037945076171578177)
                  ·
                    refine ⟨4261372528458807128683633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681830037945076171578177 4261372528458807128683633)
                    ·
                      refine ⟨3196029396344105346512725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261372528458807128683633 3196029396344105346512725)
                      ·
                        rfl

theorem cell23_6224245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6224245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224245 prefixEnd_6224245 := by exact prefixLift 6224245
  have htrace : WordTrace (prefixWord ++ tailWord_6224245) baseStart_6224245 baseEnd_6224245 := by
    simpa [prefixWord, tailWord_6224245, baseEnd_6224245] using wordTrace_append hprefix tailTrace_6224245
  have hstable : (prefixWord ++ tailWord_6224245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224245).length < 2 ^ (prefixWord ++ tailWord_6224245).sum := by decide
  have hdescent : baseEnd_6224245 < baseStart_6224245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224320 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_6224320 : Nat := 118140960795 + 6224320 * 2 ^ 59
def prefixEnd_6224320 : Nat := 4983230072969 + 3 ^ 40 * 6224320 * 2
def baseEnd_6224320 : Nat := 1065355969131064184358293

theorem tailTrace_6224320 : CollatzResearch.WordTrace tailWord_6224320 prefixEnd_6224320 1065355969131064184358293 := by
  unfold tailWord_6224320
  simp only [CollatzResearch.WordTrace]
  refine ⟨113509800405179572034515207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151346400540239429379353609 113509800405179572034515207)
  ·
    refine ⟨170264700607769358051772811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113509800405179572034515207 170264700607769358051772811)
    ·
      refine ⟨255397050911654037077659217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170264700607769358051772811 255397050911654037077659217)
      ·
        refine ⟨191547788183740527808244413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255397050911654037077659217 191547788183740527808244413)
        ·
          refine ⟨71830420568902697928091655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191547788183740527808244413 71830420568902697928091655)
          ·
            refine ⟨107745630853354046892137483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71830420568902697928091655 107745630853354046892137483)
            ·
              refine ⟨161618446280031070338206225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107745630853354046892137483 161618446280031070338206225)
              ·
                refine ⟨121213834710023302753654669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161618446280031070338206225 121213834710023302753654669)
                ·
                  refine ⟨45455188016258738532620501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121213834710023302753654669 45455188016258738532620501)
                  ·
                    refine ⟨1065355969131064184358293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45455188016258738532620501 1065355969131064184358293)
                    ·
                      rfl

theorem cell23_6224320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_6224320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224320 prefixEnd_6224320 := by exact prefixLift 6224320
  have htrace : WordTrace (prefixWord ++ tailWord_6224320) baseStart_6224320 baseEnd_6224320 := by
    simpa [prefixWord, tailWord_6224320, baseEnd_6224320] using wordTrace_append hprefix tailTrace_6224320
  have hstable : (prefixWord ++ tailWord_6224320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224320).length < 2 ^ (prefixWord ++ tailWord_6224320).sum := by decide
  have hdescent : baseEnd_6224320 < baseStart_6224320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224367 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 7, 4]
def baseStart_6224367 : Nat := 118140960795 + 6224367 * 2 ^ 59
def prefixEnd_6224367 : Nat := 4983230072969 + 3 ^ 40 * 6224367 * 2
def baseEnd_6224367 : Nat := 1065364013661317956395721

theorem tailTrace_6224367 : CollatzResearch.WordTrace tailWord_6224367 prefixEnd_6224367 1065364013661317956395721 := by
  unfold tailWord_6224367
  simp only [CollatzResearch.WordTrace]
  refine ⟨227021315041188871095991355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151347543360792580730660903 227021315041188871095991355)
  ·
    refine ⟨340531972561783306643987033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227021315041188871095991355 340531972561783306643987033)
    ·
      refine ⟨255398979421337479982990275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340531972561783306643987033 255398979421337479982990275)
      ·
        refine ⟨383098469132006219974485413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255398979421337479982990275 383098469132006219974485413)
        ·
          refine ⟨71830962962251166245216015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 383098469132006219974485413 71830962962251166245216015)
          ·
            refine ⟨107746444443376749367824023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71830962962251166245216015 107746444443376749367824023)
            ·
              refine ⟨161619666665065124051736035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107746444443376749367824023 161619666665065124051736035)
              ·
                refine ⟨242429499997597686077604053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161619666665065124051736035 242429499997597686077604053)
                ·
                  refine ⟨5681941406193695767443845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 242429499997597686077604053 5681941406193695767443845)
                  ·
                    refine ⟨1065364013661317956395721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5681941406193695767443845 1065364013661317956395721)
                    ·
                      rfl

theorem cell23_6224367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_6224367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224367 prefixEnd_6224367 := by exact prefixLift 6224367
  have htrace : WordTrace (prefixWord ++ tailWord_6224367) baseStart_6224367 baseEnd_6224367 := by
    simpa [prefixWord, tailWord_6224367, baseEnd_6224367] using wordTrace_append hprefix tailTrace_6224367
  have hstable : (prefixWord ++ tailWord_6224367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224367).length < 2 ^ (prefixWord ++ tailWord_6224367).sum := by decide
  have hdescent : baseEnd_6224367 < baseStart_6224367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224374 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6224374 : Nat := 118140960795 + 6224374 * 2 ^ 59
def prefixEnd_6224374 : Nat := 4983230072969 + 3 ^ 40 * 6224374 * 2
def baseEnd_6224374 : Nat := 3196095635348535341799631

theorem tailTrace_6224374 : CollatzResearch.WordTrace tailWord_6224374 prefixEnd_6224374 3196095635348535341799631 := by
  unfold tailWord_6224374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188848147010219455718511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151347713568109007527664117 14188848147010219455718511)
  ·
    refine ⟨21283272220515329183577767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14188848147010219455718511 21283272220515329183577767)
    ·
      refine ⟨31924908330772993775366651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21283272220515329183577767 31924908330772993775366651)
      ·
        refine ⟨47887362496159490663049977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31924908330772993775366651 47887362496159490663049977)
        ·
          refine ⟨35915521872119617997287483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47887362496159490663049977 35915521872119617997287483)
          ·
            refine ⟨53873282808179426995931225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35915521872119617997287483 53873282808179426995931225)
            ·
              refine ⟨40404962106134570246948419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53873282808179426995931225 40404962106134570246948419)
              ·
                refine ⟨60607443159201855370422629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40404962106134570246948419 60607443159201855370422629)
                ·
                  refine ⟨11363895592350347881954243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60607443159201855370422629 11363895592350347881954243)
                  ·
                    refine ⟨17045843388525521822931365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11363895592350347881954243 17045843388525521822931365)
                    ·
                      refine ⟨3196095635348535341799631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17045843388525521822931365 3196095635348535341799631)
                      ·
                        rfl

theorem cell23_6224374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6224374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224374 prefixEnd_6224374 := by exact prefixLift 6224374
  have htrace : WordTrace (prefixWord ++ tailWord_6224374) baseStart_6224374 baseEnd_6224374 := by
    simpa [prefixWord, tailWord_6224374, baseEnd_6224374] using wordTrace_append hprefix tailTrace_6224374
  have hstable : (prefixWord ++ tailWord_6224374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224374).length < 2 ^ (prefixWord ++ tailWord_6224374).sum := by decide
  have hdescent : baseEnd_6224374 < baseStart_6224374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224461 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_6224461 : Nat := 118140960795 + 6224461 * 2 ^ 59
def prefixEnd_6224461 : Nat := 4983230072969 + 3 ^ 40 * 6224461 * 2
def baseEnd_6224461 : Nat := 1065380102721825500470577

theorem tailTrace_6224461 : CollatzResearch.WordTrace tailWord_6224461 prefixEnd_6224461 1065380102721825500470577 := by
  unfold tailWord_6224461
  simp only [CollatzResearch.WordTrace]
  refine ⟨227024743502848325149913237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151349829001898883433275491 227024743502848325149913237)
  ·
    refine ⟨10641784851696015241402183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227024743502848325149913237 10641784851696015241402183)
    ·
      refine ⟨15962677277544022862103275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10641784851696015241402183 15962677277544022862103275)
      ·
        refine ⟨23944015916316034293154913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15962677277544022862103275 23944015916316034293154913)
        ·
          refine ⟨17958011937237025719866185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23944015916316034293154913 17958011937237025719866185)
          ·
            refine ⟨13468508952927769289899639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17958011937237025719866185 13468508952927769289899639)
            ·
              refine ⟨20202763429391653934849459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13468508952927769289899639 20202763429391653934849459)
              ·
                refine ⟨30304145144087480902274189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20202763429391653934849459 30304145144087480902274189)
                ·
                  refine ⟨11364054429032805338352821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30304145144087480902274189 11364054429032805338352821)
                  ·
                    refine ⟨1065380102721825500470577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11364054429032805338352821 1065380102721825500470577)
                    ·
                      rfl

theorem cell23_6224461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_6224461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224461 prefixEnd_6224461 := by exact prefixLift 6224461
  have htrace : WordTrace (prefixWord ++ tailWord_6224461) baseStart_6224461 baseEnd_6224461 := by
    simpa [prefixWord, tailWord_6224461, baseEnd_6224461] using wordTrace_append hprefix tailTrace_6224461
  have hstable : (prefixWord ++ tailWord_6224461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224461).length < 2 ^ (prefixWord ++ tailWord_6224461).sum := by decide
  have hdescent : baseEnd_6224461 < baseStart_6224461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224464 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4]
def baseStart_6224464 : Nat := 118140960795 + 6224464 * 2 ^ 59
def prefixEnd_6224464 : Nat := 4983230072969 + 3 ^ 40 * 6224464 * 2
def baseEnd_6224464 : Nat := 3196141848607439989674217

theorem tailTrace_6224464 : CollatzResearch.WordTrace tailWord_6224464 prefixEnd_6224464 3196141848607439989674217 := by
  unfold tailWord_6224464
  simp only [CollatzResearch.WordTrace]
  refine ⟨113512426460918728331136223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151349901947891637774848297 113512426460918728331136223)
  ·
    refine ⟨170268639691378092496704335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113512426460918728331136223 170268639691378092496704335)
    ·
      refine ⟨255402959537067138745056503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170268639691378092496704335 255402959537067138745056503)
      ·
        refine ⟨383104439305600708117584755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255402959537067138745056503 383104439305600708117584755)
        ·
          refine ⟨574656658958401062176377133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383104439305600708117584755 574656658958401062176377133)
          ·
            refine ⟨215496247109400398316141425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574656658958401062176377133 215496247109400398316141425)
            ·
              refine ⟨161622185332050298737106069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215496247109400398316141425 161622185332050298737106069)
              ·
                refine ⟨7576039937439857753301847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161622185332050298737106069 7576039937439857753301847)
                ·
                  refine ⟨11364059906159786629952771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576039937439857753301847 11364059906159786629952771)
                  ·
                    refine ⟨17046089859239679944929157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11364059906159786629952771 17046089859239679944929157)
                    ·
                      refine ⟨3196141848607439989674217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17046089859239679944929157 3196141848607439989674217)
                      ·
                        rfl

theorem cell23_6224464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_6224464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224464 prefixEnd_6224464 := by exact prefixLift 6224464
  have htrace : WordTrace (prefixWord ++ tailWord_6224464) baseStart_6224464 baseEnd_6224464 := by
    simpa [prefixWord, tailWord_6224464, baseEnd_6224464] using wordTrace_append hprefix tailTrace_6224464
  have hstable : (prefixWord ++ tailWord_6224464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224464).length < 2 ^ (prefixWord ++ tailWord_6224464).sum := by decide
  have hdescent : baseEnd_6224464 < baseStart_6224464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224468 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_6224468 : Nat := 118140960795 + 6224468 * 2 ^ 59
def prefixEnd_6224468 : Nat := 4983230072969 + 3 ^ 40 * 6224468 * 2
def baseEnd_6224468 : Nat := 3196143902530057974024199

theorem tailTrace_6224468 : CollatzResearch.WordTrace tailWord_6224468 prefixEnd_6224468 3196143902530057974024199 := by
  unfold tailWord_6224468
  simp only [CollatzResearch.WordTrace]
  refine ⟨113512499406911482672709029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151349999209215310230278705 113512499406911482672709029)
  ·
    refine ⟨21283593638795903001132943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113512499406911482672709029 21283593638795903001132943)
    ·
      refine ⟨31925390458193854501699415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21283593638795903001132943 31925390458193854501699415)
      ·
        refine ⟨47888085687290781752549123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31925390458193854501699415 47888085687290781752549123)
        ·
          refine ⟨71832128530936172628823685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47888085687290781752549123 71832128530936172628823685)
          ·
            refine ⟨13468524099550532367904441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71832128530936172628823685 13468524099550532367904441)
            ·
              refine ⟨10101393074662899275928331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13468524099550532367904441 10101393074662899275928331)
              ·
                refine ⟨15152089611994348913892497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10101393074662899275928331 15152089611994348913892497)
                ·
                  refine ⟨11364067208995761685419373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15152089611994348913892497 11364067208995761685419373)
                  ·
                    refine ⟨4261525203373410632032265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11364067208995761685419373 4261525203373410632032265)
                    ·
                      refine ⟨3196143902530057974024199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261525203373410632032265 3196143902530057974024199)
                      ·
                        rfl

theorem cell23_6224468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_6224468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224468 prefixEnd_6224468 := by exact prefixLift 6224468
  have htrace : WordTrace (prefixWord ++ tailWord_6224468) baseStart_6224468 baseEnd_6224468 := by
    simpa [prefixWord, tailWord_6224468, baseEnd_6224468] using wordTrace_append hprefix tailTrace_6224468
  have hstable : (prefixWord ++ tailWord_6224468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224468).length < 2 ^ (prefixWord ++ tailWord_6224468).sum := by decide
  have hdescent : baseEnd_6224468 < baseStart_6224468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224527 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_6224527 : Nat := 118140960795 + 6224527 * 2 ^ 59
def prefixEnd_6224527 : Nat := 4983230072969 + 3 ^ 40 * 6224527 * 2
def baseEnd_6224527 : Nat := 3196174197888673243186427

theorem tailTrace_6224527 : CollatzResearch.WordTrace tailWord_6224527 prefixEnd_6224527 3196174197888673243186427 := by
  unfold tailWord_6224527
  simp only [CollatzResearch.WordTrace]
  refine ⟨227027150720609218421815835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151351433813739478947877223 227027150720609218421815835)
  ·
    refine ⟨340540726080913827632723753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227027150720609218421815835 340540726080913827632723753)
    ·
      refine ⟨255405544560685370724542815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340540726080913827632723753 255405544560685370724542815)
      ·
        refine ⟨383108316841028056086814223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255405544560685370724542815 383108316841028056086814223)
        ·
          refine ⟨574662475261542084130221335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383108316841028056086814223 574662475261542084130221335)
          ·
            refine ⟨861993712892313126195332003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574662475261542084130221335 861993712892313126195332003)
            ·
              refine ⟨1292990569338469689292998005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861993712892313126195332003 1292990569338469689292998005)
              ·
                refine ⟨121217865875481533371218563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1292990569338469689292998005 121217865875481533371218563)
                ·
                  refine ⟨181826798813222300056827845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121217865875481533371218563 181826798813222300056827845)
                  ·
                    refine ⟨34092524777479181260655221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181826798813222300056827845 34092524777479181260655221)
                    ·
                      refine ⟨3196174197888673243186427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34092524777479181260655221 3196174197888673243186427)
                      ·
                        rfl

theorem cell23_6224527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_6224527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224527 prefixEnd_6224527 := by exact prefixLift 6224527
  have htrace : WordTrace (prefixWord ++ tailWord_6224527) baseStart_6224527 baseEnd_6224527 := by
    simpa [prefixWord, tailWord_6224527, baseEnd_6224527] using wordTrace_append hprefix tailTrace_6224527
  have hstable : (prefixWord ++ tailWord_6224527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224527).length < 2 ^ (prefixWord ++ tailWord_6224527).sum := by decide
  have hdescent : baseEnd_6224527 < baseStart_6224527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224532 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6224532 : Nat := 118140960795 + 6224532 * 2 ^ 59
def prefixEnd_6224532 : Nat := 4983230072969 + 3 ^ 40 * 6224532 * 2
def baseEnd_6224532 : Nat := 3196176765291945723623905

theorem tailTrace_6224532 : CollatzResearch.WordTrace tailWord_6224532 prefixEnd_6224532 3196176765291945723623905 := by
  unfold tailWord_6224532
  simp only [CollatzResearch.WordTrace]
  refine ⟨113513666542795552137873925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151351555390394069517165233 113513666542795552137873925)
  ·
    refine ⟨21283812476774166025851361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113513666542795552137873925 21283812476774166025851361)
    ·
      refine ⟨15962859357580624519388521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21283812476774166025851361 15962859357580624519388521)
      ·
        refine ⟨11972144518185468389541391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15962859357580624519388521 11972144518185468389541391)
        ·
          refine ⟨17958216777278202584312087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11972144518185468389541391 17958216777278202584312087)
          ·
            refine ⟨26937325165917303876468131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17958216777278202584312087 26937325165917303876468131)
            ·
              refine ⟨40405987748875955814702197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26937325165917303876468131 40405987748875955814702197)
              ·
                refine ⟨3788061351457120857628331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40405987748875955814702197 3788061351457120857628331)
                ·
                  refine ⟨5682092027185681286442497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788061351457120857628331 5682092027185681286442497)
                  ·
                    refine ⟨4261569020389260964831873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682092027185681286442497 4261569020389260964831873)
                    ·
                      refine ⟨3196176765291945723623905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261569020389260964831873 3196176765291945723623905)
                      ·
                        rfl

theorem cell23_6224532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6224532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224532 prefixEnd_6224532 := by exact prefixLift 6224532
  have htrace : WordTrace (prefixWord ++ tailWord_6224532) baseStart_6224532 baseEnd_6224532 := by
    simpa [prefixWord, tailWord_6224532, baseEnd_6224532] using wordTrace_append hprefix tailTrace_6224532
  have hstable : (prefixWord ++ tailWord_6224532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224532).length < 2 ^ (prefixWord ++ tailWord_6224532).sum := by decide
  have hdescent : baseEnd_6224532 < baseStart_6224532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224611 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 7]
def baseStart_6224611 : Nat := 118140960795 + 6224611 * 2 ^ 59
def prefixEnd_6224611 : Nat := 4983230072969 + 3 ^ 40 * 6224611 * 2
def baseEnd_6224611 : Nat := 355135258918183434948449

theorem tailTrace_6224611 : CollatzResearch.WordTrace tailWord_6224611 prefixEnd_6224611 355135258918183434948449 := by
  unfold tailWord_6224611
  simp only [CollatzResearch.WordTrace]
  refine ⟨227030214452304900767873687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151353476301536600511915791 227030214452304900767873687)
  ·
    refine ⟨340545321678457351151810531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227030214452304900767873687 340545321678457351151810531)
    ·
      refine ⟨510817982517686026727715797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340545321678457351151810531 510817982517686026727715797)
      ·
        refine ⟨11972296465258266251430839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 510817982517686026727715797 11972296465258266251430839)
        ·
          refine ⟨17958444697887399377146259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11972296465258266251430839 17958444697887399377146259)
          ·
            refine ⟨26937667046831099065719389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17958444697887399377146259 26937667046831099065719389)
            ·
              refine ⟨10101625142561662149644771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26937667046831099065719389 10101625142561662149644771)
              ·
                refine ⟨15152437713842493224467157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10101625142561662149644771 15152437713842493224467157)
                ·
                  refine ⟨355135258918183434948449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15152437713842493224467157 355135258918183434948449)
                  ·
                    rfl

theorem cell23_6224611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 7].length) (baseStart_6224611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224611 prefixEnd_6224611 := by exact prefixLift 6224611
  have htrace : WordTrace (prefixWord ++ tailWord_6224611) baseStart_6224611 baseEnd_6224611 := by
    simpa [prefixWord, tailWord_6224611, baseEnd_6224611] using wordTrace_append hprefix tailTrace_6224611
  have hstable : (prefixWord ++ tailWord_6224611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224611).length < 2 ^ (prefixWord ++ tailWord_6224611).sum := by decide
  have hdescent : baseEnd_6224611 < baseStart_6224611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224621 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6224621 : Nat := 118140960795 + 6224621 * 2 ^ 59
def prefixEnd_6224621 : Nat := 4983230072969 + 3 ^ 40 * 6224621 * 2
def baseEnd_6224621 : Nat := 3196222465070195875410995

theorem tailTrace_6224621 : CollatzResearch.WordTrace tailWord_6224621 prefixEnd_6224621 3196222465070195875410995 := by
  unfold tailWord_6224621
  simp only [CollatzResearch.WordTrace]
  refine ⟨227030579182268672475737717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151353719454845781650491811 227030579182268672475737717)
  ·
    refine ⟨21284116798337688044600411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227030579182268672475737717 21284116798337688044600411)
    ·
      refine ⟨31926175197506532066900617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21284116798337688044600411 31926175197506532066900617)
      ·
        refine ⟨23944631398129899050175463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31926175197506532066900617 23944631398129899050175463)
        ·
          refine ⟨35916947097194848575263195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23944631398129899050175463 35916947097194848575263195)
          ·
            refine ⟨53875420645792272862894793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35916947097194848575263195 53875420645792272862894793)
            ·
              refine ⟨40406565484344204647171095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53875420645792272862894793 40406565484344204647171095)
              ·
                refine ⟨60609848226516306970756643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40406565484344204647171095 60609848226516306970756643)
                ·
                  refine ⟨90914772339774460456134965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60609848226516306970756643 90914772339774460456134965)
                  ·
                    refine ⟨8523259906853855667762653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90914772339774460456134965 8523259906853855667762653)
                    ·
                      refine ⟨3196222465070195875410995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523259906853855667762653 3196222465070195875410995)
                      ·
                        rfl

theorem cell23_6224621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6224621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224621 prefixEnd_6224621 := by exact prefixLift 6224621
  have htrace : WordTrace (prefixWord ++ tailWord_6224621) baseStart_6224621 baseEnd_6224621 := by
    simpa [prefixWord, tailWord_6224621, baseEnd_6224621] using wordTrace_append hprefix tailTrace_6224621
  have hstable : (prefixWord ++ tailWord_6224621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224621).length < 2 ^ (prefixWord ++ tailWord_6224621).sum := by decide
  have hdescent : baseEnd_6224621 < baseStart_6224621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224622 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_6224622 : Nat := 118140960795 + 6224622 * 2 ^ 59
def prefixEnd_6224622 : Nat := 4983230072969 + 3 ^ 40 * 6224622 * 2
def baseEnd_6224622 : Nat := 3196222978550850371498491

theorem tailTrace_6224622 : CollatzResearch.WordTrace tailWord_6224622 prefixEnd_6224622 3196222978550850371498491 := by
  unfold tailWord_6224622
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378826956908131205815515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151353743770176699764349413 28378826956908131205815515)
  ·
    refine ⟨42568240435362196808723273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28378826956908131205815515 42568240435362196808723273)
    ·
      refine ⟨31926180326521647606542455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42568240435362196808723273 31926180326521647606542455)
      ·
        refine ⟨47889270489782471409813683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31926180326521647606542455 47889270489782471409813683)
        ·
          refine ⟨71833905734673707114720525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47889270489782471409813683 71833905734673707114720525)
          ·
            refine ⟨26937714650502640168020197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71833905734673707114720525 26937714650502640168020197)
            ·
              refine ⟨5050821496969245031503787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26937714650502640168020197 5050821496969245031503787)
              ·
                refine ⟨7576232245453867547255681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5050821496969245031503787 7576232245453867547255681)
                ·
                  refine ⟨5682174184090400660441761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7576232245453867547255681 5682174184090400660441761)
                  ·
                    refine ⟨4261630638067800495331321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682174184090400660441761 4261630638067800495331321)
                    ·
                      refine ⟨3196222978550850371498491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261630638067800495331321 3196222978550850371498491)
                      ·
                        rfl

theorem cell23_6224622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_6224622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224622 prefixEnd_6224622 := by exact prefixLift 6224622
  have htrace : WordTrace (prefixWord ++ tailWord_6224622) baseStart_6224622 baseEnd_6224622 := by
    simpa [prefixWord, tailWord_6224622, baseEnd_6224622] using wordTrace_append hprefix tailTrace_6224622
  have hstable : (prefixWord ++ tailWord_6224622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224622).length < 2 ^ (prefixWord ++ tailWord_6224622).sum := by decide
  have hdescent : baseEnd_6224622 < baseStart_6224622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224624 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_6224624 : Nat := 118140960795 + 6224624 * 2 ^ 59
def prefixEnd_6224624 : Nat := 4983230072969 + 3 ^ 40 * 6224624 * 2
def baseEnd_6224624 : Nat := 1065408001837386454557827

theorem tailTrace_6224624 : CollatzResearch.WordTrace tailWord_6224624 prefixEnd_6224624 1065408001837386454557827 := by
  unfold tailWord_6224624
  simp only [CollatzResearch.WordTrace]
  refine ⟨113515344300628901994048463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151353792400838535992064617 113515344300628901994048463)
  ·
    refine ⟨170273016450943352991072695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113515344300628901994048463 170273016450943352991072695)
    ·
      refine ⟨255409524676415029486609043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170273016450943352991072695 255409524676415029486609043)
      ·
        refine ⟨383114287014622544229913565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255409524676415029486609043 383114287014622544229913565)
        ·
          refine ⟨143667857630483454086217587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383114287014622544229913565 143667857630483454086217587)
          ·
            refine ⟨215501786445725181129326381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143667857630483454086217587 215501786445725181129326381)
            ·
              refine ⟨80813169917146942923497393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215501786445725181129326381 80813169917146942923497393)
              ·
                refine ⟨60609877437860207192623045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80813169917146942923497393 60609877437860207192623045)
                ·
                  refine ⟨11364352019598788848616821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60609877437860207192623045 11364352019598788848616821)
                  ·
                    refine ⟨1065408001837386454557827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11364352019598788848616821 1065408001837386454557827)
                    ·
                      rfl

theorem cell23_6224624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_6224624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224624 prefixEnd_6224624 := by exact prefixLift 6224624
  have htrace : WordTrace (prefixWord ++ tailWord_6224624) baseStart_6224624 baseEnd_6224624 := by
    simpa [prefixWord, tailWord_6224624, baseEnd_6224624] using wordTrace_append hprefix tailTrace_6224624
  have hstable : (prefixWord ++ tailWord_6224624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224624).length < 2 ^ (prefixWord ++ tailWord_6224624).sum := by decide
  have hdescent : baseEnd_6224624 < baseStart_6224624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224661 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_6224661 : Nat := 118140960795 + 6224661 * 2 ^ 59
def prefixEnd_6224661 : Nat := 4983230072969 + 3 ^ 40 * 6224661 * 2
def baseEnd_6224661 : Nat := 3196243004296375718910811

theorem tailTrace_6224661 : CollatzResearch.WordTrace tailWord_6224661 prefixEnd_6224661 3196243004296375718910811 := by
  unfold tailWord_6224661
  simp only [CollatzResearch.WordTrace]
  refine ⟨227032038102123759307193837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151354692068082506204795891 227032038102123759307193837)
  ·
    refine ⟨85137014288296409740197689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227032038102123759307193837 85137014288296409740197689)
    ·
      refine ⟨63852760716222307305148267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85137014288296409740197689 63852760716222307305148267)
      ·
        refine ⟨95779141074333460957722401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63852760716222307305148267 95779141074333460957722401)
        ·
          refine ⟨71834355805750095718291801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95779141074333460957722401 71834355805750095718291801)
          ·
            refine ⟨53875766854312571788718851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71834355805750095718291801 53875766854312571788718851)
            ·
              refine ⟨80813650281468857683078277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53875766854312571788718851 80813650281468857683078277)
              ·
                refine ⟨15152559427775410815577177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80813650281468857683078277 15152559427775410815577177)
                ·
                  refine ⟨11364419570831558111682883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15152559427775410815577177 11364419570831558111682883)
                  ·
                    refine ⟨17046629356247337167524325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11364419570831558111682883 17046629356247337167524325)
                    ·
                      refine ⟨3196243004296375718910811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17046629356247337167524325 3196243004296375718910811)
                      ·
                        rfl

theorem cell23_6224661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_6224661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224661 prefixEnd_6224661 := by exact prefixLift 6224661
  have htrace : WordTrace (prefixWord ++ tailWord_6224661) baseStart_6224661 baseEnd_6224661 := by
    simpa [prefixWord, tailWord_6224661, baseEnd_6224661] using wordTrace_append hprefix tailTrace_6224661
  have hstable : (prefixWord ++ tailWord_6224661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224661).length < 2 ^ (prefixWord ++ tailWord_6224661).sum := by decide
  have hdescent : baseEnd_6224661 < baseStart_6224661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224664 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6224664 : Nat := 118140960795 + 6224664 * 2 ^ 59
def prefixEnd_6224664 : Nat := 4983230072969 + 3 ^ 40 * 6224664 * 2
def baseEnd_6224664 : Nat := 3196244544738339207173297

theorem tailTrace_6224664 : CollatzResearch.WordTrace tailWord_6224664 prefixEnd_6224664 3196244544738339207173297 := by
  unfold tailWord_6224664
  simp only [CollatzResearch.WordTrace]
  refine ⟨113516073760556445409776523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151354765014075260546368697 113516073760556445409776523)
  ·
    refine ⟨170274110640834668114664785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113516073760556445409776523 170274110640834668114664785)
    ·
      refine ⟨127705582980626001085998589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170274110640834668114664785 127705582980626001085998589)
      ·
        refine ⟨47889593617734750407249471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127705582980626001085998589 47889593617734750407249471)
        ·
          refine ⟨71834390426602125610874207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47889593617734750407249471 71834390426602125610874207)
          ·
            refine ⟨107751585639903188416311311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71834390426602125610874207 107751585639903188416311311)
            ·
              refine ⟨161627378459854782624466967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107751585639903188416311311 161627378459854782624466967)
              ·
                refine ⟨242441067689782173936700451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161627378459854782624466967 242441067689782173936700451)
                ·
                  refine ⟨363661601534673260905050677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242441067689782173936700451 363661601534673260905050677)
                  ·
                    refine ⟨34093275143875618209848501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 363661601534673260905050677 34093275143875618209848501)
                    ·
                      refine ⟨3196244544738339207173297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34093275143875618209848501 3196244544738339207173297)
                      ·
                        rfl

theorem cell23_6224664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6224664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224664 prefixEnd_6224664 := by exact prefixLift 6224664
  have htrace : WordTrace (prefixWord ++ tailWord_6224664) baseStart_6224664 baseEnd_6224664 := by
    simpa [prefixWord, tailWord_6224664, baseEnd_6224664] using wordTrace_append hprefix tailTrace_6224664
  have hstable : (prefixWord ++ tailWord_6224664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224664).length < 2 ^ (prefixWord ++ tailWord_6224664).sum := by decide
  have hdescent : baseEnd_6224664 < baseStart_6224664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224692 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_6224692 : Nat := 118140960795 + 6224692 * 2 ^ 59
def prefixEnd_6224692 : Nat := 4983230072969 + 3 ^ 40 * 6224692 * 2
def baseEnd_6224692 : Nat := 1065419640732221699207723

theorem tailTrace_6224692 : CollatzResearch.WordTrace tailWord_6224692 prefixEnd_6224692 1065419640732221699207723 := by
  unfold tailWord_6224692
  simp only [CollatzResearch.WordTrace]
  refine ⟨113516584382505725800786165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151355445843340967734381553 113516584382505725800786165)
  ·
    refine ⟨10642179785859911793823703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113516584382505725800786165 10642179785859911793823703)
    ·
      refine ⟨15963269678789867690735555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10642179785859911793823703 15963269678789867690735555)
      ·
        refine ⟨23944904518184801536103333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15963269678789867690735555 23944904518184801536103333)
        ·
          refine ⟨4489669597159650288019375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23944904518184801536103333 4489669597159650288019375)
          ·
            refine ⟨6734504395739475432029063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489669597159650288019375 6734504395739475432029063)
            ·
              refine ⟨10101756593609213148043595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6734504395739475432029063 10101756593609213148043595)
              ·
                refine ⟨15152634890413819722065393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10101756593609213148043595 15152634890413819722065393)
                ·
                  refine ⟨11364476167810364791549045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15152634890413819722065393 11364476167810364791549045)
                  ·
                    refine ⟨1065419640732221699207723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11364476167810364791549045 1065419640732221699207723)
                    ·
                      rfl

theorem cell23_6224692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_6224692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224692 prefixEnd_6224692 := by exact prefixLift 6224692
  have htrace : WordTrace (prefixWord ++ tailWord_6224692) baseStart_6224692 baseEnd_6224692 := by
    simpa [prefixWord, tailWord_6224692, baseEnd_6224692] using wordTrace_append hprefix tailTrace_6224692
  have hstable : (prefixWord ++ tailWord_6224692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224692).length < 2 ^ (prefixWord ++ tailWord_6224692).sum := by decide
  have hdescent : baseEnd_6224692 < baseStart_6224692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224698 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_6224698 : Nat := 118140960795 + 6224698 * 2 ^ 59
def prefixEnd_6224698 : Nat := 4983230072969 + 3 ^ 40 * 6224698 * 2
def baseEnd_6224698 : Nat := 3196262003080592074148141

theorem tailTrace_6224698 : CollatzResearch.WordTrace tailWord_6224698 prefixEnd_6224698 3196262003080592074148141 := by
  unfold tailWord_6224698
  simp only [CollatzResearch.WordTrace]
  refine ⟨56758346900747428656572687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151355591735326476417527165 56758346900747428656572687)
  ·
    refine ⟨85137520351121142984859031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56758346900747428656572687 85137520351121142984859031)
    ·
      refine ⟨127706280526681714477288547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85137520351121142984859031 127706280526681714477288547)
      ·
        refine ⟨191559420790022571715932821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127706280526681714477288547 191559420790022571715932821)
        ·
          refine ⟨8979347849532308049184351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191559420790022571715932821 8979347849532308049184351)
          ·
            refine ⟨13469021774298462073776527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8979347849532308049184351 13469021774298462073776527)
            ·
              refine ⟨20203532661447693110664791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469021774298462073776527 20203532661447693110664791)
              ·
                refine ⟨30305298992171539665997187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20203532661447693110664791 30305298992171539665997187)
                ·
                  refine ⟨45457948488257309498995781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30305298992171539665997187 45457948488257309498995781)
                  ·
                    refine ⟨8523365341548245531061709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45457948488257309498995781 8523365341548245531061709)
                    ·
                      refine ⟨3196262003080592074148141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523365341548245531061709 3196262003080592074148141)
                      ·
                        rfl

theorem cell23_6224698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_6224698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224698 prefixEnd_6224698 := by exact prefixLift 6224698
  have htrace : WordTrace (prefixWord ++ tailWord_6224698) baseStart_6224698 baseEnd_6224698 := by
    simpa [prefixWord, tailWord_6224698, baseEnd_6224698] using wordTrace_append hprefix tailTrace_6224698
  have hstable : (prefixWord ++ tailWord_6224698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224698).length < 2 ^ (prefixWord ++ tailWord_6224698).sum := by decide
  have hdescent : baseEnd_6224698 < baseStart_6224698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224704 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_6224704 : Nat := 118140960795 + 6224704 * 2 ^ 59
def prefixEnd_6224704 : Nat := 4983230072969 + 3 ^ 40 * 6224704 * 2
def baseEnd_6224704 : Nat := 3196265083964519050673113

theorem tailTrace_6224704 : CollatzResearch.WordTrace tailWord_6224704 prefixEnd_6224704 3196265083964519050673113 := by
  unfold tailWord_6224704
  simp only [CollatzResearch.WordTrace]
  refine ⟨113516803220483988825504583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151355737627311985100672777 113516803220483988825504583)
  ·
    refine ⟨170275204830725983238256875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113516803220483988825504583 170275204830725983238256875)
    ·
      refine ⟨255412807246088974857385313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170275204830725983238256875 255412807246088974857385313)
      ·
        refine ⟨191559605434566731143038985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255412807246088974857385313 191559605434566731143038985)
        ·
          refine ⟨143669704075925048357279239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191559605434566731143038985 143669704075925048357279239)
          ·
            refine ⟨215504556113887572535918859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143669704075925048357279239 215504556113887572535918859)
            ·
              refine ⟨323256834170831358803878289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215504556113887572535918859 323256834170831358803878289)
              ·
                refine ⟨242442625628123519102908717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323256834170831358803878289 242442625628123519102908717)
                ·
                  refine ⟨90915984610546319663590769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242442625628123519102908717 90915984610546319663590769)
                  ·
                    refine ⟨68186988457909739747693077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90915984610546319663590769 68186988457909739747693077)
                    ·
                      refine ⟨3196265083964519050673113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68186988457909739747693077 3196265083964519050673113)
                      ·
                        rfl

theorem cell23_6224704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_6224704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224704 prefixEnd_6224704 := by exact prefixLift 6224704
  have htrace : WordTrace (prefixWord ++ tailWord_6224704) baseStart_6224704 baseEnd_6224704 := by
    simpa [prefixWord, tailWord_6224704, baseEnd_6224704] using wordTrace_append hprefix tailTrace_6224704
  have hstable : (prefixWord ++ tailWord_6224704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224704).length < 2 ^ (prefixWord ++ tailWord_6224704).sum := by decide
  have hdescent : baseEnd_6224704 < baseStart_6224704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224748 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_6224748 : Nat := 118140960795 + 6224748 * 2 ^ 59
def prefixEnd_6224748 : Nat := 4983230072969 + 3 ^ 40 * 6224748 * 2
def baseEnd_6224748 : Nat := 1065429225704438959507637

theorem tailTrace_6224748 : CollatzResearch.WordTrace tailWord_6224748 prefixEnd_6224748 1065429225704438959507637 := by
  unfold tailWord_6224748
  simp only [CollatzResearch.WordTrace]
  refine ⟨113517605626404286582805449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151356807501872382110407265 113517605626404286582805449)
  ·
    refine ⟨85138204219803214937104087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113517605626404286582805449 85138204219803214937104087)
    ·
      refine ⟨127707306329704822405656131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85138204219803214937104087 127707306329704822405656131)
      ·
        refine ⟨191560959494557233608484197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127707306329704822405656131 191560959494557233608484197)
        ·
          refine ⟨35917679905229481301590787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191560959494557233608484197 35917679905229481301590787)
          ·
            refine ⟨53876519857844221952386181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35917679905229481301590787 53876519857844221952386181)
            ·
              refine ⟨10101847473345791616072409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53876519857844221952386181 10101847473345791616072409)
              ·
                refine ⟨7576385605009343712054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10101847473345791616072409 7576385605009343712054307)
                ·
                  refine ⟨11364578407514015568081461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576385605009343712054307 11364578407514015568081461)
                  ·
                    refine ⟨1065429225704438959507637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11364578407514015568081461 1065429225704438959507637)
                    ·
                      rfl

theorem cell23_6224748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_6224748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224748 prefixEnd_6224748 := by exact prefixLift 6224748
  have htrace : WordTrace (prefixWord ++ tailWord_6224748) baseStart_6224748 baseEnd_6224748 := by
    simpa [prefixWord, tailWord_6224748, baseEnd_6224748] using wordTrace_append hprefix tailTrace_6224748
  have hstable : (prefixWord ++ tailWord_6224748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224748).length < 2 ^ (prefixWord ++ tailWord_6224748).sum := by decide
  have hdescent : baseEnd_6224748 < baseStart_6224748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224751 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_6224751 : Nat := 118140960795 + 6224751 * 2 ^ 59
def prefixEnd_6224751 : Nat := 4983230072969 + 3 ^ 40 * 6224751 * 2
def baseEnd_6224751 : Nat := 3196289217555280366785397

theorem tailTrace_6224751 : CollatzResearch.WordTrace tailWord_6224751 prefixEnd_6224751 3196289217555280366785397 := by
  unfold tailWord_6224751
  simp only [CollatzResearch.WordTrace]
  refine ⟨227035320671797704677970107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151356880447865136451980071 227035320671797704677970107)
  ·
    refine ⟨340552981007696557016955161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227035320671797704677970107 340552981007696557016955161)
    ·
      refine ⟨255414735755772417762716371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340552981007696557016955161 255414735755772417762716371)
      ·
        refine ⟨383122103633658626644074557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255414735755772417762716371 383122103633658626644074557)
        ·
          refine ⟨143670788862621984991527959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383122103633658626644074557 143670788862621984991527959)
          ·
            refine ⟨215506183293932977487291939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143670788862621984991527959 215506183293932977487291939)
            ·
              refine ⟨323259274940899466230937909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215506183293932977487291939 323259274940899466230937909)
              ·
                refine ⟨30305557025709324959150429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323259274940899466230937909 30305557025709324959150429)
                ·
                  refine ⟨11364583884640996859681411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30305557025709324959150429 11364583884640996859681411)
                  ·
                    refine ⟨17046875826961495289522117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11364583884640996859681411 17046875826961495289522117)
                    ·
                      refine ⟨3196289217555280366785397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17046875826961495289522117 3196289217555280366785397)
                      ·
                        rfl

theorem cell23_6224751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_6224751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224751 prefixEnd_6224751 := by exact prefixLift 6224751
  have htrace : WordTrace (prefixWord ++ tailWord_6224751) baseStart_6224751 baseEnd_6224751 := by
    simpa [prefixWord, tailWord_6224751, baseEnd_6224751] using wordTrace_append hprefix tailTrace_6224751
  have hstable : (prefixWord ++ tailWord_6224751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224751).length < 2 ^ (prefixWord ++ tailWord_6224751).sum := by decide
  have hdescent : baseEnd_6224751 < baseStart_6224751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224788 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6224788 : Nat := 118140960795 + 6224788 * 2 ^ 59
def prefixEnd_6224788 : Nat := 4983230072969 + 3 ^ 40 * 6224788 * 2
def baseEnd_6224788 : Nat := 3196308216339496722022727

theorem tailTrace_6224788 : CollatzResearch.WordTrace tailWord_6224788 prefixEnd_6224788 3196308216339496722022727 := by
  unfold tailWord_6224788
  simp only [CollatzResearch.WordTrace]
  refine ⟨113518335086331829998533509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151357780115109106664711345 113518335086331829998533509)
  ·
    refine ⟨21284687828687218124725033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113518335086331829998533509 21284687828687218124725033)
    ·
      refine ⟨15963515871515413593543775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21284687828687218124725033 15963515871515413593543775)
      ·
        refine ⟨23945273807273120390315663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15963515871515413593543775 23945273807273120390315663)
        ·
          refine ⟨35917910710909680585473495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23945273807273120390315663 35917910710909680585473495)
          ·
            refine ⟨53876866066364520878210243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35917910710909680585473495 53876866066364520878210243)
            ·
              refine ⟨80815299099546781317315365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53876866066364520878210243 80815299099546781317315365)
              ·
                refine ⟨15152868581165021496996631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80815299099546781317315365 15152868581165021496996631)
                ·
                  refine ⟨22729302871747532245494947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15152868581165021496996631 22729302871747532245494947)
                  ·
                    refine ⟨34093954307621298368242421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22729302871747532245494947 34093954307621298368242421)
                    ·
                      refine ⟨3196308216339496722022727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34093954307621298368242421 3196308216339496722022727)
                      ·
                        rfl

theorem cell23_6224788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6224788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224788 prefixEnd_6224788 := by exact prefixLift 6224788
  have htrace : WordTrace (prefixWord ++ tailWord_6224788) baseStart_6224788 baseEnd_6224788 := by
    simpa [prefixWord, tailWord_6224788, baseEnd_6224788] using wordTrace_append hprefix tailTrace_6224788
  have hstable : (prefixWord ++ tailWord_6224788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224788).length < 2 ^ (prefixWord ++ tailWord_6224788).sum := by decide
  have hdescent : baseEnd_6224788 < baseStart_6224788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224791 : List Nat := [1, 1, 3, 3, 1, 2, 4, 8]
def baseStart_6224791 : Nat := 118140960795 + 6224791 * 2 ^ 59
def prefixEnd_6224791 : Nat := 4983230072969 + 3 ^ 40 * 6224791 * 2
def baseEnd_6224791 : Nat := 118381842843757785566119

theorem tailTrace_6224791 : CollatzResearch.WordTrace tailWord_6224791 prefixEnd_6224791 118381842843757785566119 := by
  unfold tailWord_6224791
  simp only [CollatzResearch.WordTrace]
  refine ⟨227036779591652791509426227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151357853061101861006284151 227036779591652791509426227)
  ·
    refine ⟨340555169387479187264139341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227036779591652791509426227 340555169387479187264139341)
    ·
      refine ⟨127708188520304695224052253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340555169387479187264139341 127708188520304695224052253)
      ·
        refine ⟨47890570695114260709019595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127708188520304695224052253 47890570695114260709019595)
        ·
          refine ⟨71835856042671391063529393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47890570695114260709019595 71835856042671391063529393)
          ·
            refine ⟨53876892032003543297647045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71835856042671391063529393 53876892032003543297647045)
            ·
              refine ⟨10101917256000664368308821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53876892032003543297647045 10101917256000664368308821)
              ·
                refine ⟨118381842843757785566119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10101917256000664368308821 118381842843757785566119)
                ·
                  rfl

theorem cell23_6224791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 8].length) (baseStart_6224791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224791 prefixEnd_6224791 := by exact prefixLift 6224791
  have htrace : WordTrace (prefixWord ++ tailWord_6224791) baseStart_6224791 baseEnd_6224791 := by
    simpa [prefixWord, tailWord_6224791, baseEnd_6224791] using wordTrace_append hprefix tailTrace_6224791
  have hstable : (prefixWord ++ tailWord_6224791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224791).length < 2 ^ (prefixWord ++ tailWord_6224791).sum := by decide
  have hdescent : baseEnd_6224791 < baseStart_6224791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224802 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_6224802 : Nat := 118140960795 + 6224802 * 2 ^ 59
def prefixEnd_6224802 : Nat := 4983230072969 + 3 ^ 40 * 6224802 * 2
def baseEnd_6224802 : Nat := 3196315405068659667247663

theorem tailTrace_6224802 : CollatzResearch.WordTrace tailWord_6224802 prefixEnd_6224802 3196315405068659667247663 := by
  unfold tailWord_6224802
  simp only [CollatzResearch.WordTrace]
  refine ⟨56759295198653235097019165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151358120529741960258717773 56759295198653235097019165)
  ·
    refine ⟨21284735699494963161382187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56759295198653235097019165 21284735699494963161382187)
    ·
      refine ⟨31927103549242444742073281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21284735699494963161382187 31927103549242444742073281)
      ·
        refine ⟨23945327661931833556554961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31927103549242444742073281 23945327661931833556554961)
        ·
          refine ⟨17958995746448875167416221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23945327661931833556554961 17958995746448875167416221)
          ·
            refine ⟨6734623404918328187781083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17958995746448875167416221 6734623404918328187781083)
            ·
              refine ⟨10101935107377492281671625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6734623404918328187781083 10101935107377492281671625)
              ·
                refine ⟨7576451330533119211253719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10101935107377492281671625 7576451330533119211253719)
                ·
                  refine ⟨11364676995799678816880579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576451330533119211253719 11364676995799678816880579)
                  ·
                    refine ⟨17047015493699518225320869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11364676995799678816880579 17047015493699518225320869)
                    ·
                      refine ⟨3196315405068659667247663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17047015493699518225320869 3196315405068659667247663)
                      ·
                        rfl

theorem cell23_6224802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_6224802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224802 prefixEnd_6224802 := by exact prefixLift 6224802
  have htrace : WordTrace (prefixWord ++ tailWord_6224802) baseStart_6224802 baseEnd_6224802 := by
    simpa [prefixWord, tailWord_6224802, baseEnd_6224802] using wordTrace_append hprefix tailTrace_6224802
  have hstable : (prefixWord ++ tailWord_6224802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224802).length < 2 ^ (prefixWord ++ tailWord_6224802).sum := by decide
  have hdescent : baseEnd_6224802 < baseStart_6224802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224852 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6224852 : Nat := 118140960795 + 6224852 * 2 ^ 59
def prefixEnd_6224852 : Nat := 4983230072969 + 3 ^ 40 * 6224852 * 2
def baseEnd_6224852 : Nat := 3196341079101384471622433

theorem tailTrace_6224852 : CollatzResearch.WordTrace tailWord_6224852 prefixEnd_6224852 3196341079101384471622433 := by
  unfold tailWord_6224852
  simp only [CollatzResearch.WordTrace]
  refine ⟨113519502222215899463698405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151359336296287865951597873 113519502222215899463698405)
  ·
    refine ⟨21284906666665481149443451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113519502222215899463698405 21284906666665481149443451)
    ·
      refine ⟨31927359999998221724165177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21284906666665481149443451 31927359999998221724165177)
      ·
        refine ⟨23945519999998666293123883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31927359999998221724165177 23945519999998666293123883)
        ·
          refine ⟨35918279999997999439685825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23945519999998666293123883 35918279999997999439685825)
          ·
            refine ⟨26938709999998499579764369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35918279999997999439685825 26938709999998499579764369)
            ·
              refine ⟨20204032499998874684823277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26938709999998499579764369 20204032499998874684823277)
              ·
                refine ⟨7576512187499578006808729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20204032499998874684823277 7576512187499578006808729)
                ·
                  refine ⟨5682384140624683505106547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7576512187499578006808729 5682384140624683505106547)
                  ·
                    refine ⟨8523576210937025257659821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5682384140624683505106547 8523576210937025257659821)
                    ·
                      refine ⟨3196341079101384471622433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523576210937025257659821 3196341079101384471622433)
                      ·
                        rfl

theorem cell23_6224852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6224852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224852 prefixEnd_6224852 := by exact prefixLift 6224852
  have htrace : WordTrace (prefixWord ++ tailWord_6224852) baseStart_6224852 baseEnd_6224852 := by
    simpa [prefixWord, tailWord_6224852, baseEnd_6224852] using wordTrace_append hprefix tailTrace_6224852
  have hstable : (prefixWord ++ tailWord_6224852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224852).length < 2 ^ (prefixWord ++ tailWord_6224852).sum := by decide
  have hdescent : baseEnd_6224852 < baseStart_6224852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224879 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 1, 3, 2]
def baseStart_6224879 : Nat := 118140960795 + 6224879 * 2 ^ 59
def prefixEnd_6224879 : Nat := 4983230072969 + 3 ^ 40 * 6224879 * 2
def baseEnd_6224879 : Nat := 3196354943079055865984809

theorem tailTrace_6224879 : CollatzResearch.WordTrace tailWord_6224879 prefixEnd_6224879 3196354943079055865984809 := by
  unfold tailWord_6224879
  simp only [CollatzResearch.WordTrace]
  refine ⟨227039989215333982538629691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151359992810222655025753127 227039989215333982538629691)
  ·
    refine ⟨340559983823000973807944537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227039989215333982538629691 340559983823000973807944537)
    ·
      refine ⟨255419987867250730355958403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340559983823000973807944537 255419987867250730355958403)
      ·
        refine ⟨383129981800876095533937605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255419987867250730355958403 383129981800876095533937605)
        ·
          refine ⟨71836871587664267912613301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 383129981800876095533937605 71836871587664267912613301)
          ·
            refine ⟨6734706711343525116807497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71836871587664267912613301 6734706711343525116807497)
            ·
              refine ⟨5051030033507643837605623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6734706711343525116807497 5051030033507643837605623)
              ·
                refine ⟨7576545050261465756408435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051030033507643837605623 7576545050261465756408435)
                ·
                  refine ⟨11364817575392198634612653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576545050261465756408435 11364817575392198634612653)
                  ·
                    refine ⟨4261806590772074487979745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11364817575392198634612653 4261806590772074487979745)
                    ·
                      refine ⟨3196354943079055865984809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261806590772074487979745 3196354943079055865984809)
                      ·
                        rfl

theorem cell23_6224879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 3, 2].length) (baseStart_6224879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224879 prefixEnd_6224879 := by exact prefixLift 6224879
  have htrace : WordTrace (prefixWord ++ tailWord_6224879) baseStart_6224879 baseEnd_6224879 := by
    simpa [prefixWord, tailWord_6224879, baseEnd_6224879] using wordTrace_append hprefix tailTrace_6224879
  have hstable : (prefixWord ++ tailWord_6224879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224879).length < 2 ^ (prefixWord ++ tailWord_6224879).sum := by decide
  have hdescent : baseEnd_6224879 < baseStart_6224879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224892 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_6224892 : Nat := 118140960795 + 6224892 * 2 ^ 59
def prefixEnd_6224892 : Nat := 4983230072969 + 3 ^ 40 * 6224892 * 2
def baseEnd_6224892 : Nat := 3196361618327564315122249

theorem tailTrace_6224892 : CollatzResearch.WordTrace tailWord_6224892 prefixEnd_6224892 3196361618327564315122249 := by
  unfold tailWord_6224892
  simp only [CollatzResearch.WordTrace]
  refine ⟨113520231682143442879426465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151360308909524590505901953 113520231682143442879426465)
  ·
    refine ⟨85140173761607582159569849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113520231682143442879426465 85140173761607582159569849)
    ·
      refine ⟨63855130321205686619677387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85140173761607582159569849 63855130321205686619677387)
      ·
        refine ⟨95782695481808529929516081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63855130321205686619677387 95782695481808529929516081)
        ·
          refine ⟨71837021611356397447137061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95782695481808529929516081 71837021611356397447137061)
          ·
            refine ⟨13469441552129324521338199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71837021611356397447137061 13469441552129324521338199)
            ·
              refine ⟨20204162328193986782007299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469441552129324521338199 20204162328193986782007299)
              ·
                refine ⟨30306243492290980173010949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20204162328193986782007299 30306243492290980173010949)
                ·
                  refine ⟨5682420654804558782439553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30306243492290980173010949 5682420654804558782439553)
                  ·
                    refine ⟨4261815491103419086829665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682420654804558782439553 4261815491103419086829665)
                    ·
                      refine ⟨3196361618327564315122249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261815491103419086829665 3196361618327564315122249)
                      ·
                        rfl

theorem cell23_6224892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_6224892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224892 prefixEnd_6224892 := by exact prefixLift 6224892
  have htrace : WordTrace (prefixWord ++ tailWord_6224892) baseStart_6224892 baseEnd_6224892 := by
    simpa [prefixWord, tailWord_6224892, baseEnd_6224892] using wordTrace_append hprefix tailTrace_6224892
  have hstable : (prefixWord ++ tailWord_6224892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224892).length < 2 ^ (prefixWord ++ tailWord_6224892).sum := by decide
  have hdescent : baseEnd_6224892 < baseStart_6224892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224932 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 5]
def baseStart_6224932 : Nat := 118140960795 + 6224932 * 2 ^ 59
def prefixEnd_6224932 : Nat := 4983230072969 + 3 ^ 40 * 6224932 * 2
def baseEnd_6224932 : Nat := 355153573061527128735785

theorem tailTrace_6224932 : CollatzResearch.WordTrace tailWord_6224932 prefixEnd_6224932 355153573061527128735785 := by
  unfold tailWord_6224932
  simp only [CollatzResearch.WordTrace]
  refine ⟨113520961142070986295154525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151361281522761315060206033 113520961142070986295154525)
  ·
    refine ⟨42570360428276619860682947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113520961142070986295154525 42570360428276619860682947)
    ·
      refine ⟨63855540642414929791024421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42570360428276619860682947 63855540642414929791024421)
      ·
        refine ⟨11972913870452799335817079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63855540642414929791024421 11972913870452799335817079)
        ·
          refine ⟨17959370805679199003725619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11972913870452799335817079 17959370805679199003725619)
          ·
            refine ⟨26939056208518798505588429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17959370805679199003725619 26939056208518798505588429)
            ·
              refine ⟨10102146078194549439595661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26939056208518798505588429 10102146078194549439595661)
              ·
                refine ⟨3788304779322956039848373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10102146078194549439595661 3788304779322956039848373)
                ·
                  refine ⟨355153573061527128735785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3788304779322956039848373 355153573061527128735785)
                  ·
                    rfl

theorem cell23_6224932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_6224932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224932 prefixEnd_6224932 := by exact prefixLift 6224932
  have htrace : WordTrace (prefixWord ++ tailWord_6224932) baseStart_6224932 baseEnd_6224932 := by
    simpa [prefixWord, tailWord_6224932, baseEnd_6224932] using wordTrace_append hprefix tailTrace_6224932
  have hstable : (prefixWord ++ tailWord_6224932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224932).length < 2 ^ (prefixWord ++ tailWord_6224932).sum := by decide
  have hdescent : baseEnd_6224932 < baseStart_6224932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224965 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 2, 4, 2]
def baseStart_6224965 : Nat := 118140960795 + 6224965 * 2 ^ 59
def prefixEnd_6224965 : Nat := 4983230072969 + 3 ^ 40 * 6224965 * 2
def baseEnd_6224965 : Nat := 3196399102415342529509413

theorem tailTrace_6224965 : CollatzResearch.WordTrace tailWord_6224965 prefixEnd_6224965 3196399102415342529509413 := by
  unfold tailWord_6224965
  simp only [CollatzResearch.WordTrace]
  refine ⟨227043125893022419226260349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151362083928681612817506899 227043125893022419226260349)
  ·
    refine ⟨85141172209883407209847631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227043125893022419226260349 85141172209883407209847631)
    ·
      refine ⟨127711758314825110814771447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85141172209883407209847631 127711758314825110814771447)
      ·
        refine ⟨191567637472237666222157171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127711758314825110814771447 191567637472237666222157171)
        ·
          refine ⟨287351456208356499333235757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191567637472237666222157171 287351456208356499333235757)
          ·
            refine ⟨107756796078133687249963409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287351456208356499333235757 107756796078133687249963409)
            ·
              refine ⟨80817597058600265437472557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107756796078133687249963409 80817597058600265437472557)
              ·
                refine ⟨30306598896975099539052209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80817597058600265437472557 30306598896975099539052209)
                ·
                  refine ⟨22729949172731324654289157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30306598896975099539052209 22729949172731324654289157)
                  ·
                    refine ⟨4261865469887123372679217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22729949172731324654289157 4261865469887123372679217)
                    ·
                      refine ⟨3196399102415342529509413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261865469887123372679217 3196399102415342529509413)
                      ·
                        rfl

theorem cell23_6224965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_6224965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224965 prefixEnd_6224965 := by exact prefixLift 6224965
  have htrace : WordTrace (prefixWord ++ tailWord_6224965) baseStart_6224965 baseEnd_6224965 := by
    simpa [prefixWord, tailWord_6224965, baseEnd_6224965] using wordTrace_append hprefix tailTrace_6224965
  have hstable : (prefixWord ++ tailWord_6224965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224965).length < 2 ^ (prefixWord ++ tailWord_6224965).sum := by decide
  have hdescent : baseEnd_6224965 < baseStart_6224965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6224992 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 1, 4]
def baseStart_6224992 : Nat := 118140960795 + 6224992 * 2 ^ 59
def prefixEnd_6224992 : Nat := 4983230072969 + 3 ^ 40 * 6224992 * 2
def baseEnd_6224992 : Nat := 1065470988797671307957263

theorem tailTrace_6224992 : CollatzResearch.WordTrace tailWord_6224992 prefixEnd_6224992 1065470988797671307957263 := by
  unfold tailWord_6224992
  simp only [CollatzResearch.WordTrace]
  refine ⟨113522055331962301418746615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151362740442616401891662153 113522055331962301418746615)
  ·
    refine ⟨170283082997943452128119923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113522055331962301418746615 170283082997943452128119923)
    ·
      refine ⟨255424624496915178192179885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170283082997943452128119923 255424624496915178192179885)
      ·
        refine ⟨95784234186343191822067457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255424624496915178192179885 95784234186343191822067457)
        ·
          refine ⟨71838175639757393866550593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95784234186343191822067457 71838175639757393866550593)
          ·
            refine ⟨53878631729818045399912945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71838175639757393866550593 53878631729818045399912945)
            ·
              refine ⟨40408973797363534049934709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53878631729818045399912945 40408973797363534049934709)
              ·
                refine ⟨3788341293502831317181379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40408973797363534049934709 3788341293502831317181379)
                ·
                  refine ⟨5682511940254246975772069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788341293502831317181379 5682511940254246975772069)
                  ·
                    refine ⟨1065470988797671307957263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5682511940254246975772069 1065470988797671307957263)
                    ·
                      rfl

theorem cell23_6224992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 4].length) (baseStart_6224992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6224992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6224992 prefixEnd_6224992 := by exact prefixLift 6224992
  have htrace : WordTrace (prefixWord ++ tailWord_6224992) baseStart_6224992 baseEnd_6224992 := by
    simpa [prefixWord, tailWord_6224992, baseEnd_6224992] using wordTrace_append hprefix tailTrace_6224992
  have hstable : (prefixWord ++ tailWord_6224992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6224992).length < 2 ^ (prefixWord ++ tailWord_6224992).sum := by decide
  have hdescent : baseEnd_6224992 < baseStart_6224992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6224992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225002 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6225002 : Nat := 118140960795 + 6225002 * 2 ^ 59
def prefixEnd_6225002 : Nat := 4983230072969 + 3 ^ 40 * 6225002 * 2
def baseEnd_6225002 : Nat := 3196418101199558884746743

theorem tailTrace_6225002 : CollatzResearch.WordTrace tailWord_6225002 prefixEnd_6225002 3196418101199558884746743 := by
  unfold tailWord_6225002
  simp only [CollatzResearch.WordTrace]
  refine ⟨56761118848472093636339315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151362983595925583030238173 56761118848472093636339315)
  ·
    refine ⟨85141678272708140454508973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56761118848472093636339315 85141678272708140454508973)
    ·
      refine ⟨31928129352265552670440865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85141678272708140454508973 31928129352265552670440865)
      ·
        refine ⟨23946097014199164502830649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31928129352265552670440865 23946097014199164502830649)
        ·
          refine ⟨17959572760649373377122987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23946097014199164502830649 17959572760649373377122987)
          ·
            refine ⟨26939359140974060065684481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17959572760649373377122987 26939359140974060065684481)
            ·
              refine ⟨20204519355730545049263361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26939359140974060065684481 20204519355730545049263361)
              ·
                refine ⟨15153389516797908786947521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20204519355730545049263361 15153389516797908786947521)
                ·
                  refine ⟨11365042137598431590210641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15153389516797908786947521 11365042137598431590210641)
                  ·
                    refine ⟨8523781603198823692657981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11365042137598431590210641 8523781603198823692657981)
                    ·
                      refine ⟨3196418101199558884746743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523781603198823692657981 3196418101199558884746743)
                      ·
                        rfl

theorem cell23_6225002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6225002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225002 prefixEnd_6225002 := by exact prefixLift 6225002
  have htrace : WordTrace (prefixWord ++ tailWord_6225002) baseStart_6225002 baseEnd_6225002 := by
    simpa [prefixWord, tailWord_6225002, baseEnd_6225002] using wordTrace_append hprefix tailTrace_6225002
  have hstable : (prefixWord ++ tailWord_6225002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225002).length < 2 ^ (prefixWord ++ tailWord_6225002).sum := by decide
  have hdescent : baseEnd_6225002 < baseStart_6225002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225005 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 6]
def baseStart_6225005 : Nat := 118140960795 + 6225005 * 2 ^ 59
def prefixEnd_6225005 : Nat := 4983230072969 + 3 ^ 40 * 6225005 * 2
def baseEnd_6225005 : Nat := 355157737960169152556581

theorem tailTrace_6225005 : CollatzResearch.WordTrace tailWord_6225005 prefixEnd_6225005 355157737960169152556581 := by
  unfold tailWord_6225005
  simp only [CollatzResearch.WordTrace]
  refine ⟨227044584812877506057716469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151363056541918337371810979 227044584812877506057716469)
  ·
    refine ⟨21285429826207266192910919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227044584812877506057716469 21285429826207266192910919)
    ·
      refine ⟨31928144739310899289366379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21285429826207266192910919 31928144739310899289366379)
      ·
        refine ⟨47892217108966348934049569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31928144739310899289366379 47892217108966348934049569)
        ·
          refine ⟨35919162831724761700537177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47892217108966348934049569 35919162831724761700537177)
          ·
            refine ⟨26939372123793571275402883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35919162831724761700537177 26939372123793571275402883)
            ·
              refine ⟨40409058185690356913104325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26939372123793571275402883 40409058185690356913104325)
              ·
                refine ⟨7576698409816941921207061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40409058185690356913104325 7576698409816941921207061)
                ·
                  refine ⟨355157737960169152556581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7576698409816941921207061 355157737960169152556581)
                  ·
                    rfl

theorem cell23_6225005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_6225005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225005 prefixEnd_6225005 := by exact prefixLift 6225005
  have htrace : WordTrace (prefixWord ++ tailWord_6225005) baseStart_6225005 baseEnd_6225005 := by
    simpa [prefixWord, tailWord_6225005, baseEnd_6225005] using wordTrace_append hprefix tailTrace_6225005
  have hstable : (prefixWord ++ tailWord_6225005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225005).length < 2 ^ (prefixWord ++ tailWord_6225005).sum := by decide
  have hdescent : baseEnd_6225005 < baseStart_6225005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225008 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_6225008 : Nat := 118140960795 + 6225008 * 2 ^ 59
def prefixEnd_6225008 : Nat := 4983230072969 + 3 ^ 40 * 6225008 * 2
def baseEnd_6225008 : Nat := 3196421182083485861271715

theorem tailTrace_6225008 : CollatzResearch.WordTrace tailWord_6225008 prefixEnd_6225008 3196421182083485861271715 := by
  unfold tailWord_6225008
  simp only [CollatzResearch.WordTrace]
  refine ⟨113522347115933318785037839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151363129487911091713383785 113522347115933318785037839)
  ·
    refine ⟨170283520673899978177556759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113522347115933318785037839 170283520673899978177556759)
    ·
      refine ⟨255425281010849967266335139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170283520673899978177556759 255425281010849967266335139)
      ·
        refine ⟨383137921516274950899502709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255425281010849967266335139 383137921516274950899502709)
        ·
          refine ⟨35919180142150776646828379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 383137921516274950899502709 35919180142150776646828379)
          ·
            refine ⟨53878770213226164970242569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35919180142150776646828379 53878770213226164970242569)
            ·
              refine ⟨40409077659919623727681927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53878770213226164970242569 40409077659919623727681927)
              ·
                refine ⟨60613616489879435591522891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40409077659919623727681927 60613616489879435591522891)
                ·
                  refine ⟨90920424734819153387284337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60613616489879435591522891 90920424734819153387284337)
                  ·
                    refine ⟨68190318551114365040463253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90920424734819153387284337 68190318551114365040463253)
                    ·
                      refine ⟨3196421182083485861271715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68190318551114365040463253 3196421182083485861271715)
                      ·
                        rfl

theorem cell23_6225008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_6225008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225008 prefixEnd_6225008 := by exact prefixLift 6225008
  have htrace : WordTrace (prefixWord ++ tailWord_6225008) baseStart_6225008 baseEnd_6225008 := by
    simpa [prefixWord, tailWord_6225008, baseEnd_6225008] using wordTrace_append hprefix tailTrace_6225008
  have hstable : (prefixWord ++ tailWord_6225008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225008).length < 2 ^ (prefixWord ++ tailWord_6225008).sum := by decide
  have hdescent : baseEnd_6225008 < baseStart_6225008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225052 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_6225052 : Nat := 118140960795 + 6225052 * 2 ^ 59
def prefixEnd_6225052 : Nat := 4983230072969 + 3 ^ 40 * 6225052 * 2
def baseEnd_6225052 : Nat := 1065481258410761229707171

theorem tailTrace_6225052 : CollatzResearch.WordTrace tailWord_6225052 prefixEnd_6225052 1065481258410761229707171 := by
  unfold tailWord_6225052
  simp only [CollatzResearch.WordTrace]
  refine ⟨113523149521853616542338705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151364199362471488723118273 113523149521853616542338705)
  ·
    refine ⟨85142362141390212406754029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113523149521853616542338705 85142362141390212406754029)
    ·
      refine ⟨31928385803021329652532761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85142362141390212406754029 31928385803021329652532761)
      ·
        refine ⟨23946289352265997239399571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31928385803021329652532761 23946289352265997239399571)
        ·
          refine ⟨35919434028398995859099357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23946289352265997239399571 35919434028398995859099357)
          ·
            refine ⟨13469787760649623447162259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35919434028398995859099357 13469787760649623447162259)
            ·
              refine ⟨20204681640974435170743389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469787760649623447162259 20204681640974435170743389)
              ·
                refine ⟨7576755615365413189028771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20204681640974435170743389 7576755615365413189028771)
                ·
                  refine ⟨11365133423048119783543157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576755615365413189028771 11365133423048119783543157)
                  ·
                    refine ⟨1065481258410761229707171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11365133423048119783543157 1065481258410761229707171)
                    ·
                      rfl

theorem cell23_6225052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_6225052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225052 prefixEnd_6225052 := by exact prefixLift 6225052
  have htrace : WordTrace (prefixWord ++ tailWord_6225052) baseStart_6225052 baseEnd_6225052 := by
    simpa [prefixWord, tailWord_6225052, baseEnd_6225052] using wordTrace_append hprefix tailTrace_6225052
  have hstable : (prefixWord ++ tailWord_6225052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225052).length < 2 ^ (prefixWord ++ tailWord_6225052).sum := by decide
  have hdescent : baseEnd_6225052 < baseStart_6225052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225066 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6225066 : Nat := 118140960795 + 6225066 * 2 ^ 59
def prefixEnd_6225066 : Nat := 4983230072969 + 3 ^ 40 * 6225066 * 2
def baseEnd_6225066 : Nat := 3196450963961446634346449

theorem tailTrace_6225066 : CollatzResearch.WordTrace tailWord_6225066 prefixEnd_6225066 3196450963961446634346449 := by
  unfold tailWord_6225066
  simp only [CollatzResearch.WordTrace]
  refine ⟨56761702416414128368921763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151364539777104342317124701 56761702416414128368921763)
  ·
    refine ⟨85142553624621192553382645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56761702416414128368921763 85142553624621192553382645)
    ·
      refine ⟨7982114402308236801879623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85142553624621192553382645 7982114402308236801879623)
      ·
        refine ⟨11973171603462355202819435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982114402308236801879623 11973171603462355202819435)
        ·
          refine ⟨17959757405193532804229153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973171603462355202819435 17959757405193532804229153)
          ·
            refine ⟨13469818053895149603171865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17959757405193532804229153 13469818053895149603171865)
            ·
              refine ⟨10102363540421362202378899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13469818053895149603171865 10102363540421362202378899)
              ·
                refine ⟨15153545310632043303568349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10102363540421362202378899 15153545310632043303568349)
                ·
                  refine ⟨5682579491487016238838131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15153545310632043303568349 5682579491487016238838131)
                  ·
                    refine ⟨8523869237230524358257197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5682579491487016238838131 8523869237230524358257197)
                    ·
                      refine ⟨3196450963961446634346449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523869237230524358257197 3196450963961446634346449)
                      ·
                        rfl

theorem cell23_6225066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6225066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225066 prefixEnd_6225066 := by exact prefixLift 6225066
  have htrace : WordTrace (prefixWord ++ tailWord_6225066) baseStart_6225066 baseEnd_6225066 := by
    simpa [prefixWord, tailWord_6225066, baseEnd_6225066] using wordTrace_append hprefix tailTrace_6225066
  have hstable : (prefixWord ++ tailWord_6225066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225066).length < 2 ^ (prefixWord ++ tailWord_6225066).sum := by decide
  have hdescent : baseEnd_6225066 < baseStart_6225066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225072 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 7, 2, 2]
def baseStart_6225072 : Nat := 118140960795 + 6225072 * 2 ^ 59
def prefixEnd_6225072 : Nat := 4983230072969 + 3 ^ 40 * 6225072 * 2
def baseEnd_6225072 : Nat := 3196454044845373610871421

theorem tailTrace_6225072 : CollatzResearch.WordTrace tailWord_6225072 prefixEnd_6225072 3196454044845373610871421 := by
  unfold tailWord_6225072
  simp only [CollatzResearch.WordTrace]
  refine ⟨113523514251817388250202735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151364685669089851000270313 113523514251817388250202735)
  ·
    refine ⟨170285271377726082375304103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113523514251817388250202735 170285271377726082375304103)
    ·
      refine ⟨255427907066589123562956155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170285271377726082375304103 255427907066589123562956155)
      ·
        refine ⟨383141860599883685344434233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255427907066589123562956155 383141860599883685344434233)
        ·
          refine ⟨287356395449912764008325675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383141860599883685344434233 287356395449912764008325675)
          ·
            refine ⟨431034593174869146012488513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287356395449912764008325675 431034593174869146012488513)
            ·
              refine ⟨323275944881151859509366385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431034593174869146012488513 323275944881151859509366385)
              ·
                refine ⟨242456958660863894632024789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323275944881151859509366385 242456958660863894632024789)
                ·
                  refine ⟨5682584968613997530438081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 242456958660863894632024789 5682584968613997530438081)
                  ·
                    refine ⟨4261938726460498147828561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682584968613997530438081 4261938726460498147828561)
                    ·
                      refine ⟨3196454044845373610871421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4261938726460498147828561 3196454044845373610871421)
                      ·
                        rfl

theorem cell23_6225072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 2, 2].length) (baseStart_6225072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225072 prefixEnd_6225072 := by exact prefixLift 6225072
  have htrace : WordTrace (prefixWord ++ tailWord_6225072) baseStart_6225072 baseEnd_6225072 := by
    simpa [prefixWord, tailWord_6225072, baseEnd_6225072] using wordTrace_append hprefix tailTrace_6225072
  have hstable : (prefixWord ++ tailWord_6225072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225072).length < 2 ^ (prefixWord ++ tailWord_6225072).sum := by decide
  have hdescent : baseEnd_6225072 < baseStart_6225072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225075 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 3]
def baseStart_6225075 : Nat := 118140960795 + 6225075 * 2 ^ 59
def prefixEnd_6225075 : Nat := 4983230072969 + 3 ^ 40 * 6225075 * 2
def baseEnd_6225075 : Nat := 3196455585287337099133907

theorem tailTrace_6225075 : CollatzResearch.WordTrace tailWord_6225075 prefixEnd_6225075 3196455585287337099133907 := by
  unfold tailWord_6225075
  simp only [CollatzResearch.WordTrace]
  refine ⟨227047137922623908012764679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151364758615082605341843119 227047137922623908012764679)
  ·
    refine ⟨340570706883935862019147019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227047137922623908012764679 340570706883935862019147019)
    ·
      refine ⟨510856060325903793028720529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340570706883935862019147019 510856060325903793028720529)
      ·
        refine ⟨383142045244427844771540397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510856060325903793028720529 383142045244427844771540397)
        ·
          refine ⟨143678266966660441789327649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383142045244427844771540397 143678266966660441789327649)
          ·
            refine ⟨107758700224995331341995737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143678266966660441789327649 107758700224995331341995737)
            ·
              refine ⟨80819025168746498506496803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107758700224995331341995737 80819025168746498506496803)
              ·
                refine ⟨121228537753119747759745205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80819025168746498506496803 121228537753119747759745205)
                ·
                  refine ⟨11365175414354976352476113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121228537753119747759745205 11365175414354976352476113)
                  ·
                    refine ⟨8523881560766232264357085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11365175414354976352476113 8523881560766232264357085)
                    ·
                      refine ⟨3196455585287337099133907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523881560766232264357085 3196455585287337099133907)
                      ·
                        rfl

theorem cell23_6225075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_6225075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225075 prefixEnd_6225075 := by exact prefixLift 6225075
  have htrace : WordTrace (prefixWord ++ tailWord_6225075) baseStart_6225075 baseEnd_6225075 := by
    simpa [prefixWord, tailWord_6225075, baseEnd_6225075] using wordTrace_append hprefix tailTrace_6225075
  have hstable : (prefixWord ++ tailWord_6225075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225075).length < 2 ^ (prefixWord ++ tailWord_6225075).sum := by decide
  have hdescent : baseEnd_6225075 < baseStart_6225075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225089 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6225089 : Nat := 118140960795 + 6225089 * 2 ^ 59
def prefixEnd_6225089 : Nat := 4983230072969 + 3 ^ 40 * 6225089 * 2
def baseEnd_6225089 : Nat := 3196462774016500044358843

theorem tailTrace_6225089 : CollatzResearch.WordTrace tailWord_6225089 prefixEnd_6225089 3196462774016500044358843 := by
  unfold tailWord_6225089
  simp only [CollatzResearch.WordTrace]
  refine ⟨227047648544573188403774321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151365099029715458935849547 227047648544573188403774321)
  ·
    refine ⟨170285736408429891302830741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227047648544573188403774321 170285736408429891302830741)
    ·
      refine ⟨7982143894145151154820191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170285736408429891302830741 7982143894145151154820191)
      ·
        refine ⟨11973215841217726732230287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982143894145151154820191 11973215841217726732230287)
        ·
          refine ⟨17959823761826590098345431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973215841217726732230287 17959823761826590098345431)
          ·
            refine ⟨26939735642739885147518147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17959823761826590098345431 26939735642739885147518147)
            ·
              refine ⟨40409603464109827721277221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26939735642739885147518147 40409603464109827721277221)
              ·
                refine ⟨7576800649520592697739479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40409603464109827721277221 7576800649520592697739479)
                ·
                  refine ⟨11365200974280889046609219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576800649520592697739479 11365200974280889046609219)
                  ·
                    refine ⟨17047801461421333569913829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11365200974280889046609219 17047801461421333569913829)
                    ·
                      refine ⟨3196462774016500044358843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17047801461421333569913829 3196462774016500044358843)
                      ·
                        rfl

theorem cell23_6225089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6225089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225089 prefixEnd_6225089 := by exact prefixLift 6225089
  have htrace : WordTrace (prefixWord ++ tailWord_6225089) baseStart_6225089 baseEnd_6225089 := by
    simpa [prefixWord, tailWord_6225089, baseEnd_6225089] using wordTrace_append hprefix tailTrace_6225089
  have hstable : (prefixWord ++ tailWord_6225089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225089).length < 2 ^ (prefixWord ++ tailWord_6225089).sum := by decide
  have hdescent : baseEnd_6225089 < baseStart_6225089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225105 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_6225105 : Nat := 118140960795 + 6225105 * 2 ^ 59
def prefixEnd_6225105 : Nat := 4983230072969 + 3 ^ 40 * 6225105 * 2
def baseEnd_6225105 : Nat := 3196470989706971981758769

theorem tailTrace_6225105 : CollatzResearch.WordTrace tailWord_6225105 prefixEnd_6225105 3196470989706971981758769 := by
  unfold tailWord_6225105
  simp only [CollatzResearch.WordTrace]
  refine ⟨227048232112515223136356769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151365488075010148757571179 227048232112515223136356769)
  ·
    refine ⟨170286174084386417352267577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227048232112515223136356769 170286174084386417352267577)
    ·
      refine ⟨127714630563289813014200683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170286174084386417352267577 127714630563289813014200683)
      ·
        refine ⟨191571945844934719521301025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127714630563289813014200683 191571945844934719521301025)
        ·
          refine ⟨143678959383701039640975769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191571945844934719521301025 143678959383701039640975769)
          ·
            refine ⟨107759219537775779730731827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143678959383701039640975769 107759219537775779730731827)
            ·
              refine ⟨161638829306663669596097741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107759219537775779730731827 161638829306663669596097741)
              ·
                refine ⟨60614560989998876098536653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161638829306663669596097741 60614560989998876098536653)
                ·
                  refine ⟨22730460371249578536951245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60614560989998876098536653 22730460371249578536951245)
                  ·
                    refine ⟨8523922639218591951356717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22730460371249578536951245 8523922639218591951356717)
                    ·
                      refine ⟨3196470989706971981758769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523922639218591951356717 3196470989706971981758769)
                      ·
                        rfl

theorem cell23_6225105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_6225105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225105 prefixEnd_6225105 := by exact prefixLift 6225105
  have htrace : WordTrace (prefixWord ++ tailWord_6225105) baseStart_6225105 baseEnd_6225105 := by
    simpa [prefixWord, tailWord_6225105, baseEnd_6225105] using wordTrace_append hprefix tailTrace_6225105
  have hstable : (prefixWord ++ tailWord_6225105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225105).length < 2 ^ (prefixWord ++ tailWord_6225105).sum := by decide
  have hdescent : baseEnd_6225105 < baseStart_6225105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225109 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6225109 : Nat := 118140960795 + 6225109 * 2 ^ 59
def prefixEnd_6225109 : Nat := 4983230072969 + 3 ^ 40 * 6225109 * 2
def baseEnd_6225109 : Nat := 3196473043629589966108751

theorem tailTrace_6225109 : CollatzResearch.WordTrace tailWord_6225109 prefixEnd_6225109 3196473043629589966108751 := by
  unfold tailWord_6225109
  simp only [CollatzResearch.WordTrace]
  refine ⟨227048378004500731819502381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151365585336333821213001587 227048378004500731819502381)
  ·
    refine ⟨85143141751687774432313393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227048378004500731819502381 85143141751687774432313393)
    ·
      refine ⟨63857356313765830824235045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85143141751687774432313393 63857356313765830824235045)
      ·
        refine ⟨11973254308831093279544071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63857356313765830824235045 11973254308831093279544071)
        ·
          refine ⟨17959881463246639919316107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973254308831093279544071 17959881463246639919316107)
          ·
            refine ⟨26939822194869959878974161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17959881463246639919316107 26939822194869959878974161)
            ·
              refine ⟨20204866646152469909230621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26939822194869959878974161 20204866646152469909230621)
              ·
                refine ⟨7576824992307176215961483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20204866646152469909230621 7576824992307176215961483)
                ·
                  refine ⟨11365237488460764323942225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576824992307176215961483 11365237488460764323942225)
                  ·
                    refine ⟨8523928116345573242956669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11365237488460764323942225 8523928116345573242956669)
                    ·
                      refine ⟨3196473043629589966108751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523928116345573242956669 3196473043629589966108751)
                      ·
                        rfl

theorem cell23_6225109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6225109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225109 prefixEnd_6225109 := by exact prefixLift 6225109
  have htrace : WordTrace (prefixWord ++ tailWord_6225109) baseStart_6225109 baseEnd_6225109 := by
    simpa [prefixWord, tailWord_6225109, baseEnd_6225109] using wordTrace_append hprefix tailTrace_6225109
  have hstable : (prefixWord ++ tailWord_6225109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225109).length < 2 ^ (prefixWord ++ tailWord_6225109).sum := by decide
  have hdescent : baseEnd_6225109 < baseStart_6225109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225112 : List Nat := [2, 1, 2, 2, 6, 1, 9]
def baseStart_6225112 : Nat := 118140960795 + 6225112 * 2 ^ 59
def prefixEnd_6225112 : Nat := 4983230072969 + 3 ^ 40 * 6225112 * 2
def baseEnd_6225112 : Nat := 39462649186068561165077

theorem tailTrace_6225112 : CollatzResearch.WordTrace tailWord_6225112 prefixEnd_6225112 39462649186068561165077 := by
  unfold tailWord_6225112
  simp only [CollatzResearch.WordTrace]
  refine ⟨113524243711744931665930795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151365658282326575554574393 113524243711744931665930795)
  ·
    refine ⟨170286365567617397498896193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113524243711744931665930795 170286365567617397498896193)
    ·
      refine ⟨127714774175713048124172145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170286365567617397498896193 127714774175713048124172145)
      ·
        refine ⟨95786080631784786093129109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127714774175713048124172145 95786080631784786093129109)
        ·
          refine ⟨4489972529614911848115427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95786080631784786093129109 4489972529614911848115427)
          ·
            refine ⟨6734958794422367772173141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489972529614911848115427 6734958794422367772173141)
            ·
              refine ⟨39462649186068561165077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6734958794422367772173141 39462649186068561165077)
              ·
                rfl

theorem cell23_6225112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 9].length) (baseStart_6225112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225112 prefixEnd_6225112 := by exact prefixLift 6225112
  have htrace : WordTrace (prefixWord ++ tailWord_6225112) baseStart_6225112 baseEnd_6225112 := by
    simpa [prefixWord, tailWord_6225112, baseEnd_6225112] using wordTrace_append hprefix tailTrace_6225112
  have hstable : (prefixWord ++ tailWord_6225112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225112).length < 2 ^ (prefixWord ++ tailWord_6225112).sum := by decide
  have hdescent : baseEnd_6225112 < baseStart_6225112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225139 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 3]
def baseStart_6225139 : Nat := 118140960795 + 6225139 * 2 ^ 59
def prefixEnd_6225139 : Nat := 4983230072969 + 3 ^ 40 * 6225139 * 2
def baseEnd_6225139 : Nat := 3196488448049224848733613

theorem tailTrace_6225139 : CollatzResearch.WordTrace tailWord_6225139 prefixEnd_6225139 3196488448049224848733613 := by
  unfold tailWord_6225139
  simp only [CollatzResearch.WordTrace]
  refine ⟨227049472194392046943094471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151366314796261364628729647 227049472194392046943094471)
  ·
    refine ⟨340574208291588070414641707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227049472194392046943094471 340574208291588070414641707)
    ·
      refine ⟨510861312437382105621962561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340574208291588070414641707 510861312437382105621962561)
      ·
        refine ⟨383145984328036579216471921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510861312437382105621962561 383145984328036579216471921)
        ·
          refine ⟨287359488246027434412353941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383145984328036579216471921 287359488246027434412353941)
          ·
            refine ⟨13469976011532535988079091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287359488246027434412353941 13469976011532535988079091)
            ·
              refine ⟨20204964017298803982118637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469976011532535988079091 20204964017298803982118637)
              ·
                refine ⟨7576861506487051493294489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20204964017298803982118637 7576861506487051493294489)
                ·
                  refine ⟨5682646129865288619970867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7576861506487051493294489 5682646129865288619970867)
                  ·
                    refine ⟨8523969194797932929956301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5682646129865288619970867 8523969194797932929956301)
                    ·
                      refine ⟨3196488448049224848733613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8523969194797932929956301 3196488448049224848733613)
                      ·
                        rfl

theorem cell23_6225139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_6225139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225139 prefixEnd_6225139 := by exact prefixLift 6225139
  have htrace : WordTrace (prefixWord ++ tailWord_6225139) baseStart_6225139 baseEnd_6225139 := by
    simpa [prefixWord, tailWord_6225139, baseEnd_6225139] using wordTrace_append hprefix tailTrace_6225139
  have hstable : (prefixWord ++ tailWord_6225139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225139).length < 2 ^ (prefixWord ++ tailWord_6225139).sum := by decide
  have hdescent : baseEnd_6225139 < baseStart_6225139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225140 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6225140 : Nat := 118140960795 + 6225140 * 2 ^ 59
def prefixEnd_6225140 : Nat := 4983230072969 + 3 ^ 40 * 6225140 * 2
def baseEnd_6225140 : Nat := 3196488961529879344821109

theorem tailTrace_6225140 : CollatzResearch.WordTrace tailWord_6225140 prefixEnd_6225140 3196488961529879344821109 := by
  unfold tailWord_6225140
  simp only [CollatzResearch.WordTrace]
  refine ⟨113524754333694212056940437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151366339111592282742587249 113524754333694212056940437)
  ·
    refine ⟨5321472859391916190169083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113524754333694212056940437 5321472859391916190169083)
    ·
      refine ⟨7982209289087874285253625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5321472859391916190169083 7982209289087874285253625)
      ·
        refine ⟨5986656966815905713940219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7982209289087874285253625 5986656966815905713940219)
        ·
          refine ⟨8979985450223858570910329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5986656966815905713940219 8979985450223858570910329)
          ·
            refine ⟨6734989087667893928182747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8979985450223858570910329 6734989087667893928182747)
            ·
              refine ⟨10102483631501840892274121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6734989087667893928182747 10102483631501840892274121)
              ·
                refine ⟨7576862723626380669205591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10102483631501840892274121 7576862723626380669205591)
                ·
                  refine ⟨11365294085439571003808387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576862723626380669205591 11365294085439571003808387)
                  ·
                    refine ⟨17047941128159356505712581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11365294085439571003808387 17047941128159356505712581)
                    ·
                      refine ⟨3196488961529879344821109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17047941128159356505712581 3196488961529879344821109)
                      ·
                        rfl

theorem cell23_6225140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6225140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225140 prefixEnd_6225140 := by exact prefixLift 6225140
  have htrace : WordTrace (prefixWord ++ tailWord_6225140) baseStart_6225140 baseEnd_6225140 := by
    simpa [prefixWord, tailWord_6225140, baseEnd_6225140] using wordTrace_append hprefix tailTrace_6225140
  have hstable : (prefixWord ++ tailWord_6225140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225140).length < 2 ^ (prefixWord ++ tailWord_6225140).sum := by decide
  have hdescent : baseEnd_6225140 < baseStart_6225140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225185 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 7]
def baseStart_6225185 : Nat := 118140960795 + 6225185 * 2 ^ 59
def prefixEnd_6225185 : Nat := 4983230072969 + 3 ^ 40 * 6225185 * 2
def baseEnd_6225185 : Nat := 355168007573259074306489

theorem tailTrace_6225185 : CollatzResearch.WordTrace tailWord_6225185 prefixEnd_6225185 355168007573259074306489 := by
  unfold tailWord_6225185
  simp only [CollatzResearch.WordTrace]
  refine ⟨227051149952225396799269009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151367433301483597866179339 227051149952225396799269009)
  ·
    refine ⟨170288362464169047599451757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227051149952225396799269009 170288362464169047599451757)
    ·
      refine ⟨63858135924063392849794409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170288362464169047599451757 63858135924063392849794409)
      ·
        refine ⟨47893601943047544637345807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63858135924063392849794409 47893601943047544637345807)
        ·
          refine ⟨71840402914571316956018711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47893601943047544637345807 71840402914571316956018711)
          ·
            refine ⟨107760604371856975434028067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71840402914571316956018711 107760604371856975434028067)
            ·
              refine ⟨161640906557785463151042101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107760604371856975434028067 161640906557785463151042101)
              ·
                refine ⟨15153834989792387170410197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161640906557785463151042101 15153834989792387170410197)
                ·
                  refine ⟨355168007573259074306489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15153834989792387170410197 355168007573259074306489)
                  ·
                    rfl

theorem cell23_6225185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_6225185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225185 prefixEnd_6225185 := by exact prefixLift 6225185
  have htrace : WordTrace (prefixWord ++ tailWord_6225185) baseStart_6225185 baseEnd_6225185 := by
    simpa [prefixWord, tailWord_6225185, baseEnd_6225185] using wordTrace_append hprefix tailTrace_6225185
  have hstable : (prefixWord ++ tailWord_6225185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225185).length < 2 ^ (prefixWord ++ tailWord_6225185).sum := by decide
  have hdescent : baseEnd_6225185 < baseStart_6225185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225192 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6225192 : Nat := 118140960795 + 6225192 * 2 ^ 59
def prefixEnd_6225192 : Nat := 4983230072969 + 3 ^ 40 * 6225192 * 2
def baseEnd_6225192 : Nat := 3196515662523913141370869

theorem tailTrace_6225192 : CollatzResearch.WordTrace tailWord_6225192 prefixEnd_6225192 3196515662523913141370869 := by
  unfold tailWord_6225192
  simp only [CollatzResearch.WordTrace]
  refine ⟨113525702631600018497386915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151367603508800024663182553 113525702631600018497386915)
  ·
    refine ⟨170288553947400027746080373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113525702631600018497386915 170288553947400027746080373)
    ·
      refine ⟨15964551932568752601195035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170288553947400027746080373 15964551932568752601195035)
      ·
        refine ⟨23946827898853128901792553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15964551932568752601195035 23946827898853128901792553)
        ·
          refine ⟨17960120924139846676344415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23946827898853128901792553 17960120924139846676344415)
          ·
            refine ⟨26940181386209770014516623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960120924139846676344415 26940181386209770014516623)
            ·
              refine ⟨40410272079314655021774935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26940181386209770014516623 40410272079314655021774935)
              ·
                refine ⟨60615408118971982532662403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40410272079314655021774935 60615408118971982532662403)
                ·
                  refine ⟨90923112178457973798993605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60615408118971982532662403 90923112178457973798993605)
                  ·
                    refine ⟨17048083533460870087311301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90923112178457973798993605 17048083533460870087311301)
                    ·
                      refine ⟨3196515662523913141370869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17048083533460870087311301 3196515662523913141370869)
                      ·
                        rfl

theorem cell23_6225192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6225192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225192 prefixEnd_6225192 := by exact prefixLift 6225192
  have htrace : WordTrace (prefixWord ++ tailWord_6225192) baseStart_6225192 baseEnd_6225192 := by
    simpa [prefixWord, tailWord_6225192, baseEnd_6225192] using wordTrace_append hprefix tailTrace_6225192
  have hstable : (prefixWord ++ tailWord_6225192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225192).length < 2 ^ (prefixWord ++ tailWord_6225192).sum := by decide
  have hdescent : baseEnd_6225192 < baseStart_6225192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225202 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_6225202 : Nat := 118140960795 + 6225202 * 2 ^ 59
def prefixEnd_6225202 : Nat := 4983230072969 + 3 ^ 40 * 6225202 * 2
def baseEnd_6225202 : Nat := 355168977481162011360647

theorem tailTrace_6225202 : CollatzResearch.WordTrace tailWord_6225202 prefixEnd_6225202 355168977481162011360647 := by
  unfold tailWord_6225202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56762942498290952175659465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151367846662109205801758573 56762942498290952175659465)
  ·
    refine ⟨42572206873718214131744599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56762942498290952175659465 42572206873718214131744599)
    ·
      refine ⟨63858310310577321197616899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42572206873718214131744599 63858310310577321197616899)
      ·
        refine ⟨95787465465865981796425349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63858310310577321197616899 95787465465865981796425349)
        ·
          refine ⟨17960149774849871586829753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95787465465865981796425349 17960149774849871586829753)
          ·
            refine ⟨13470112331137403690122315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17960149774849871586829753 13470112331137403690122315)
            ·
              refine ⟨20205168496706105535183473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13470112331137403690122315 20205168496706105535183473)
              ·
                refine ⟨15153876372529579151387605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20205168496706105535183473 15153876372529579151387605)
                ·
                  refine ⟨355168977481162011360647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15153876372529579151387605 355168977481162011360647)
                  ·
                    rfl

theorem cell23_6225202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_6225202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225202 prefixEnd_6225202 := by exact prefixLift 6225202
  have htrace : WordTrace (prefixWord ++ tailWord_6225202) baseStart_6225202 baseEnd_6225202 := by
    simpa [prefixWord, tailWord_6225202, baseEnd_6225202] using wordTrace_append hprefix tailTrace_6225202
  have hstable : (prefixWord ++ tailWord_6225202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225202).length < 2 ^ (prefixWord ++ tailWord_6225202).sum := by decide
  have hdescent : baseEnd_6225202 < baseStart_6225202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225225 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_6225225 : Nat := 118140960795 + 6225225 * 2 ^ 59
def prefixEnd_6225225 : Nat := 4983230072969 + 3 ^ 40 * 6225225 * 2
def baseEnd_6225225 : Nat := 3196532607385511512258217

theorem tailTrace_6225225 : CollatzResearch.WordTrace tailWord_6225225 prefixEnd_6225225 3196532607385511512258217 := by
  unfold tailWord_6225225
  simp only [CollatzResearch.WordTrace]
  refine ⟨227052608872080483630725129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151368405914720322420483419 227052608872080483630725129)
  ·
    refine ⟨170289456654060362723043847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227052608872080483630725129 170289456654060362723043847)
    ·
      refine ⟨255434184981090544084565771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170289456654060362723043847 255434184981090544084565771)
      ·
        refine ⟨383151277471635816126848657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255434184981090544084565771 383151277471635816126848657)
        ·
          refine ⟨287363458103726862095136493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383151277471635816126848657 287363458103726862095136493)
          ·
            refine ⟨107761296788897573285676185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287363458103726862095136493 107761296788897573285676185)
            ·
              refine ⟨80820972591673179964257139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107761296788897573285676185 80820972591673179964257139)
              ·
                refine ⟨121231458887509769946385709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80820972591673179964257139 121231458887509769946385709)
                ·
                  refine ⟨45461797082816163729894641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121231458887509769946385709 45461797082816163729894641)
                  ·
                    refine ⟨34096347812112122797420981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45461797082816163729894641 34096347812112122797420981)
                    ·
                      refine ⟨3196532607385511512258217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34096347812112122797420981 3196532607385511512258217)
                      ·
                        rfl

theorem cell23_6225225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_6225225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225225 prefixEnd_6225225 := by exact prefixLift 6225225
  have htrace : WordTrace (prefixWord ++ tailWord_6225225) baseStart_6225225 baseEnd_6225225 := by
    simpa [prefixWord, tailWord_6225225, baseEnd_6225225] using wordTrace_append hprefix tailTrace_6225225
  have hstable : (prefixWord ++ tailWord_6225225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225225).length < 2 ^ (prefixWord ++ tailWord_6225225).sum := by decide
  have hdescent : baseEnd_6225225 < baseStart_6225225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225252 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_6225252 : Nat := 118140960795 + 6225252 * 2 ^ 59
def prefixEnd_6225252 : Nat := 4983230072969 + 3 ^ 40 * 6225252 * 2
def baseEnd_6225252 : Nat := 3196546471363182906620593

theorem tailTrace_6225252 : CollatzResearch.WordTrace tailWord_6225252 prefixEnd_6225252 3196546471363182906620593 := by
  unfold tailWord_6225252
  simp only [CollatzResearch.WordTrace]
  refine ⟨113526796821491333620979005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151369062428655111494638673 113526796821491333620979005)
  ·
    refine ⟨42572548808059250107867127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113526796821491333620979005 42572548808059250107867127)
    ·
      refine ⟨63858823212088875161800691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42572548808059250107867127 63858823212088875161800691)
      ·
        refine ⟨95788234818133312742701037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63858823212088875161800691 95788234818133312742701037)
        ·
          refine ⟨35920588056799992278512889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95788234818133312742701037 35920588056799992278512889)
          ·
            refine ⟨26940441042599994208884667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35920588056799992278512889 26940441042599994208884667)
            ·
              refine ⟨40410661563899991313327001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26940441042599994208884667 40410661563899991313327001)
              ·
                refine ⟨30307996172924993484995251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40410661563899991313327001 30307996172924993484995251)
                ·
                  refine ⟨45461994259387490227492877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30307996172924993484995251 45461994259387490227492877)
                  ·
                    refine ⟨17048247847270308835309829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45461994259387490227492877 17048247847270308835309829)
                    ·
                      refine ⟨3196546471363182906620593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17048247847270308835309829 3196546471363182906620593)
                      ·
                        rfl

theorem cell23_6225252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_6225252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225252 prefixEnd_6225252 := by exact prefixLift 6225252
  have htrace : WordTrace (prefixWord ++ tailWord_6225252) baseStart_6225252 baseEnd_6225252 := by
    simpa [prefixWord, tailWord_6225252, baseEnd_6225252] using wordTrace_append hprefix tailTrace_6225252
  have hstable : (prefixWord ++ tailWord_6225252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225252).length < 2 ^ (prefixWord ++ tailWord_6225252).sum := by decide
  have hdescent : baseEnd_6225252 < baseStart_6225252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225272 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_6225272 : Nat := 118140960795 + 6225272 * 2 ^ 59
def prefixEnd_6225272 : Nat := 4983230072969 + 3 ^ 40 * 6225272 * 2
def baseEnd_6225272 : Nat := 3196556740976272828370501

theorem tailTrace_6225272 : CollatzResearch.WordTrace tailWord_6225272 prefixEnd_6225272 3196556740976272828370501 := by
  unfold tailWord_6225272
  simp only [CollatzResearch.WordTrace]
  refine ⟨113527161551455105328843035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151369548735273473771790713 113527161551455105328843035)
  ·
    refine ⟨170290742327182657993264553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113527161551455105328843035 170290742327182657993264553)
    ·
      refine ⟨127718056745386993494948415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170290742327182657993264553 127718056745386993494948415)
      ·
        refine ⟨191577085118080490242422623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127718056745386993494948415 191577085118080490242422623)
        ·
          refine ⟨287365627677120735363633935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191577085118080490242422623 287365627677120735363633935)
          ·
            refine ⟨431048441515681103045450903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287365627677120735363633935 431048441515681103045450903)
            ·
              refine ⟨646572662273521654568176355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431048441515681103045450903 646572662273521654568176355)
              ·
                refine ⟨969858993410282481852264533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646572662273521654568176355 969858993410282481852264533)
                ·
                  refine ⟨11365535079026747834206225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 969858993410282481852264533 11365535079026747834206225)
                  ·
                    refine ⟨8524151309270060875654669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11365535079026747834206225 8524151309270060875654669)
                    ·
                      refine ⟨3196556740976272828370501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524151309270060875654669 3196556740976272828370501)
                      ·
                        rfl

theorem cell23_6225272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_6225272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225272 prefixEnd_6225272 := by exact prefixLift 6225272
  have htrace : WordTrace (prefixWord ++ tailWord_6225272) baseStart_6225272 baseEnd_6225272 := by
    simpa [prefixWord, tailWord_6225272, baseEnd_6225272] using wordTrace_append hprefix tailTrace_6225272
  have hstable : (prefixWord ++ tailWord_6225272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225272).length < 2 ^ (prefixWord ++ tailWord_6225272).sum := by decide
  have hdescent : baseEnd_6225272 < baseStart_6225272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225275 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 10]
def baseStart_6225275 : Nat := 118140960795 + 6225275 * 2 ^ 59
def prefixEnd_6225275 : Nat := 4983230072969 + 3 ^ 40 * 6225275 * 2
def baseEnd_6225275 : Nat := 355173142379804035181443

theorem tailTrace_6225275 : CollatzResearch.WordTrace tailWord_6225275 prefixEnd_6225275 355173142379804035181443 := by
  unfold tailWord_6225275
  simp only [CollatzResearch.WordTrace]
  refine ⟨227054432521899342170045279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151369621681266228113363519 227054432521899342170045279)
  ·
    refine ⟨340581648782849013255067919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227054432521899342170045279 340581648782849013255067919)
    ·
      refine ⟨510872473174273519882601879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340581648782849013255067919 510872473174273519882601879)
      ·
        refine ⟨766308709761410279823902819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510872473174273519882601879 766308709761410279823902819)
        ·
          refine ⟨1149463064642115419735854229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766308709761410279823902819 1149463064642115419735854229)
          ·
            refine ⟨53881081155099160300118167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1149463064642115419735854229 53881081155099160300118167)
            ·
              refine ⟨80821621732648740450177251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53881081155099160300118167 80821621732648740450177251)
              ·
                refine ⟨121232432598973110675265877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80821621732648740450177251 121232432598973110675265877)
                ·
                  refine ⟨355173142379804035181443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121232432598973110675265877 355173142379804035181443)
                  ·
                    rfl

theorem cell23_6225275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 10].length) (baseStart_6225275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225275 prefixEnd_6225275 := by exact prefixLift 6225275
  have htrace : WordTrace (prefixWord ++ tailWord_6225275) baseStart_6225275 baseEnd_6225275 := by
    simpa [prefixWord, tailWord_6225275, baseEnd_6225275] using wordTrace_append hprefix tailTrace_6225275
  have hstable : (prefixWord ++ tailWord_6225275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225275).length < 2 ^ (prefixWord ++ tailWord_6225275).sum := by decide
  have hdescent : baseEnd_6225275 < baseStart_6225275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225292 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 6]
def baseStart_6225292 : Nat := 118140960795 + 6225292 * 2 ^ 59
def prefixEnd_6225292 : Nat := 4983230072969 + 3 ^ 40 * 6225292 * 2
def baseEnd_6225292 : Nat := 355174112287706972235601

theorem tailTrace_6225292 : CollatzResearch.WordTrace tailWord_6225292 prefixEnd_6225292 355174112287706972235601 := by
  unfold tailWord_6225292
  simp only [CollatzResearch.WordTrace]
  refine ⟨113527526281418877036707065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151370035041891836048942753 113527526281418877036707065)
  ·
    refine ⟨85145644711064157777530299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113527526281418877036707065 85145644711064157777530299)
    ·
      refine ⟨127718467066596236666295449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85145644711064157777530299 127718467066596236666295449)
      ·
        refine ⟨95788850299947177499721587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127718467066596236666295449 95788850299947177499721587)
        ·
          refine ⟨143683275449920766249582381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95788850299947177499721587 143683275449920766249582381)
          ·
            refine ⟨53881228293720287343593393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143683275449920766249582381 53881228293720287343593393)
            ·
              refine ⟨40410921220290215507695045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53881228293720287343593393 40410921220290215507695045)
              ·
                refine ⟨7577047728804415407692821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40410921220290215507695045 7577047728804415407692821)
                ·
                  refine ⟨355174112287706972235601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7577047728804415407692821 355174112287706972235601)
                  ·
                    rfl

theorem cell23_6225292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_6225292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225292 prefixEnd_6225292 := by exact prefixLift 6225292
  have htrace : WordTrace (prefixWord ++ tailWord_6225292) baseStart_6225292 baseEnd_6225292 := by
    simpa [prefixWord, tailWord_6225292, baseEnd_6225292] using wordTrace_append hprefix tailTrace_6225292
  have hstable : (prefixWord ++ tailWord_6225292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225292).length < 2 ^ (prefixWord ++ tailWord_6225292).sum := by decide
  have hdescent : baseEnd_6225292 < baseStart_6225292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225309 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 6]
def baseStart_6225309 : Nat := 118140960795 + 6225309 * 2 ^ 59
def prefixEnd_6225309 : Nat := 4983230072969 + 3 ^ 40 * 6225309 * 2
def baseEnd_6225309 : Nat := 355175082195609909289759

theorem tailTrace_6225309 : CollatzResearch.WordTrace tailWord_6225309 prefixEnd_6225309 355175082195609909289759 := by
  unfold tailWord_6225309
  simp only [CollatzResearch.WordTrace]
  refine ⟨227055672603776165976782981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151370448402517443984521987 227055672603776165976782981)
  ·
    refine ⟨42572938613208031120646809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227055672603776165976782981 42572938613208031120646809)
    ·
      refine ⟨31929703959906023340485107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42572938613208031120646809 31929703959906023340485107)
      ·
        refine ⟨47894555939859035010727661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31929703959906023340485107 47894555939859035010727661)
        ·
          refine ⟨17960458477447138129022873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47894555939859035010727661 17960458477447138129022873)
          ·
            refine ⟨13470343858085353596767155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17960458477447138129022873 13470343858085353596767155)
            ·
              refine ⟨20205515787128030395150733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13470343858085353596767155 20205515787128030395150733)
              ·
                refine ⟨7577068420173011398181525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20205515787128030395150733 7577068420173011398181525)
                ·
                  refine ⟨355175082195609909289759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7577068420173011398181525 355175082195609909289759)
                  ·
                    rfl

theorem cell23_6225309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_6225309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225309 prefixEnd_6225309 := by exact prefixLift 6225309
  have htrace : WordTrace (prefixWord ++ tailWord_6225309) baseStart_6225309 baseEnd_6225309 := by
    simpa [prefixWord, tailWord_6225309, baseEnd_6225309] using wordTrace_append hprefix tailTrace_6225309
  have hstable : (prefixWord ++ tailWord_6225309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225309).length < 2 ^ (prefixWord ++ tailWord_6225309).sum := by decide
  have hdescent : baseEnd_6225309 < baseStart_6225309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225352 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_6225352 : Nat := 118140960795 + 6225352 * 2 ^ 59
def prefixEnd_6225352 : Nat := 4983230072969 + 3 ^ 40 * 6225352 * 2
def baseEnd_6225352 : Nat := 1065532606476210838456711

theorem tailTrace_6225352 : CollatzResearch.WordTrace tailWord_6225352 prefixEnd_6225352 1065532606476210838456711 := by
  unfold tailWord_6225352
  simp only [CollatzResearch.WordTrace]
  refine ⟨113528620471310192160299155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151371493961746922880398873 113528620471310192160299155)
  ·
    refine ⟨170292930706965288240448733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113528620471310192160299155 170292930706965288240448733)
    ·
      refine ⟨63859849015111983090168275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170292930706965288240448733 63859849015111983090168275)
      ·
        refine ⟨95789773522667974635252413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63859849015111983090168275 95789773522667974635252413)
        ·
          refine ⟨35921165071000490488219655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95789773522667974635252413 35921165071000490488219655)
          ·
            refine ⟨53881747606500735732329483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35921165071000490488219655 53881747606500735732329483)
            ·
              refine ⟨80822621409751103598494225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53881747606500735732329483 80822621409751103598494225)
              ·
                refine ⟨60616966057313327698870669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80822621409751103598494225 60616966057313327698870669)
                ·
                  refine ⟨22731362271492497887076501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60616966057313327698870669 22731362271492497887076501)
                  ·
                    refine ⟨1065532606476210838456711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22731362271492497887076501 1065532606476210838456711)
                    ·
                      rfl

theorem cell23_6225352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_6225352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225352 prefixEnd_6225352 := by exact prefixLift 6225352
  have htrace : WordTrace (prefixWord ++ tailWord_6225352) baseStart_6225352 baseEnd_6225352 := by
    simpa [prefixWord, tailWord_6225352, baseEnd_6225352] using wordTrace_append hprefix tailTrace_6225352
  have hstable : (prefixWord ++ tailWord_6225352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225352).length < 2 ^ (prefixWord ++ tailWord_6225352).sum := by decide
  have hdescent : baseEnd_6225352 < baseStart_6225352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225369 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 1, 6]
def baseStart_6225369 : Nat := 118140960795 + 6225369 * 2 ^ 59
def prefixEnd_6225369 : Nat := 4983230072969 + 3 ^ 40 * 6225369 * 2
def baseEnd_6225369 : Nat := 1065535516199919649619185

theorem tailTrace_6225369 : CollatzResearch.WordTrace tailWord_6225369 prefixEnd_6225369 1065535516199919649619185 := by
  unfold tailWord_6225369
  simp only [CollatzResearch.WordTrace]
  refine ⟨227057860983558796223967161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151371907322372530815978107 227057860983558796223967161)
  ·
    refine ⟨170293395737669097167975371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227057860983558796223967161 170293395737669097167975371)
    ·
      refine ⟨255440093606503645751963057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170293395737669097167975371 255440093606503645751963057)
      ·
        refine ⟨191580070204877734313972293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255440093606503645751963057 191580070204877734313972293)
        ·
          refine ⟨35921263163414575183869805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191580070204877734313972293 35921263163414575183869805)
          ·
            refine ⟨13470473686280465693951177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35921263163414575183869805 13470473686280465693951177)
            ·
              refine ⟨10102855264710349270463383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13470473686280465693951177 10102855264710349270463383)
              ·
                refine ⟨15154282897065523905695075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10102855264710349270463383 15154282897065523905695075)
                ·
                  refine ⟨22731424345598285858542613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15154282897065523905695075 22731424345598285858542613)
                  ·
                    refine ⟨1065535516199919649619185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22731424345598285858542613 1065535516199919649619185)
                    ·
                      rfl

theorem cell23_6225369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_6225369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225369 prefixEnd_6225369 := by exact prefixLift 6225369
  have htrace : WordTrace (prefixWord ++ tailWord_6225369) baseStart_6225369 baseEnd_6225369 := by
    simpa [prefixWord, tailWord_6225369, baseEnd_6225369] using wordTrace_append hprefix tailTrace_6225369
  have hstable : (prefixWord ++ tailWord_6225369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225369).length < 2 ^ (prefixWord ++ tailWord_6225369).sum := by decide
  have hdescent : baseEnd_6225369 < baseStart_6225369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225393 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 1, 1, 4]
def baseStart_6225393 : Nat := 118140960795 + 6225393 * 2 ^ 59
def prefixEnd_6225393 : Nat := 4983230072969 + 3 ^ 40 * 6225393 * 2
def baseEnd_6225393 : Nat := 3196618872135466854957445

theorem tailTrace_6225393 : CollatzResearch.WordTrace tailWord_6225393 prefixEnd_6225393 3196618872135466854957445 := by
  unfold tailWord_6225393
  simp only [CollatzResearch.WordTrace]
  refine ⟨227058736335471848322840833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151372490890314565548560555 227058736335471848322840833)
  ·
    refine ⟨170294052251603886242130625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227058736335471848322840833 170294052251603886242130625)
    ·
      refine ⟨127720539188702914681597969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170294052251603886242130625 127720539188702914681597969)
      ·
        refine ⟨95790404391527186011198477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127720539188702914681597969 95790404391527186011198477)
        ·
          refine ⟨35921401646822694754199429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95790404391527186011198477 35921401646822694754199429)
          ·
            refine ⟨6735262808779255266412393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35921401646822694754199429 6735262808779255266412393)
            ·
              refine ⟨5051447106584441449809295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6735262808779255266412393 5051447106584441449809295)
              ·
                refine ⟨7577170659876662174713943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051447106584441449809295 7577170659876662174713943)
                ·
                  refine ⟨11365755989814993262070915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7577170659876662174713943 11365755989814993262070915)
                  ·
                    refine ⟨17048633984722489893106373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11365755989814993262070915 17048633984722489893106373)
                    ·
                      refine ⟨3196618872135466854957445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17048633984722489893106373 3196618872135466854957445)
                      ·
                        rfl

theorem cell23_6225393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_6225393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225393 prefixEnd_6225393 := by exact prefixLift 6225393
  have htrace : WordTrace (prefixWord ++ tailWord_6225393) baseStart_6225393 baseEnd_6225393 := by
    simpa [prefixWord, tailWord_6225393, baseEnd_6225393] using wordTrace_append hprefix tailTrace_6225393
  have hstable : (prefixWord ++ tailWord_6225393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225393).length < 2 ^ (prefixWord ++ tailWord_6225393).sum := by decide
  have hdescent : baseEnd_6225393 < baseStart_6225393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225410 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6225410 : Nat := 118140960795 + 6225410 * 2 ^ 59
def prefixEnd_6225410 : Nat := 4983230072969 + 3 ^ 40 * 6225410 * 2
def baseEnd_6225410 : Nat := 3196627601306593288444867

theorem tailTrace_6225410 : CollatzResearch.WordTrace tailWord_6225410 prefixEnd_6225410 3196627601306593288444867 := by
  unfold tailWord_6225410
  simp only [CollatzResearch.WordTrace]
  refine ⟨56764839094102565056552421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151372904250940173484139789 56764839094102565056552421)
  ·
    refine ⟨10643407330144230948103579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56764839094102565056552421 10643407330144230948103579)
    ·
      refine ⟨15965110995216346422155369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643407330144230948103579 15965110995216346422155369)
      ·
        refine ⟨11973833246412259816616527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15965110995216346422155369 11973833246412259816616527)
        ·
          refine ⟨17960749869618389724924791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973833246412259816616527 17960749869618389724924791)
          ·
            refine ⟨26941124804427584587387187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960749869618389724924791 26941124804427584587387187)
            ·
              refine ⟨40411687206641376881080781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26941124804427584587387187 40411687206641376881080781)
              ·
                refine ⟨15154382702490516330405293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40411687206641376881080781 15154382702490516330405293)
                ·
                  refine ⟨5682893513433943623901985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15154382702490516330405293 5682893513433943623901985)
                  ·
                    refine ⟨4262170135075457717926489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682893513433943623901985 4262170135075457717926489)
                    ·
                      refine ⟨3196627601306593288444867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262170135075457717926489 3196627601306593288444867)
                      ·
                        rfl

theorem cell23_6225410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6225410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225410 prefixEnd_6225410 := by exact prefixLift 6225410
  have htrace : WordTrace (prefixWord ++ tailWord_6225410) baseStart_6225410 baseEnd_6225410 := by
    simpa [prefixWord, tailWord_6225410, baseEnd_6225410] using wordTrace_append hprefix tailTrace_6225410
  have hstable : (prefixWord ++ tailWord_6225410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225410).length < 2 ^ (prefixWord ++ tailWord_6225410).sum := by decide
  have hdescent : baseEnd_6225410 < baseStart_6225410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225438 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6225438 : Nat := 118140960795 + 6225438 * 2 ^ 59
def prefixEnd_6225438 : Nat := 4983230072969 + 3 ^ 40 * 6225438 * 2
def baseEnd_6225438 : Nat := 3196641978764919178894739

theorem tailTrace_6225438 : CollatzResearch.WordTrace tailWord_6225438 prefixEnd_6225438 3196641978764919178894739 := by
  unfold tailWord_6225438
  simp only [CollatzResearch.WordTrace]
  refine ⟨28382547202538602626028621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151373585080205880672152645 28382547202538602626028621)
  ·
    refine ⟨10643455200951975984760733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28382547202538602626028621 10643455200951975984760733)
    ·
      refine ⟨3991295700356990994285275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10643455200951975984760733 3991295700356990994285275)
      ·
        refine ⟨5986943550535486491427913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991295700356990994285275 5986943550535486491427913)
        ·
          refine ⟨4490207662901614868570935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5986943550535486491427913 4490207662901614868570935)
          ·
            refine ⟨6735311494352422302856403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490207662901614868570935 6735311494352422302856403)
            ·
              refine ⟨10102967241528633454284605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6735311494352422302856403 10102967241528633454284605)
              ·
                refine ⟨3788612715573237545356727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10102967241528633454284605 3788612715573237545356727)
                ·
                  refine ⟨5682919073359856318035091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788612715573237545356727 5682919073359856318035091)
                  ·
                    refine ⟨8524378610039784477052637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5682919073359856318035091 8524378610039784477052637)
                    ·
                      refine ⟨3196641978764919178894739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524378610039784477052637 3196641978764919178894739)
                      ·
                        rfl

theorem cell23_6225438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6225438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225438 prefixEnd_6225438 := by exact prefixLift 6225438
  have htrace : WordTrace (prefixWord ++ tailWord_6225438) baseStart_6225438 baseEnd_6225438 := by
    simpa [prefixWord, tailWord_6225438, baseEnd_6225438] using wordTrace_append hprefix tailTrace_6225438
  have hstable : (prefixWord ++ tailWord_6225438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225438).length < 2 ^ (prefixWord ++ tailWord_6225438).sum := by decide
  have hdescent : baseEnd_6225438 < baseStart_6225438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225517 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6225517 : Nat := 118140960795 + 6225517 * 2 ^ 59
def prefixEnd_6225517 : Nat := 4983230072969 + 3 ^ 40 * 6225517 * 2
def baseEnd_6225517 : Nat := 3196682543736624369806875

theorem tailTrace_6225517 : CollatzResearch.WordTrace tailWord_6225517 prefixEnd_6225517 3196682543736624369806875 := by
  unfold tailWord_6225517
  simp only [CollatzResearch.WordTrace]
  refine ⟨227063258987022617500354805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151375505991348411666903203 227063258987022617500354805)
  ·
    refine ⟨21287180530033370390658263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227063258987022617500354805 21287180530033370390658263)
    ·
      refine ⟨31930770795050055585987395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21287180530033370390658263 31930770795050055585987395)
      ·
        refine ⟨47896156192575083378981093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31930770795050055585987395 47896156192575083378981093)
        ·
          refine ⟨8980529286107828133558955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47896156192575083378981093 8980529286107828133558955)
          ·
            refine ⟨13470793929161742200338433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8980529286107828133558955 13470793929161742200338433)
            ·
              refine ⟨10103095446871306650253825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13470793929161742200338433 10103095446871306650253825)
              ·
                refine ⟨7577321585153479987690369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10103095446871306650253825 7577321585153479987690369)
                ·
                  refine ⟨5682991188865109990767777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577321585153479987690369 5682991188865109990767777)
                  ·
                    refine ⟨4262243391648832493075833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682991188865109990767777 4262243391648832493075833)
                    ·
                      refine ⟨3196682543736624369806875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262243391648832493075833 3196682543736624369806875)
                      ·
                        rfl

theorem cell23_6225517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6225517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225517 prefixEnd_6225517 := by exact prefixLift 6225517
  have htrace : WordTrace (prefixWord ++ tailWord_6225517) baseStart_6225517 baseEnd_6225517 := by
    simpa [prefixWord, tailWord_6225517, baseEnd_6225517] using wordTrace_append hprefix tailTrace_6225517
  have hstable : (prefixWord ++ tailWord_6225517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225517).length < 2 ^ (prefixWord ++ tailWord_6225517).sum := by decide
  have hdescent : baseEnd_6225517 < baseStart_6225517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225529 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6225529 : Nat := 118140960795 + 6225529 * 2 ^ 59
def prefixEnd_6225529 : Nat := 4983230072969 + 3 ^ 40 * 6225529 * 2
def baseEnd_6225529 : Nat := 3196688705504478322856819

theorem tailTrace_6225529 : CollatzResearch.WordTrace tailWord_6225529 prefixEnd_6225529 3196688705504478322856819 := by
  unfold tailWord_6225529
  simp only [CollatzResearch.WordTrace]
  refine ⟨227063696662979143549791641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151375797775319429033194427 227063696662979143549791641)
  ·
    refine ⟨170297772497234357662343731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227063696662979143549791641 170297772497234357662343731)
    ·
      refine ⟨255446658745851536493515597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170297772497234357662343731 255446658745851536493515597)
      ·
        refine ⟨95792497029694326185068349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255446658745851536493515597 95792497029694326185068349)
        ·
          refine ⟨35922186386135372319400631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95792497029694326185068349 35922186386135372319400631)
          ·
            refine ⟨53883279579203058479100947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35922186386135372319400631 53883279579203058479100947)
            ·
              refine ⟨80824919368804587718651421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53883279579203058479100947 80824919368804587718651421)
              ·
                refine ⟨30309344763301720394494283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80824919368804587718651421 30309344763301720394494283)
                ·
                  refine ⟨45464017144952580591741425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30309344763301720394494283 45464017144952580591741425)
                  ·
                    refine ⟨34098012858714435443806069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45464017144952580591741425 34098012858714435443806069)
                    ·
                      refine ⟨3196688705504478322856819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34098012858714435443806069 3196688705504478322856819)
                      ·
                        rfl

theorem cell23_6225529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6225529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225529 prefixEnd_6225529 := by exact prefixLift 6225529
  have htrace : WordTrace (prefixWord ++ tailWord_6225529) baseStart_6225529 baseEnd_6225529 := by
    simpa [prefixWord, tailWord_6225529, baseEnd_6225529] using wordTrace_append hprefix tailTrace_6225529
  have hstable : (prefixWord ++ tailWord_6225529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225529).length < 2 ^ (prefixWord ++ tailWord_6225529).sum := by decide
  have hdescent : baseEnd_6225529 < baseStart_6225529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225539 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4]
def baseStart_6225539 : Nat := 118140960795 + 6225539 * 2 ^ 59
def prefixEnd_6225539 : Nat := 4983230072969 + 3 ^ 40 * 6225539 * 2
def baseEnd_6225539 : Nat := 3196693840311023283731773

theorem tailTrace_6225539 : CollatzResearch.WordTrace tailWord_6225539 prefixEnd_6225539 3196693840311023283731773 := by
  unfold tailWord_6225539
  simp only [CollatzResearch.WordTrace]
  refine ⟨227064061392942915257655671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151376040928628610171770447 227064061392942915257655671)
  ·
    refine ⟨340596092089414372886483507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227064061392942915257655671 340596092089414372886483507)
    ·
      refine ⟨510894138134121559329725261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340596092089414372886483507 510894138134121559329725261)
      ·
        refine ⟨191585301800295584748646973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510894138134121559329725261 191585301800295584748646973)
        ·
          refine ⟨71844488175110844280742615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191585301800295584748646973 71844488175110844280742615)
          ·
            refine ⟨107766732262666266421113923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71844488175110844280742615 107766732262666266421113923)
            ·
              refine ⟨161650098393999399631670885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107766732262666266421113923 161650098393999399631670885)
              ·
                refine ⟨30309393448874887430938291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161650098393999399631670885 30309393448874887430938291)
                ·
                  refine ⟨45464090173312331146407437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30309393448874887430938291 45464090173312331146407437)
                  ·
                    refine ⟨17049033814992124179902789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45464090173312331146407437 17049033814992124179902789)
                    ·
                      refine ⟨3196693840311023283731773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17049033814992124179902789 3196693840311023283731773)
                      ·
                        rfl

theorem cell23_6225539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_6225539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225539 prefixEnd_6225539 := by exact prefixLift 6225539
  have htrace : WordTrace (prefixWord ++ tailWord_6225539) baseStart_6225539 baseEnd_6225539 := by
    simpa [prefixWord, tailWord_6225539, baseEnd_6225539] using wordTrace_append hprefix tailTrace_6225539
  have hstable : (prefixWord ++ tailWord_6225539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225539).length < 2 ^ (prefixWord ++ tailWord_6225539).sum := by decide
  have hdescent : baseEnd_6225539 < baseStart_6225539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225583 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 1, 4]
def baseStart_6225583 : Nat := 118140960795 + 6225583 * 2 ^ 59
def prefixEnd_6225583 : Nat := 4983230072969 + 3 ^ 40 * 6225583 * 2
def baseEnd_6225583 : Nat := 1065572144486607037193857

theorem tailTrace_6225583 : CollatzResearch.WordTrace tailWord_6225583 prefixEnd_6225583 1065572144486607037193857 := by
  unfold tailWord_6225583
  simp only [CollatzResearch.WordTrace]
  refine ⟨227065666204783510772257403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151377110803189007181504935 227065666204783510772257403)
  ·
    refine ⟨340598499307175266158386105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227065666204783510772257403 340598499307175266158386105)
    ·
      refine ⟨255448874480381449618789579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340598499307175266158386105 255448874480381449618789579)
      ·
        refine ⟨383173311720572174428184369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255448874480381449618789579 383173311720572174428184369)
        ·
          refine ⟨287379983790429130821138277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383173311720572174428184369 287379983790429130821138277)
          ·
            refine ⟨53883746960705462028963427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287379983790429130821138277 53883746960705462028963427)
            ·
              refine ⟨80825620441058193043445141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53883746960705462028963427 80825620441058193043445141)
              ·
                refine ⟨3788700958174602798911491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80825620441058193043445141 3788700958174602798911491)
                ·
                  refine ⟨5683051437261904198367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788700958174602798911491 5683051437261904198367237)
                  ·
                    refine ⟨1065572144486607037193857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683051437261904198367237 1065572144486607037193857)
                    ·
                      rfl

theorem cell23_6225583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 4].length) (baseStart_6225583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225583 prefixEnd_6225583 := by exact prefixLift 6225583
  have htrace : WordTrace (prefixWord ++ tailWord_6225583) baseStart_6225583 baseEnd_6225583 := by
    simpa [prefixWord, tailWord_6225583, baseEnd_6225583] using wordTrace_append hprefix tailTrace_6225583
  have hstable : (prefixWord ++ tailWord_6225583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225583).length < 2 ^ (prefixWord ++ tailWord_6225583).sum := by decide
  have hdescent : baseEnd_6225583 < baseStart_6225583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225599 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_6225599 : Nat := 118140960795 + 6225599 * 2 ^ 59
def prefixEnd_6225599 : Nat := 4983230072969 + 3 ^ 40 * 6225599 * 2
def baseEnd_6225599 : Nat := 3196724649150293048981497

theorem tailTrace_6225599 : CollatzResearch.WordTrace tailWord_6225599 prefixEnd_6225599 3196724649150293048981497 := by
  unfold tailWord_6225599
  simp only [CollatzResearch.WordTrace]
  refine ⟨227066249772725545504839851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151377499848483697003226567 227066249772725545504839851)
  ·
    refine ⟨340599374659088318257259777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227066249772725545504839851 340599374659088318257259777)
    ·
      refine ⟨255449530994316238692944833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340599374659088318257259777 255449530994316238692944833)
      ·
        refine ⟨191587148245737179019708625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255449530994316238692944833 191587148245737179019708625)
        ·
          refine ⟨143690361184302884264781469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191587148245737179019708625 143690361184302884264781469)
          ·
            refine ⟨53883885444113581599293051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143690361184302884264781469 53883885444113581599293051)
            ·
              refine ⟨80825828166170372398939577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53883885444113581599293051 80825828166170372398939577)
              ·
                refine ⟨60619371124627779299204683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80825828166170372398939577 60619371124627779299204683)
                ·
                  refine ⟨90929056686941668948807025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60619371124627779299204683 90929056686941668948807025)
                  ·
                    refine ⟨68196792515206251711605269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90929056686941668948807025 68196792515206251711605269)
                    ·
                      refine ⟨3196724649150293048981497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68196792515206251711605269 3196724649150293048981497)
                      ·
                        rfl

theorem cell23_6225599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_6225599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225599 prefixEnd_6225599 := by exact prefixLift 6225599
  have htrace : WordTrace (prefixWord ++ tailWord_6225599) baseStart_6225599 baseEnd_6225599 := by
    simpa [prefixWord, tailWord_6225599, baseEnd_6225599] using wordTrace_append hprefix tailTrace_6225599
  have hstable : (prefixWord ++ tailWord_6225599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225599).length < 2 ^ (prefixWord ++ tailWord_6225599).sum := by decide
  have hdescent : baseEnd_6225599 < baseStart_6225599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225613 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 8]
def baseStart_6225613 : Nat := 118140960795 + 6225613 * 2 ^ 59
def prefixEnd_6225613 : Nat := 4983230072969 + 3 ^ 40 * 6225613 * 2
def baseEnd_6225613 : Nat := 355192426431050666022937

theorem tailTrace_6225613 : CollatzResearch.WordTrace tailWord_6225613 prefixEnd_6225613 355192426431050666022937 := by
  unfold tailWord_6225613
  simp only [CollatzResearch.WordTrace]
  refine ⟨227066760394674825895849493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151377840263116550597232995 227066760394674825895849493)
  ·
    refine ⟨10643754393500382463867945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227066760394674825895849493 10643754393500382463867945)
    ·
      refine ⟨7982815795125286847900959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10643754393500382463867945 7982815795125286847900959)
      ·
        refine ⟨11974223692687930271851439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982815795125286847900959 11974223692687930271851439)
        ·
          refine ⟨17961335539031895407777159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11974223692687930271851439 17961335539031895407777159)
          ·
            refine ⟨26942003308547843111665739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961335539031895407777159 26942003308547843111665739)
            ·
              refine ⟨40413004962821764667498609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26942003308547843111665739 40413004962821764667498609)
              ·
                refine ⟨30309753722116323500623957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40413004962821764667498609 30309753722116323500623957)
                ·
                  refine ⟨355192426431050666022937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30309753722116323500623957 355192426431050666022937)
                  ·
                    rfl

theorem cell23_6225613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_6225613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225613 prefixEnd_6225613 := by exact prefixLift 6225613
  have htrace : WordTrace (prefixWord ++ tailWord_6225613) baseStart_6225613 baseEnd_6225613 := by
    simpa [prefixWord, tailWord_6225613, baseEnd_6225613] using wordTrace_append hprefix tailTrace_6225613
  have hstable : (prefixWord ++ tailWord_6225613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225613).length < 2 ^ (prefixWord ++ tailWord_6225613).sum := by decide
  have hdescent : baseEnd_6225613 < baseStart_6225613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225640 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_6225640 : Nat := 118140960795 + 6225640 * 2 ^ 59
def prefixEnd_6225640 : Nat := 4983230072969 + 3 ^ 40 * 6225640 * 2
def baseEnd_6225640 : Nat := 3196745701857127388568809

theorem tailTrace_6225640 : CollatzResearch.WordTrace tailWord_6225640 prefixEnd_6225640 3196745701857127388568809 := by
  unfold tailWord_6225640
  simp only [CollatzResearch.WordTrace]
  refine ⟨113533872582788504753541187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151378496777051339671388249 113533872582788504753541187)
  ·
    refine ⟨170300808874182757130311781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113533872582788504753541187 170300808874182757130311781)
    ·
      refine ⟨31931401663909266961933459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170300808874182757130311781 31931401663909266961933459)
      ·
        refine ⟨47897102495863900442900189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31931401663909266961933459 47897102495863900442900189)
        ·
          refine ⟨17961413435948962666087571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47897102495863900442900189 17961413435948962666087571)
          ·
            refine ⟨26942120153923443999131357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961413435948962666087571 26942120153923443999131357)
            ·
              refine ⟨10103295057721291499674259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26942120153923443999131357 10103295057721291499674259)
              ·
                refine ⟨15154942586581937249511389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10103295057721291499674259 15154942586581937249511389)
                ·
                  refine ⟨5683103469968226468566771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15154942586581937249511389 5683103469968226468566771)
                  ·
                    refine ⟨8524655204952339702850157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683103469968226468566771 8524655204952339702850157)
                    ·
                      refine ⟨3196745701857127388568809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524655204952339702850157 3196745701857127388568809)
                      ·
                        rfl

theorem cell23_6225640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_6225640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225640 prefixEnd_6225640 := by exact prefixLift 6225640
  have htrace : WordTrace (prefixWord ++ tailWord_6225640) baseStart_6225640 baseEnd_6225640 := by
    simpa [prefixWord, tailWord_6225640, baseEnd_6225640] using wordTrace_append hprefix tailTrace_6225640
  have hstable : (prefixWord ++ tailWord_6225640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225640).length < 2 ^ (prefixWord ++ tailWord_6225640).sum := by decide
  have hdescent : baseEnd_6225640 < baseStart_6225640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225656 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 6, 4]
def baseStart_6225656 : Nat := 118140960795 + 6225656 * 2 ^ 59
def prefixEnd_6225656 : Nat := 4983230072969 + 3 ^ 40 * 6225656 * 2
def baseEnd_6225656 : Nat := 1065584639182533108656245

theorem tailTrace_6225656 : CollatzResearch.WordTrace tailWord_6225656 prefixEnd_6225656 1065584639182533108656245 := by
  unfold tailWord_6225656
  simp only [CollatzResearch.WordTrace]
  refine ⟨113534164366759522119832411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151378885822346029493109881 113534164366759522119832411)
  ·
    refine ⟨170301246550139283179748617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113534164366759522119832411 170301246550139283179748617)
    ·
      refine ⟨127725934912604462384811463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170301246550139283179748617 127725934912604462384811463)
      ·
        refine ⟨191588902368906693577217195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127725934912604462384811463 191588902368906693577217195)
        ·
          refine ⟨287383353553360040365825793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191588902368906693577217195 287383353553360040365825793)
          ·
            refine ⟨215537515165020030274369345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287383353553360040365825793 215537515165020030274369345)
            ·
              refine ⟨161653136373765022705777009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215537515165020030274369345 161653136373765022705777009)
              ·
                refine ⟨121239852280323767029332757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161653136373765022705777009 121239852280323767029332757)
                ·
                  refine ⟨5683118075640176579499973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121239852280323767029332757 5683118075640176579499973)
                  ·
                    refine ⟨1065584639182533108656245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683118075640176579499973 1065584639182533108656245)
                    ·
                      rfl

theorem cell23_6225656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_6225656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225656 prefixEnd_6225656 := by exact prefixLift 6225656
  have htrace : WordTrace (prefixWord ++ tailWord_6225656) baseStart_6225656 baseEnd_6225656 := by
    simpa [prefixWord, tailWord_6225656, baseEnd_6225656] using wordTrace_append hprefix tailTrace_6225656
  have hstable : (prefixWord ++ tailWord_6225656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225656).length < 2 ^ (prefixWord ++ tailWord_6225656).sum := by decide
  have hdescent : baseEnd_6225656 < baseStart_6225656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225663 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 4]
def baseStart_6225663 : Nat := 118140960795 + 6225663 * 2 ^ 59
def prefixEnd_6225663 : Nat := 4983230072969 + 3 ^ 40 * 6225663 * 2
def baseEnd_6225663 : Nat := 3196757511912180798581203

theorem tailTrace_6225663 : CollatzResearch.WordTrace tailWord_6225663 prefixEnd_6225663 3196757511912180798581203 := by
  unfold tailWord_6225663
  simp only [CollatzResearch.WordTrace]
  refine ⟨227068584044493684435169643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151379056029662456290113095 227068584044493684435169643)
  ·
    refine ⟨340602876066740526652754465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227068584044493684435169643 340602876066740526652754465)
    ·
      refine ⟨255452157050055394989565849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340602876066740526652754465 255452157050055394989565849)
      ·
        refine ⟨191589117787541546242174387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255452157050055394989565849 191589117787541546242174387)
        ·
          refine ⟨287383676681312319363261581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191589117787541546242174387 287383676681312319363261581)
          ·
            refine ⟨107768878755492119761223093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287383676681312319363261581 107768878755492119761223093)
            ·
              refine ⟨10103332383327386227614665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107768878755492119761223093 10103332383327386227614665)
              ·
                refine ⟨7577499287495539670710999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10103332383327386227614665 7577499287495539670710999)
                ·
                  refine ⟨11366248931243309506066499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7577499287495539670710999 11366248931243309506066499)
                  ·
                    refine ⟨17049373396864964259099749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11366248931243309506066499 17049373396864964259099749)
                    ·
                      refine ⟨3196757511912180798581203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17049373396864964259099749 3196757511912180798581203)
                      ·
                        rfl

theorem cell23_6225663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_6225663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225663 prefixEnd_6225663 := by exact prefixLift 6225663
  have htrace : WordTrace (prefixWord ++ tailWord_6225663) baseStart_6225663 baseEnd_6225663 := by
    simpa [prefixWord, tailWord_6225663, baseEnd_6225663] using wordTrace_append hprefix tailTrace_6225663
  have hstable : (prefixWord ++ tailWord_6225663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225663).length < 2 ^ (prefixWord ++ tailWord_6225663).sum := by decide
  have hdescent : baseEnd_6225663 < baseStart_6225663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225676 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6225676 : Nat := 118140960795 + 6225676 * 2 ^ 59
def prefixEnd_6225676 : Nat := 4983230072969 + 3 ^ 40 * 6225676 * 2
def baseEnd_6225676 : Nat := 3196764187160689247718643

theorem tailTrace_6225676 : CollatzResearch.WordTrace tailWord_6225676 prefixEnd_6225676 3196764187160689247718643 := by
  unfold tailWord_6225676
  simp only [CollatzResearch.WordTrace]
  refine ⟨113534529096723293827696441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151379372128964391770261921 113534529096723293827696441)
  ·
    refine ⟨85150896822542470370772331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113534529096723293827696441 85150896822542470370772331)
    ·
      refine ⟨127726345233813705556158497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85150896822542470370772331 127726345233813705556158497)
      ·
        refine ⟨95794758925360279167118873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127726345233813705556158497 95794758925360279167118873)
        ·
          refine ⟨71846069194020209375339155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95794758925360279167118873 71846069194020209375339155)
          ·
            refine ⟨107769103791030314063008733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71846069194020209375339155 107769103791030314063008733)
            ·
              refine ⟨40413413921636367773628275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107769103791030314063008733 40413413921636367773628275)
              ·
                refine ⟨60620120882454551660442413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40413413921636367773628275 60620120882454551660442413)
                ·
                  refine ⟨22732545330920456872665905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60620120882454551660442413 22732545330920456872665905)
                  ·
                    refine ⟨17049408998190342654499429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22732545330920456872665905 17049408998190342654499429)
                    ·
                      refine ⟨3196764187160689247718643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17049408998190342654499429 3196764187160689247718643)
                      ·
                        rfl

theorem cell23_6225676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6225676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225676 prefixEnd_6225676 := by exact prefixLift 6225676
  have htrace : WordTrace (prefixWord ++ tailWord_6225676) baseStart_6225676 baseEnd_6225676 := by
    simpa [prefixWord, tailWord_6225676, baseEnd_6225676] using wordTrace_append hprefix tailTrace_6225676
  have hstable : (prefixWord ++ tailWord_6225676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225676).length < 2 ^ (prefixWord ++ tailWord_6225676).sum := by decide
  have hdescent : baseEnd_6225676 < baseStart_6225676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225690 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_6225690 : Nat := 118140960795 + 6225690 * 2 ^ 59
def prefixEnd_6225690 : Nat := 4983230072969 + 3 ^ 40 * 6225690 * 2
def baseEnd_6225690 : Nat := 1065590458629950730981193

theorem tailTrace_6225690 : CollatzResearch.WordTrace tailWord_6225690 prefixEnd_6225690 1065590458629950730981193 := by
  unfold tailWord_6225690
  simp only [CollatzResearch.WordTrace]
  refine ⟨56767392203848967011600631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151379712543597245364268349 56767392203848967011600631)
  ·
    refine ⟨85151088305773450517400947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56767392203848967011600631 85151088305773450517400947)
    ·
      refine ⟨127726632458660175776101421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85151088305773450517400947 127726632458660175776101421)
      ·
        refine ⟨47897487171997565916038033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127726632458660175776101421 47897487171997565916038033)
        ·
          refine ⟨35923115378998174437028525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47897487171997565916038033 35923115378998174437028525)
          ·
            refine ⟨13471168267124315413885697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35923115378998174437028525 13471168267124315413885697)
            ·
              refine ⟨10103376200343236560414273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13471168267124315413885697 10103376200343236560414273)
              ·
                refine ⟨7577532150257427420310705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10103376200343236560414273 7577532150257427420310705)
                ·
                  refine ⟨5683149112693070565233029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577532150257427420310705 5683149112693070565233029)
                  ·
                    refine ⟨1065590458629950730981193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683149112693070565233029 1065590458629950730981193)
                    ·
                      rfl

theorem cell23_6225690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_6225690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225690 prefixEnd_6225690 := by exact prefixLift 6225690
  have htrace : WordTrace (prefixWord ++ tailWord_6225690) baseStart_6225690 baseEnd_6225690 := by
    simpa [prefixWord, tailWord_6225690, baseEnd_6225690] using wordTrace_append hprefix tailTrace_6225690
  have hstable : (prefixWord ++ tailWord_6225690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225690).length < 2 ^ (prefixWord ++ tailWord_6225690).sum := by decide
  have hdescent : baseEnd_6225690 < baseStart_6225690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225713 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_6225713 : Nat := 118140960795 + 6225713 * 2 ^ 59
def prefixEnd_6225713 : Nat := 4983230072969 + 3 ^ 40 * 6225713 * 2
def baseEnd_6225713 : Nat := 3196783185944905602955973

theorem tailTrace_6225713 : CollatzResearch.WordTrace tailWord_6225713 prefixEnd_6225713 3196783185944905602955973 := by
  unfold tailWord_6225713
  simp only [CollatzResearch.WordTrace]
  refine ⟨227070407694312542974489793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151380271796208361982993195 227070407694312542974489793)
  ·
    refine ⟨170302805770734407230867345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227070407694312542974489793 170302805770734407230867345)
    ·
      refine ⟨127727104328050805423150509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170302805770734407230867345 127727104328050805423150509)
      ·
        refine ⟨47897664123019052033681441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127727104328050805423150509 47897664123019052033681441)
        ·
          refine ⟨35923248092264289025261081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47897664123019052033681441 35923248092264289025261081)
          ·
            refine ⟨26942436069198216768945811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35923248092264289025261081 26942436069198216768945811)
            ·
              refine ⟨40413654103797325153418717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26942436069198216768945811 40413654103797325153418717)
              ·
                refine ⟨15155120288923996932532019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40413654103797325153418717 15155120288923996932532019)
                ·
                  refine ⟨22732680433385995398798029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15155120288923996932532019 22732680433385995398798029)
                  ·
                    refine ⟨8524755162519748274549261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22732680433385995398798029 8524755162519748274549261)
                    ·
                      refine ⟨3196783185944905602955973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524755162519748274549261 3196783185944905602955973)
                      ·
                        rfl

theorem cell23_6225713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_6225713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225713 prefixEnd_6225713 := by exact prefixLift 6225713
  have htrace : WordTrace (prefixWord ++ tailWord_6225713) baseStart_6225713 baseEnd_6225713 := by
    simpa [prefixWord, tailWord_6225713, baseEnd_6225713] using wordTrace_append hprefix tailTrace_6225713
  have hstable : (prefixWord ++ tailWord_6225713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225713).length < 2 ^ (prefixWord ++ tailWord_6225713).sum := by decide
  have hdescent : baseEnd_6225713 < baseStart_6225713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225734 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6225734 : Nat := 118140960795 + 6225734 * 2 ^ 59
def prefixEnd_6225734 : Nat := 4983230072969 + 3 ^ 40 * 6225734 * 2
def baseEnd_6225734 : Nat := 3196793969038650020793377

theorem tailTrace_6225734 : CollatzResearch.WordTrace tailWord_6225734 prefixEnd_6225734 3196793969038650020793377 := by
  unfold tailWord_6225734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7095974175851139486281383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151380782418157642374002837 7095974175851139486281383)
  ·
    refine ⟨10643961263776709229422075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7095974175851139486281383 10643961263776709229422075)
    ·
      refine ⟨15965941895665063844133113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643961263776709229422075 15965941895665063844133113)
      ·
        refine ⟨11974456421748797883099835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15965941895665063844133113 11974456421748797883099835)
        ·
          refine ⟨17961684632623196824649753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11974456421748797883099835 17961684632623196824649753)
          ·
            refine ⟨13471263474467397618487315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17961684632623196824649753 13471263474467397618487315)
            ·
              refine ⟨20206895211701096427730973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13471263474467397618487315 20206895211701096427730973)
              ·
                refine ⟨7577585704387911160399115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20206895211701096427730973 7577585704387911160399115)
                ·
                  refine ⟨11366378556581866740598673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7577585704387911160399115 11366378556581866740598673)
                  ·
                    refine ⟨8524783917436400055449005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11366378556581866740598673 8524783917436400055449005)
                    ·
                      refine ⟨3196793969038650020793377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524783917436400055449005 3196793969038650020793377)
                      ·
                        rfl

theorem cell23_6225734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6225734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225734 prefixEnd_6225734 := by exact prefixLift 6225734
  have htrace : WordTrace (prefixWord ++ tailWord_6225734) baseStart_6225734 baseEnd_6225734 := by
    simpa [prefixWord, tailWord_6225734, baseEnd_6225734] using wordTrace_append hprefix tailTrace_6225734
  have hstable : (prefixWord ++ tailWord_6225734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225734).length < 2 ^ (prefixWord ++ tailWord_6225734).sum := by decide
  have hdescent : baseEnd_6225734 < baseStart_6225734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225764 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_6225764 : Nat := 118140960795 + 6225764 * 2 ^ 59
def prefixEnd_6225764 : Nat := 4983230072969 + 3 ^ 40 * 6225764 * 2
def baseEnd_6225764 : Nat := 3196809373458284903418239

theorem tailTrace_6225764 : CollatzResearch.WordTrace tailWord_6225764 prefixEnd_6225764 3196809373458284903418239 := by
  unfold tailWord_6225764
  simp only [CollatzResearch.WordTrace]
  refine ⟨113536133908563889342298173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151381511878085185789730897 113536133908563889342298173)
  ·
    refine ⟨42576050215711458503361815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113536133908563889342298173 42576050215711458503361815)
    ·
      refine ⟨63864075323567187755042723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42576050215711458503361815 63864075323567187755042723)
      ·
        refine ⟨95796112985350781632564085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63864075323567187755042723 95796112985350781632564085)
        ·
          refine ⟨8980885592376635778052883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95796112985350781632564085 8980885592376635778052883)
          ·
            refine ⟨13471328388564953667079325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8980885592376635778052883 13471328388564953667079325)
            ·
              refine ⟨5051748145711857625154747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13471328388564953667079325 5051748145711857625154747)
              ·
                refine ⟨7577622218567786437732121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051748145711857625154747 7577622218567786437732121)
                ·
                  refine ⟨5683216663925839828299091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577622218567786437732121 5683216663925839828299091)
                  ·
                    refine ⟨8524824995888759742448637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683216663925839828299091 8524824995888759742448637)
                    ·
                      refine ⟨3196809373458284903418239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524824995888759742448637 3196809373458284903418239)
                      ·
                        rfl

theorem cell23_6225764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_6225764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225764 prefixEnd_6225764 := by exact prefixLift 6225764
  have htrace : WordTrace (prefixWord ++ tailWord_6225764) baseStart_6225764 baseEnd_6225764 := by
    simpa [prefixWord, tailWord_6225764, baseEnd_6225764] using wordTrace_append hprefix tailTrace_6225764
  have hstable : (prefixWord ++ tailWord_6225764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225764).length < 2 ^ (prefixWord ++ tailWord_6225764).sum := by decide
  have hdescent : baseEnd_6225764 < baseStart_6225764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225773 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6225773 : Nat := 118140960795 + 6225773 * 2 ^ 59
def prefixEnd_6225773 : Nat := 4983230072969 + 3 ^ 40 * 6225773 * 2
def baseEnd_6225773 : Nat := 3196813994784175368205697

theorem tailTrace_6225773 : CollatzResearch.WordTrace tailWord_6225773 prefixEnd_6225773 3196813994784175368205697 := by
  unfold tailWord_6225773
  simp only [CollatzResearch.WordTrace]
  refine ⟨227072596074095173221673973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151381730716063448814449315 227072596074095173221673973)
  ·
    refine ⟨21288055881946422489531935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227072596074095173221673973 21288055881946422489531935)
    ·
      refine ⟨31932083822919633734297903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21288055881946422489531935 31932083822919633734297903)
      ·
        refine ⟨47898125734379450601446855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31932083822919633734297903 47898125734379450601446855)
        ·
          refine ⟨71847188601569175902170283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47898125734379450601446855 71847188601569175902170283)
          ·
            refine ⟨107770782902353763853255425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71847188601569175902170283 107770782902353763853255425)
            ·
              refine ⟨80828087176765322889941569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107770782902353763853255425 80828087176765322889941569)
              ·
                refine ⟨60621065382573992167456177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80828087176765322889941569 60621065382573992167456177)
                ·
                  refine ⟨45465799036930494125592133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60621065382573992167456177 45465799036930494125592133)
                  ·
                    refine ⟨8524837319424467648548525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45465799036930494125592133 8524837319424467648548525)
                    ·
                      refine ⟨3196813994784175368205697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524837319424467648548525 3196813994784175368205697)
                      ·
                        rfl

theorem cell23_6225773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6225773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225773 prefixEnd_6225773 := by exact prefixLift 6225773
  have htrace : WordTrace (prefixWord ++ tailWord_6225773) baseStart_6225773 baseEnd_6225773 := by
    simpa [prefixWord, tailWord_6225773, baseEnd_6225773] using wordTrace_append hprefix tailTrace_6225773
  have hstable : (prefixWord ++ tailWord_6225773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225773).length < 2 ^ (prefixWord ++ tailWord_6225773).sum := by decide
  have hdescent : baseEnd_6225773 < baseStart_6225773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225774 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_6225774 : Nat := 118140960795 + 6225774 * 2 ^ 59
def prefixEnd_6225774 : Nat := 4983230072969 + 3 ^ 40 * 6225774 * 2
def baseEnd_6225774 : Nat := 3196814508264829864293193

theorem tailTrace_6225774 : CollatzResearch.WordTrace tailWord_6225774 prefixEnd_6225774 3196814508264829864293193 := by
  unfold tailWord_6225774
  simp only [CollatzResearch.WordTrace]
  refine ⟨28384079068386443799057547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151381755031394366928306917 28384079068386443799057547)
  ·
    refine ⟨42576118602579665698586321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28384079068386443799057547 42576118602579665698586321)
    ·
      refine ⟨31932088951934749273939741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42576118602579665698586321 31932088951934749273939741)
      ·
        refine ⟨11974533356975530977727403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31932088951934749273939741 11974533356975530977727403)
        ·
          refine ⟨17961800035463296466591105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11974533356975530977727403 17961800035463296466591105)
          ·
            refine ⟨13471350026597472349943329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17961800035463296466591105 13471350026597472349943329)
            ·
              refine ⟨10103512519948104262457497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13471350026597472349943329 10103512519948104262457497)
              ·
                refine ⟨7577634389961078196843123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10103512519948104262457497 7577634389961078196843123)
                ·
                  refine ⟨11366451584941617295264685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7577634389961078196843123 11366451584941617295264685)
                  ·
                    refine ⟨4262419344353106485724257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11366451584941617295264685 4262419344353106485724257)
                    ·
                      refine ⟨3196814508264829864293193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262419344353106485724257 3196814508264829864293193)
                      ·
                        rfl

theorem cell23_6225774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_6225774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225774 prefixEnd_6225774 := by exact prefixLift 6225774
  have htrace : WordTrace (prefixWord ++ tailWord_6225774) baseStart_6225774 baseEnd_6225774 := by
    simpa [prefixWord, tailWord_6225774, baseEnd_6225774] using wordTrace_append hprefix tailTrace_6225774
  have hstable : (prefixWord ++ tailWord_6225774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225774).length < 2 ^ (prefixWord ++ tailWord_6225774).sum := by decide
  have hdescent : baseEnd_6225774 < baseStart_6225774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225790 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6225790 : Nat := 118140960795 + 6225790 * 2 ^ 59
def prefixEnd_6225790 : Nat := 4983230072969 + 3 ^ 40 * 6225790 * 2
def baseEnd_6225790 : Nat := 3196822723955301801693119

theorem tailTrace_6225790 : CollatzResearch.WordTrace tailWord_6225790 prefixEnd_6225790 3196822723955301801693119 := by
  unfold tailWord_6225790
  simp only [CollatzResearch.WordTrace]
  refine ⟨28384152014379198140630353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151382144076689056750028549 28384152014379198140630353)
  ·
    refine ⟨21288114010784398605472765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28384152014379198140630353 21288114010784398605472765)
    ·
      refine ⟨7983042754044149477052287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21288114010784398605472765 7983042754044149477052287)
      ·
        refine ⟨11974564131066224215578431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7983042754044149477052287 11974564131066224215578431)
        ·
          refine ⟨17961846196599336323367647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11974564131066224215578431 17961846196599336323367647)
          ·
            refine ⟨26942769294899004485051471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961846196599336323367647 26942769294899004485051471)
            ·
              refine ⟨40414153942348506727577207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26942769294899004485051471 40414153942348506727577207)
              ·
                refine ⟨60621230913522760091365811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40414153942348506727577207 60621230913522760091365811)
                ·
                  refine ⟨90931846370284140137048717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60621230913522760091365811 90931846370284140137048717)
                  ·
                    refine ⟨34099442388856552551393269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90931846370284140137048717 34099442388856552551393269)
                    ·
                      refine ⟨3196822723955301801693119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34099442388856552551393269 3196822723955301801693119)
                      ·
                        rfl

theorem cell23_6225790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6225790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225790 prefixEnd_6225790 := by exact prefixLift 6225790
  have htrace : WordTrace (prefixWord ++ tailWord_6225790) baseStart_6225790 baseEnd_6225790 := by
    simpa [prefixWord, tailWord_6225790, baseEnd_6225790] using wordTrace_append hprefix tailTrace_6225790
  have hstable : (prefixWord ++ tailWord_6225790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225790).length < 2 ^ (prefixWord ++ tailWord_6225790).sum := by decide
  have hdescent : baseEnd_6225790 < baseStart_6225790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225810 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_6225810 : Nat := 118140960795 + 6225810 * 2 ^ 59
def prefixEnd_6225810 : Nat := 4983230072969 + 3 ^ 40 * 6225810 * 2
def baseEnd_6225810 : Nat := 355203665952043524827003

theorem tailTrace_6225810 : CollatzResearch.WordTrace tailWord_6225810 prefixEnd_6225810 355203665952043524827003 := by
  unfold tailWord_6225810
  simp only [CollatzResearch.WordTrace]
  refine ⟨56768486393740282135192721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151382630383307419027180589 56768486393740282135192721)
  ·
    refine ⟨42576364795305211601394541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56768486393740282135192721 42576364795305211601394541)
    ·
      refine ⟨15966136798239454350522953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42576364795305211601394541 15966136798239454350522953)
      ·
        refine ⟨11974602598679590762892215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15966136798239454350522953 11974602598679590762892215)
        ·
          refine ⟨17961903898019386144338323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11974602598679590762892215 17961903898019386144338323)
          ·
            refine ⟨26942855847029079216507485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961903898019386144338323 26942855847029079216507485)
            ·
              refine ⟨10103570942635904706190307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26942855847029079216507485 10103570942635904706190307)
              ·
                refine ⟨15155356413953857059285461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10103570942635904706190307 15155356413953857059285461)
                ·
                  refine ⟨355203665952043524827003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15155356413953857059285461 355203665952043524827003)
                  ·
                    rfl

theorem cell23_6225810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_6225810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225810 prefixEnd_6225810 := by exact prefixLift 6225810
  have htrace : WordTrace (prefixWord ++ tailWord_6225810) baseStart_6225810 baseEnd_6225810 := by
    simpa [prefixWord, tailWord_6225810, baseEnd_6225810] using wordTrace_append hprefix tailTrace_6225810
  have hstable : (prefixWord ++ tailWord_6225810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225810).length < 2 ^ (prefixWord ++ tailWord_6225810).sum := by decide
  have hdescent : baseEnd_6225810 < baseStart_6225810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225821 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_6225821 : Nat := 118140960795 + 6225821 * 2 ^ 59
def prefixEnd_6225821 : Nat := 4983230072969 + 3 ^ 40 * 6225821 * 2
def baseEnd_6225821 : Nat := 3196838641855591180405477

theorem tailTrace_6225821 : CollatzResearch.WordTrace tailWord_6225821 prefixEnd_6225821 3196838641855591180405477 := by
  unfold tailWord_6225821
  simp only [CollatzResearch.WordTrace]
  refine ⟨227074346777921277419421317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151382897851947518279614211 227074346777921277419421317)
  ·
    refine ⟨42576440020860239516141497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227074346777921277419421317 42576440020860239516141497)
    ·
      refine ⟨31932330015645179637106123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42576440020860239516141497 31932330015645179637106123)
      ·
        refine ⟨47898495023467769455659185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31932330015645179637106123 47898495023467769455659185)
        ·
          refine ⟨35923871267600827091744389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47898495023467769455659185 35923871267600827091744389)
          ·
            refine ⟨6735725862675155079702073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35923871267600827091744389 6735725862675155079702073)
            ·
              refine ⟨5051794397006366309776555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6735725862675155079702073 5051794397006366309776555)
              ·
                refine ⟨7577691595509549464664833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051794397006366309776555 7577691595509549464664833)
                ·
                  refine ⟨5683268696632162098498625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577691595509549464664833 5683268696632162098498625)
                  ·
                    refine ⟨4262451522474121573873969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5683268696632162098498625 4262451522474121573873969)
                    ·
                      refine ⟨3196838641855591180405477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262451522474121573873969 3196838641855591180405477)
                      ·
                        rfl

theorem cell23_6225821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_6225821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225821 prefixEnd_6225821 := by exact prefixLift 6225821
  have htrace : WordTrace (prefixWord ++ tailWord_6225821) baseStart_6225821 baseEnd_6225821 := by
    simpa [prefixWord, tailWord_6225821, baseEnd_6225821] using wordTrace_append hprefix tailTrace_6225821
  have hstable : (prefixWord ++ tailWord_6225821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225821).length < 2 ^ (prefixWord ++ tailWord_6225821).sum := by decide
  have hdescent : baseEnd_6225821 < baseStart_6225821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225863 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_6225863 : Nat := 118140960795 + 6225863 * 2 ^ 59
def prefixEnd_6225863 : Nat := 4983230072969 + 3 ^ 40 * 6225863 * 2
def baseEnd_6225863 : Nat := 3196860208043080016080283

theorem tailTrace_6225863 : CollatzResearch.WordTrace tailWord_6225863 prefixEnd_6225863 3196860208043080016080283 := by
  unfold tailWord_6225863
  simp only [CollatzResearch.WordTrace]
  refine ⟨227075878643769118592450243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151383919095846079061633495 227075878643769118592450243)
  ·
    refine ⟨340613817965653677888675365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227075878643769118592450243 340613817965653677888675365)
    ·
      refine ⟨63865090868560064604126631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340613817965653677888675365 63865090868560064604126631)
      ·
        refine ⟨95797636302840096906189947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63865090868560064604126631 95797636302840096906189947)
        ·
          refine ⟨143696454454260145359284921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95797636302840096906189947 143696454454260145359284921)
          ·
            refine ⟨107772340840695109019463691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143696454454260145359284921 107772340840695109019463691)
            ·
              refine ⟨161658511261042663529195537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107772340840695109019463691 161658511261042663529195537)
              ·
                refine ⟨121243883445781997646896653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161658511261042663529195537 121243883445781997646896653)
                ·
                  refine ⟨45466456292168249117586245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121243883445781997646896653 45466456292168249117586245)
                  ·
                    refine ⟨8524960554781546709547421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45466456292168249117586245 8524960554781546709547421)
                    ·
                      refine ⟨3196860208043080016080283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8524960554781546709547421 3196860208043080016080283)
                      ·
                        rfl

theorem cell23_6225863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_6225863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225863 prefixEnd_6225863 := by exact prefixLift 6225863
  have htrace : WordTrace (prefixWord ++ tailWord_6225863) baseStart_6225863 baseEnd_6225863 := by
    simpa [prefixWord, tailWord_6225863, baseEnd_6225863] using wordTrace_append hprefix tailTrace_6225863
  have hstable : (prefixWord ++ tailWord_6225863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225863).length < 2 ^ (prefixWord ++ tailWord_6225863).sum := by decide
  have hdescent : baseEnd_6225863 < baseStart_6225863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225870 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_6225870 : Nat := 118140960795 + 6225870 * 2 ^ 59
def prefixEnd_6225870 : Nat := 4983230072969 + 3 ^ 40 * 6225870 * 2
def baseEnd_6225870 : Nat := 1065621267469220496230917

theorem tailTrace_6225870 : CollatzResearch.WordTrace tailWord_6225870 prefixEnd_6225870 1065621267469220496230917 := by
  unfold tailWord_6225870
  simp only [CollatzResearch.WordTrace]
  refine ⟨28384516744342969848494383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151384089303162505858636709 28384516744342969848494383)
  ·
    refine ⟨42576775116514454772741575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28384516744342969848494383 42576775116514454772741575)
    ·
      refine ⟨63865162674771682159112363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42576775116514454772741575 63865162674771682159112363)
      ·
        refine ⟨95797744012157523238668545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63865162674771682159112363 95797744012157523238668545)
        ·
          refine ⟨71848308009118142429001409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95797744012157523238668545 71848308009118142429001409)
          ·
            refine ⟨53886231006838606821751057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71848308009118142429001409 53886231006838606821751057)
            ·
              refine ⟨40414673255128955116313293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53886231006838606821751057 40414673255128955116313293)
              ·
                refine ⟨15155502470673358168617485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40414673255128955116313293 15155502470673358168617485)
                ·
                  refine ⟨5683313426502509313231557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15155502470673358168617485 5683313426502509313231557)
                  ·
                    refine ⟨1065621267469220496230917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683313426502509313231557 1065621267469220496230917)
                    ·
                      rfl

theorem cell23_6225870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_6225870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225870 prefixEnd_6225870 := by exact prefixLift 6225870
  have htrace : WordTrace (prefixWord ++ tailWord_6225870) baseStart_6225870 baseEnd_6225870 := by
    simpa [prefixWord, tailWord_6225870, baseEnd_6225870] using wordTrace_append hprefix tailTrace_6225870
  have hstable : (prefixWord ++ tailWord_6225870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225870).length < 2 ^ (prefixWord ++ tailWord_6225870).sum := by decide
  have hdescent : baseEnd_6225870 < baseStart_6225870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225877 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6225877 : Nat := 118140960795 + 6225877 * 2 ^ 59
def prefixEnd_6225877 : Nat := 4983230072969 + 3 ^ 40 * 6225877 * 2
def baseEnd_6225877 : Nat := 3196867396772242961305219

theorem tailTrace_6225877 : CollatzResearch.WordTrace tailWord_6225877 prefixEnd_6225877 3196867396772242961305219 := by
  unfold tailWord_6225877
  simp only [CollatzResearch.WordTrace]
  refine ⟨227076389265718398983459885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151384259510478932655639923 227076389265718398983459885)
  ·
    refine ⟨85153645974644399618797457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227076389265718398983459885 85153645974644399618797457)
    ·
      refine ⟨63865234480983299714098093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85153645974644399618797457 63865234480983299714098093)
      ·
        refine ⟨23949462930368737392786785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63865234480983299714098093 23949462930368737392786785)
        ·
          refine ⟨17962097197776553044590089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23949462930368737392786785 17962097197776553044590089)
          ·
            refine ⟨13471572898332414783442567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17962097197776553044590089 13471572898332414783442567)
            ·
              refine ⟨20207359347498622175163851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13471572898332414783442567 20207359347498622175163851)
              ·
                refine ⟨30311039021247933262745777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20207359347498622175163851 30311039021247933262745777)
                ·
                  refine ⟨22733279265935949947059333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30311039021247933262745777 22733279265935949947059333)
                  ·
                    refine ⟨4262489862362990615073625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22733279265935949947059333 4262489862362990615073625)
                    ·
                      refine ⟨3196867396772242961305219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262489862362990615073625 3196867396772242961305219)
                      ·
                        rfl

theorem cell23_6225877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6225877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225877 prefixEnd_6225877 := by exact prefixLift 6225877
  have htrace : WordTrace (prefixWord ++ tailWord_6225877) baseStart_6225877 baseEnd_6225877 := by
    simpa [prefixWord, tailWord_6225877, baseEnd_6225877] using wordTrace_append hprefix tailTrace_6225877
  have hstable : (prefixWord ++ tailWord_6225877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225877).length < 2 ^ (prefixWord ++ tailWord_6225877).sum := by decide
  have hdescent : baseEnd_6225877 < baseStart_6225877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225927 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_6225927 : Nat := 118140960795 + 6225927 * 2 ^ 59
def prefixEnd_6225927 : Nat := 4983230072969 + 3 ^ 40 * 6225927 * 2
def baseEnd_6225927 : Nat := 3196893070804967765679989

theorem tailTrace_6225927 : CollatzResearch.WordTrace tailWord_6225927 prefixEnd_6225927 3196893070804967765679989 := by
  unfold tailWord_6225927
  simp only [CollatzResearch.WordTrace]
  refine ⟨227078212915537257522780035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151385475277024838348520023 227078212915537257522780035)
  ·
    refine ⟨340617319373305886284170053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227078212915537257522780035 340617319373305886284170053)
    ·
      refine ⟨63865747382494853678281885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340617319373305886284170053 63865747382494853678281885)
      ·
        refine ⟨23949655268435570129355707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63865747382494853678281885 23949655268435570129355707)
        ·
          refine ⟨35924482902653355194033561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23949655268435570129355707 35924482902653355194033561)
          ·
            refine ⟨26943362176990016395525171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35924482902653355194033561 26943362176990016395525171)
            ·
              refine ⟨40415043265485024593287757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26943362176990016395525171 40415043265485024593287757)
              ·
                refine ⟨15155641224556884222482909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40415043265485024593287757 15155641224556884222482909)
                ·
                  refine ⟨5683365459208831583431091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15155641224556884222482909 5683365459208831583431091)
                  ·
                    refine ⟨8525048188813247375146637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683365459208831583431091 8525048188813247375146637)
                    ·
                      refine ⟨3196893070804967765679989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8525048188813247375146637 3196893070804967765679989)
                      ·
                        rfl

theorem cell23_6225927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_6225927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225927 prefixEnd_6225927 := by exact prefixLift 6225927
  have htrace : WordTrace (prefixWord ++ tailWord_6225927) baseStart_6225927 baseEnd_6225927 := by
    simpa [prefixWord, tailWord_6225927, baseEnd_6225927] using wordTrace_append hprefix tailTrace_6225927
  have hstable : (prefixWord ++ tailWord_6225927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225927).length < 2 ^ (prefixWord ++ tailWord_6225927).sum := by decide
  have hdescent : baseEnd_6225927 < baseStart_6225927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225970 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_6225970 : Nat := 118140960795 + 6225970 * 2 ^ 59
def prefixEnd_6225970 : Nat := 4983230072969 + 3 ^ 40 * 6225970 * 2
def baseEnd_6225970 : Nat := 3196915150473111097442291

theorem tailTrace_6225970 : CollatzResearch.WordTrace tailWord_6225970 prefixEnd_6225970 3196915150473111097442291 := by
  unfold tailWord_6225970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56769945313595368966648841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151386520836254317244396909 56769945313595368966648841)
  ·
    refine ⟨42577458985196526724986631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56769945313595368966648841 42577458985196526724986631)
    ·
      refine ⟨63866188477794790087479947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42577458985196526724986631 63866188477794790087479947)
      ·
        refine ⟨95799282716692185131219921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63866188477794790087479947 95799282716692185131219921)
        ·
          refine ⟨71849462037519138848414941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95799282716692185131219921 71849462037519138848414941)
          ·
            refine ⟨26943548264069677068155603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71849462037519138848414941 26943548264069677068155603)
            ·
              refine ⟨40415322396104515602233405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26943548264069677068155603 40415322396104515602233405)
              ·
                refine ⟨15155745898539193350837527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40415322396104515602233405 15155745898539193350837527)
                ·
                  refine ⟨22733618847808790026256291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15155745898539193350837527 22733618847808790026256291)
                  ·
                    refine ⟨34100428271713185039384437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22733618847808790026256291 34100428271713185039384437)
                    ·
                      refine ⟨3196915150473111097442291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34100428271713185039384437 3196915150473111097442291)
                      ·
                        rfl

theorem cell23_6225970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_6225970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225970 prefixEnd_6225970 := by exact prefixLift 6225970
  have htrace : WordTrace (prefixWord ++ tailWord_6225970) baseStart_6225970 baseEnd_6225970 := by
    simpa [prefixWord, tailWord_6225970, baseEnd_6225970] using wordTrace_append hprefix tailTrace_6225970
  have hstable : (prefixWord ++ tailWord_6225970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225970).length < 2 ^ (prefixWord ++ tailWord_6225970).sum := by decide
  have hdescent : baseEnd_6225970 < baseStart_6225970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225973 : List Nat := [1, 3, 3, 1, 1, 1, 13]
def baseStart_6225973 : Nat := 118140960795 + 6225973 * 2 ^ 59
def prefixEnd_6225973 : Nat := 4983230072969 + 3 ^ 40 * 6225973 * 2
def baseEnd_6225973 : Nat := 39468107295247834391417

theorem tailTrace_6225973 : CollatzResearch.WordTrace tailWord_6225973 prefixEnd_6225973 39468107295247834391417 := by
  unfold tailWord_6225973
  simp only [CollatzResearch.WordTrace]
  refine ⟨227079890673370607378954573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151386593782247071585969715 227079890673370607378954573)
  ·
    refine ⟨85154959002513977767107965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227079890673370607378954573 85154959002513977767107965)
    ·
      refine ⟨31933109625942741662665487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85154959002513977767107965 31933109625942741662665487)
      ·
        refine ⟨47899664438914112493998231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31933109625942741662665487 47899664438914112493998231)
        ·
          refine ⟨71849496658371168740997347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47899664438914112493998231 71849496658371168740997347)
          ·
            refine ⟨107774244987556753111496021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71849496658371168740997347 107774244987556753111496021)
            ·
              refine ⟨39468107295247834391417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 107774244987556753111496021 39468107295247834391417)
              ·
                rfl

theorem cell23_6225973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 13].length) (baseStart_6225973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225973 prefixEnd_6225973 := by exact prefixLift 6225973
  have htrace : WordTrace (prefixWord ++ tailWord_6225973) baseStart_6225973 baseEnd_6225973 := by
    simpa [prefixWord, tailWord_6225973, baseEnd_6225973] using wordTrace_append hprefix tailTrace_6225973
  have hstable : (prefixWord ++ tailWord_6225973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225973).length < 2 ^ (prefixWord ++ tailWord_6225973).sum := by decide
  have hdescent : baseEnd_6225973 < baseStart_6225973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225984 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 3, 2, 2]
def baseStart_6225984 : Nat := 118140960795 + 6225984 * 2 ^ 59
def prefixEnd_6225984 : Nat := 4983230072969 + 3 ^ 40 * 6225984 * 2
def baseEnd_6225984 : Nat := 3196922339202274042667227

theorem tailTrace_6225984 : CollatzResearch.WordTrace tailWord_6225984 prefixEnd_6225984 3196922339202274042667227 := by
  unfold tailWord_6225984
  simp only [CollatzResearch.WordTrace]
  refine ⟨113540145938165378128802503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151386861250887170838403337 113540145938165378128802503)
  ·
    refine ⟨170310218907248067193203755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113540145938165378128802503 170310218907248067193203755)
    ·
      refine ⟨255465328360872100789805633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170310218907248067193203755 255465328360872100789805633)
      ·
        refine ⟨191598996270654075592354225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255465328360872100789805633 191598996270654075592354225)
        ·
          refine ⟨143699247202990556694265669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191598996270654075592354225 143699247202990556694265669)
          ·
            refine ⟨26943608850560729380174813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143699247202990556694265669 26943608850560729380174813)
            ·
              refine ⟨10103853318960273517565555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26943608850560729380174813 10103853318960273517565555)
              ·
                refine ⟨15155779978440410276348333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10103853318960273517565555 15155779978440410276348333)
                ·
                  refine ⟨5683417491915153853630625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15155779978440410276348333 5683417491915153853630625)
                  ·
                    refine ⟨4262563118936365390222969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5683417491915153853630625 4262563118936365390222969)
                    ·
                      refine ⟨3196922339202274042667227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262563118936365390222969 3196922339202274042667227)
                      ·
                        rfl

theorem cell23_6225984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_6225984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225984 prefixEnd_6225984 := by exact prefixLift 6225984
  have htrace : WordTrace (prefixWord ++ tailWord_6225984) baseStart_6225984 baseEnd_6225984 := by
    simpa [prefixWord, tailWord_6225984, baseEnd_6225984] using wordTrace_append hprefix tailTrace_6225984
  have hstable : (prefixWord ++ tailWord_6225984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225984).length < 2 ^ (prefixWord ++ tailWord_6225984).sum := by decide
  have hdescent : baseEnd_6225984 < baseStart_6225984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225993 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_6225993 : Nat := 118140960795 + 6225993 * 2 ^ 59
def prefixEnd_6225993 : Nat := 4983230072969 + 3 ^ 40 * 6225993 * 2
def baseEnd_6225993 : Nat := 3196926960528164507454685

theorem tailTrace_6225993 : CollatzResearch.WordTrace tailWord_6225993 prefixEnd_6225993 3196926960528164507454685 := by
  unfold tailWord_6225993
  simp only [CollatzResearch.WordTrace]
  refine ⟨227080620133298150794682633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151387080088865433863121755 227080620133298150794682633)
  ·
    refine ⟨170310465099973613096011975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227080620133298150794682633 170310465099973613096011975)
    ·
      refine ⟨255465697649960419644017963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170310465099973613096011975 255465697649960419644017963)
      ·
        refine ⟨383198546474940629466026945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255465697649960419644017963 383198546474940629466026945)
        ·
          refine ⟨287398909856205472099520209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383198546474940629466026945 287398909856205472099520209)
          ·
            refine ⟨215549182392154104074640157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287398909856205472099520209 215549182392154104074640157)
            ·
              refine ⟨80830943397057789027990059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215549182392154104074640157 80830943397057789027990059)
              ·
                refine ⟨121246415095586683541985089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80830943397057789027990059 121246415095586683541985089)
                ·
                  refine ⟨90934811321690012656488817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121246415095586683541985089 90934811321690012656488817)
                  ·
                    refine ⟨68201108491267509492366613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90934811321690012656488817 68201108491267509492366613)
                    ·
                      refine ⟨3196926960528164507454685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68201108491267509492366613 3196926960528164507454685)
                      ·
                        rfl

theorem cell23_6225993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_6225993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225993 prefixEnd_6225993 := by exact prefixLift 6225993
  have htrace : WordTrace (prefixWord ++ tailWord_6225993) baseStart_6225993 baseEnd_6225993 := by
    simpa [prefixWord, tailWord_6225993, baseEnd_6225993] using wordTrace_append hprefix tailTrace_6225993
  have hstable : (prefixWord ++ tailWord_6225993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225993).length < 2 ^ (prefixWord ++ tailWord_6225993).sum := by decide
  have hdescent : baseEnd_6225993 < baseStart_6225993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6225997 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6225997 : Nat := 118140960795 + 6225997 * 2 ^ 59
def prefixEnd_6225997 : Nat := 4983230072969 + 3 ^ 40 * 6225997 * 2
def baseEnd_6225997 : Nat := 3196929014450782491804667

theorem tailTrace_6225997 : CollatzResearch.WordTrace tailWord_6225997 prefixEnd_6225997 3196929014450782491804667 := by
  unfold tailWord_6225997
  simp only [CollatzResearch.WordTrace]
  refine ⟨227080766025283659477828245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151387177350189106318552163 227080766025283659477828245)
  ·
    refine ⟨10644410907435171538023199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227080766025283659477828245 10644410907435171538023199)
    ·
      refine ⟨15966616361152757307034799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644410907435171538023199 15966616361152757307034799)
      ·
        refine ⟨23949924541729135960552199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15966616361152757307034799 23949924541729135960552199)
        ·
          refine ⟨35924886812593703940828299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23949924541729135960552199 35924886812593703940828299)
          ·
            refine ⟨53887330218890555911242449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35924886812593703940828299 53887330218890555911242449)
            ·
              refine ⟨40415497664167916933431837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53887330218890555911242449 40415497664167916933431837)
              ·
                refine ⟨15155811624062968850036939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40415497664167916933431837 15155811624062968850036939)
                ·
                  refine ⟨22733717436094453275055409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15155811624062968850036939 22733717436094453275055409)
                  ·
                    refine ⟨17050288077070839956291557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22733717436094453275055409 17050288077070839956291557)
                    ·
                      refine ⟨3196929014450782491804667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17050288077070839956291557 3196929014450782491804667)
                      ·
                        rfl

theorem cell23_6225997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6225997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6225997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6225997 prefixEnd_6225997 := by exact prefixLift 6225997
  have htrace : WordTrace (prefixWord ++ tailWord_6225997) baseStart_6225997 baseEnd_6225997 := by
    simpa [prefixWord, tailWord_6225997, baseEnd_6225997] using wordTrace_append hprefix tailTrace_6225997
  have hstable : (prefixWord ++ tailWord_6225997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6225997).length < 2 ^ (prefixWord ++ tailWord_6225997).sum := by decide
  have hdescent : baseEnd_6225997 < baseStart_6225997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6225997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226034 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_6226034 : Nat := 118140960795 + 6226034 * 2 ^ 59
def prefixEnd_6226034 : Nat := 4983230072969 + 3 ^ 40 * 6226034 * 2
def baseEnd_6226034 : Nat := 3196948013234998847041997

theorem tailTrace_6226034 : CollatzResearch.WordTrace tailWord_6226034 prefixEnd_6226034 3196948013234998847041997 := by
  unfold tailWord_6226034
  simp only [CollatzResearch.WordTrace]
  refine ⟨56770528881537403699231289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151388077017433076531283437 56770528881537403699231289)
  ·
    refine ⟨42577896661153052774423467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56770528881537403699231289 42577896661153052774423467)
    ·
      refine ⟨63866844991729579161635201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42577896661153052774423467 63866844991729579161635201)
      ·
        refine ⟨47900133743797184371226401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63866844991729579161635201 47900133743797184371226401)
        ·
          refine ⟨35925100307847888278419801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47900133743797184371226401 35925100307847888278419801)
          ·
            refine ⟨26943825230885916208814851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35925100307847888278419801 26943825230885916208814851)
            ·
              refine ⟨40415737846328874313222277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26943825230885916208814851 40415737846328874313222277)
              ·
                refine ⟨7577950846186663933729177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40415737846328874313222277 7577950846186663933729177)
                ·
                  refine ⟨5683463134639997950296883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577950846186663933729177 5683463134639997950296883)
                  ·
                    refine ⟨8525194701959996925445325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683463134639997950296883 8525194701959996925445325)
                    ·
                      refine ⟨3196948013234998847041997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8525194701959996925445325 3196948013234998847041997)
                      ·
                        rfl

theorem cell23_6226034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_6226034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226034 prefixEnd_6226034 := by exact prefixLift 6226034
  have htrace : WordTrace (prefixWord ++ tailWord_6226034) baseStart_6226034 baseEnd_6226034 := by
    simpa [prefixWord, tailWord_6226034, baseEnd_6226034] using wordTrace_append hprefix tailTrace_6226034
  have hstable : (prefixWord ++ tailWord_6226034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226034).length < 2 ^ (prefixWord ++ tailWord_6226034).sum := by decide
  have hdescent : baseEnd_6226034 < baseStart_6226034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226078 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_6226078 : Nat := 118140960795 + 6226078 * 2 ^ 59
def prefixEnd_6226078 : Nat := 4983230072969 + 3 ^ 40 * 6226078 * 2
def baseEnd_6226078 : Nat := 3196970606383796674891795

theorem tailTrace_6226078 : CollatzResearch.WordTrace tailWord_6226078 prefixEnd_6226078 3196970606383796674891795 := by
  unfold tailWord_6226078
  simp only [CollatzResearch.WordTrace]
  refine ⟨28385465042248776288940861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151389146891993473541017925 28385465042248776288940861)
  ·
    refine ⟨10644549390843291108352823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28385465042248776288940861 10644549390843291108352823)
    ·
      refine ⟨15966824086264936662529235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644549390843291108352823 15966824086264936662529235)
      ·
        refine ⟨23950236129397404993793853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15966824086264936662529235 23950236129397404993793853)
        ·
          refine ⟨8981338548524026872672695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23950236129397404993793853 8981338548524026872672695)
          ·
            refine ⟨13472007822786040309009043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981338548524026872672695 13472007822786040309009043)
            ·
              refine ⟨20208011734179060463513565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13472007822786040309009043 20208011734179060463513565)
              ·
                refine ⟨7578004400317147673817587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20208011734179060463513565 7578004400317147673817587)
                ·
                  refine ⟨11367006600475721510726381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7578004400317147673817587 11367006600475721510726381)
                  ·
                    refine ⟨4262627475178395566522393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11367006600475721510726381 4262627475178395566522393)
                    ·
                      refine ⟨3196970606383796674891795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262627475178395566522393 3196970606383796674891795)
                      ·
                        rfl

theorem cell23_6226078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_6226078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226078 prefixEnd_6226078 := by exact prefixLift 6226078
  have htrace : WordTrace (prefixWord ++ tailWord_6226078) baseStart_6226078 baseEnd_6226078 := by
    simpa [prefixWord, tailWord_6226078, baseEnd_6226078] using wordTrace_append hprefix tailTrace_6226078
  have hstable : (prefixWord ++ tailWord_6226078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226078).length < 2 ^ (prefixWord ++ tailWord_6226078).sum := by decide
  have hdescent : baseEnd_6226078 < baseStart_6226078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226108 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_6226108 : Nat := 118140960795 + 6226108 * 2 ^ 59
def prefixEnd_6226108 : Nat := 4983230072969 + 3 ^ 40 * 6226108 * 2
def baseEnd_6226108 : Nat := 3196986010803431557516657

theorem tailTrace_6226108 : CollatzResearch.WordTrace tailWord_6226108 prefixEnd_6226108 3196986010803431557516657 := by
  unfold tailWord_6226108
  simp only [CollatzResearch.WordTrace]
  refine ⟨113542407263940762717559489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151389876351921016956745985 113542407263940762717559489)
  ·
    refine ⟨85156805447955572038169617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113542407263940762717559489 85156805447955572038169617)
    ·
      refine ⟨63867604085966679028627213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85156805447955572038169617 63867604085966679028627213)
      ·
        refine ⟨23950351532237504635735205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63867604085966679028627213 23950351532237504635735205)
        ·
          refine ⟨4490690912294532119200351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23950351532237504635735205 4490690912294532119200351)
          ·
            refine ⟨6736036368441798178800527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490690912294532119200351 6736036368441798178800527)
            ·
              refine ⟨10104054552662697268200791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6736036368441798178800527 10104054552662697268200791)
              ·
                refine ⟨15156081828994045902301187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10104054552662697268200791 15156081828994045902301187)
                ·
                  refine ⟨22734122743491068853451781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15156081828994045902301187 22734122743491068853451781)
                  ·
                    refine ⟨4262648014404575410022209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22734122743491068853451781 4262648014404575410022209)
                    ·
                      refine ⟨3196986010803431557516657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262648014404575410022209 3196986010803431557516657)
                      ·
                        rfl

theorem cell23_6226108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_6226108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226108 prefixEnd_6226108 := by exact prefixLift 6226108
  have htrace : WordTrace (prefixWord ++ tailWord_6226108) baseStart_6226108 baseEnd_6226108 := by
    simpa [prefixWord, tailWord_6226108, baseEnd_6226108] using wordTrace_append hprefix tailTrace_6226108
  have hstable : (prefixWord ++ tailWord_6226108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226108).length < 2 ^ (prefixWord ++ tailWord_6226108).sum := by decide
  have hdescent : baseEnd_6226108 < baseStart_6226108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226117 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 2, 5, 2]
def baseStart_6226117 : Nat := 118140960795 + 6226117 * 2 ^ 59
def prefixEnd_6226117 : Nat := 4983230072969 + 3 ^ 40 * 6226117 * 2
def baseEnd_6226117 : Nat := 3196990632129322022304115

theorem tailTrace_6226117 : CollatzResearch.WordTrace tailWord_6226117 prefixEnd_6226117 3196990632129322022304115 := by
  unfold tailWord_6226117
  simp only [CollatzResearch.WordTrace]
  refine ⟨227085142784848919972196605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151390095189899279981464403 227085142784848919972196605)
  ·
    refine ⟨85156928544318344989573727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227085142784848919972196605 85156928544318344989573727)
    ·
      refine ⟨127735392816477517484360591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85156928544318344989573727 127735392816477517484360591)
      ·
        refine ⟨191603089224716276226540887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127735392816477517484360591 191603089224716276226540887)
        ·
          refine ⟨287404633837074414339811331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191603089224716276226540887 287404633837074414339811331)
          ·
            refine ⟨431106950755611621509716997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287404633837074414339811331 431106950755611621509716997)
            ·
              refine ⟨80832553266677179033071937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431106950755611621509716997 80832553266677179033071937)
              ·
                refine ⟨60624414950007884274803953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80832553266677179033071937 60624414950007884274803953)
                ·
                  refine ⟨45468311212505913206102965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60624414950007884274803953 45468311212505913206102965)
                  ·
                    refine ⟨4262654176172429363072153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45468311212505913206102965 4262654176172429363072153)
                    ·
                      refine ⟨3196990632129322022304115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262654176172429363072153 3196990632129322022304115)
                      ·
                        rfl

theorem cell23_6226117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_6226117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226117 prefixEnd_6226117 := by exact prefixLift 6226117
  have htrace : WordTrace (prefixWord ++ tailWord_6226117) baseStart_6226117 baseEnd_6226117 := by
    simpa [prefixWord, tailWord_6226117, baseEnd_6226117] using wordTrace_append hprefix tailTrace_6226117
  have hstable : (prefixWord ++ tailWord_6226117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226117).length < 2 ^ (prefixWord ++ tailWord_6226117).sum := by decide
  have hdescent : baseEnd_6226117 < baseStart_6226117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226120 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_6226120 : Nat := 118140960795 + 6226120 * 2 ^ 59
def prefixEnd_6226120 : Nat := 4983230072969 + 3 ^ 40 * 6226120 * 2
def baseEnd_6226120 : Nat := 3196992172571285510566601

theorem tailTrace_6226120 : CollatzResearch.WordTrace tailWord_6226120 prefixEnd_6226120 3196992172571285510566601 := by
  unfold tailWord_6226120
  simp only [CollatzResearch.WordTrace]
  refine ⟨113542626101919025742277907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151390168135892034323037209 113542626101919025742277907)
  ·
    refine ⟨170313939152878538613416861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113542626101919025742277907 170313939152878538613416861)
    ·
      refine ⟨63867727182329451980031323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170313939152878538613416861 63867727182329451980031323)
      ·
        refine ⟨95801590773494177970046985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63867727182329451980031323 95801590773494177970046985)
        ·
          refine ⟨71851193080120633477535239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95801590773494177970046985 71851193080120633477535239)
          ·
            refine ⟨107776789620180950216302859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71851193080120633477535239 107776789620180950216302859)
            ·
              refine ⟨161665184430271425324454289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107776789620180950216302859 161665184430271425324454289)
              ·
                refine ⟨121248888322703568993340717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161665184430271425324454289 121248888322703568993340717)
                ·
                  refine ⟨45468333121013838372502769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121248888322703568993340717 45468333121013838372502769)
                  ·
                    refine ⟨34101249840760378779377077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45468333121013838372502769 34101249840760378779377077)
                    ·
                      refine ⟨3196992172571285510566601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34101249840760378779377077 3196992172571285510566601)
                      ·
                        rfl

theorem cell23_6226120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_6226120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226120 prefixEnd_6226120 := by exact prefixLift 6226120
  have htrace : WordTrace (prefixWord ++ tailWord_6226120) baseStart_6226120 baseEnd_6226120 := by
    simpa [prefixWord, tailWord_6226120, baseEnd_6226120] using wordTrace_append hprefix tailTrace_6226120
  have hstable : (prefixWord ++ tailWord_6226120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226120).length < 2 ^ (prefixWord ++ tailWord_6226120).sum := by decide
  have hdescent : baseEnd_6226120 < baseStart_6226120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226160 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_6226160 : Nat := 118140960795 + 6226160 * 2 ^ 59
def prefixEnd_6226160 : Nat := 4983230072969 + 3 ^ 40 * 6226160 * 2
def baseEnd_6226160 : Nat := 3197012711797465354066417

theorem tailTrace_6226160 : CollatzResearch.WordTrace tailWord_6226160 prefixEnd_6226160 3197012711797465354066417 := by
  unfold tailWord_6226160
  simp only [CollatzResearch.WordTrace]
  refine ⟨113543355561846569158005967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151391140749128758877341289 113543355561846569158005967)
  ·
    refine ⟨170315033342769853737008951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113543355561846569158005967 170315033342769853737008951)
    ·
      refine ⟨255472550014154780605513427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170315033342769853737008951 255472550014154780605513427)
      ·
        refine ⟨383208825021232170908270141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255472550014154780605513427 383208825021232170908270141)
        ·
          refine ⟨143703309382962064090601303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383208825021232170908270141 143703309382962064090601303)
          ·
            refine ⟨215554964074443096135901955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143703309382962064090601303 215554964074443096135901955)
            ·
              refine ⟨323332446111664644203852933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215554964074443096135901955 323332446111664644203852933)
              ·
                refine ⟨60624833645937120788222425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323332446111664644203852933 60624833645937120788222425)
                ·
                  refine ⟨45468625234452840591166819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60624833645937120788222425 45468625234452840591166819)
                  ·
                    refine ⟨68202937851679260886750229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45468625234452840591166819 68202937851679260886750229)
                    ·
                      refine ⟨3197012711797465354066417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68202937851679260886750229 3197012711797465354066417)
                      ·
                        rfl

theorem cell23_6226160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_6226160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226160 prefixEnd_6226160 := by exact prefixLift 6226160
  have htrace : WordTrace (prefixWord ++ tailWord_6226160) baseStart_6226160 baseEnd_6226160 := by
    simpa [prefixWord, tailWord_6226160, baseEnd_6226160] using wordTrace_append hprefix tailTrace_6226160
  have hstable : (prefixWord ++ tailWord_6226160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226160).length < 2 ^ (prefixWord ++ tailWord_6226160).sum := by decide
  have hdescent : baseEnd_6226160 < baseStart_6226160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226174 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_6226174 : Nat := 118140960795 + 6226174 * 2 ^ 59
def prefixEnd_6226174 : Nat := 4983230072969 + 3 ^ 40 * 6226174 * 2
def baseEnd_6226174 : Nat := 1065673300175542766430451

theorem tailTrace_6226174 : CollatzResearch.WordTrace tailWord_6226174 prefixEnd_6226174 1065673300175542766430451 := by
  unfold tailWord_6226174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28385902718205302338377697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151391481163761612471347717 28385902718205302338377697)
  ·
    refine ⟨21289427038653976753783273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28385902718205302338377697 21289427038653976753783273)
    ·
      refine ⟨15967070278990482565337455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21289427038653976753783273 15967070278990482565337455)
      ·
        refine ⟨23950605418485723848006183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15967070278990482565337455 23950605418485723848006183)
        ·
          refine ⟨35925908127728585772009275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23950605418485723848006183 35925908127728585772009275)
          ·
            refine ⟨53888862191592878658013913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35925908127728585772009275 53888862191592878658013913)
            ·
              refine ⟨40416646643694658993510435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53888862191592878658013913 40416646643694658993510435)
              ·
                refine ⟨60624969965541988490265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40416646643694658993510435 60624969965541988490265653)
                ·
                  refine ⟨5683590934269561420962405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60624969965541988490265653 5683590934269561420962405)
                  ·
                    refine ⟨1065673300175542766430451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683590934269561420962405 1065673300175542766430451)
                    ·
                      rfl

theorem cell23_6226174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_6226174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226174 prefixEnd_6226174 := by exact prefixLift 6226174
  have htrace : WordTrace (prefixWord ++ tailWord_6226174) baseStart_6226174 baseEnd_6226174 := by
    simpa [prefixWord, tailWord_6226174, baseEnd_6226174] using wordTrace_append hprefix tailTrace_6226174
  have hstable : (prefixWord ++ tailWord_6226174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226174).length < 2 ^ (prefixWord ++ tailWord_6226174).sum := by decide
  have hdescent : baseEnd_6226174 < baseStart_6226174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226184 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_6226184 : Nat := 118140960795 + 6226184 * 2 ^ 59
def prefixEnd_6226184 : Nat := 4983230072969 + 3 ^ 40 * 6226184 * 2
def baseEnd_6226184 : Nat := 3197025035333173260166307

theorem tailTrace_6226184 : CollatzResearch.WordTrace tailWord_6226184 prefixEnd_6226184 3197025035333173260166307 := by
  unfold tailWord_6226184
  simp only [CollatzResearch.WordTrace]
  refine ⟨113543793237803095207442803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151391724317070793609923737 113543793237803095207442803)
  ·
    refine ⟨170315689856704642811164205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113543793237803095207442803 170315689856704642811164205)
    ·
      refine ⟨63868383696264241054186577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170315689856704642811164205 63868383696264241054186577)
      ·
        refine ⟨47901287772198180790639933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63868383696264241054186577 47901287772198180790639933)
        ·
          refine ⟨17962982914574317796489975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47901287772198180790639933 17962982914574317796489975)
          ·
            refine ⟨26944474371861476694734963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17962982914574317796489975 26944474371861476694734963)
            ·
              refine ⟨40416711557792215042102445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26944474371861476694734963 40416711557792215042102445)
              ·
                refine ⟨15156266834172080640788417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40416711557792215042102445 15156266834172080640788417)
                ·
                  refine ⟨11367200125629060480591313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15156266834172080640788417 11367200125629060480591313)
                  ·
                    refine ⟨8525400094221795360443485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11367200125629060480591313 8525400094221795360443485)
                    ·
                      refine ⟨3197025035333173260166307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8525400094221795360443485 3197025035333173260166307)
                      ·
                        rfl

theorem cell23_6226184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_6226184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226184 prefixEnd_6226184 := by exact prefixLift 6226184
  have htrace : WordTrace (prefixWord ++ tailWord_6226184) baseStart_6226184 baseEnd_6226184 := by
    simpa [prefixWord, tailWord_6226184, baseEnd_6226184] using wordTrace_append hprefix tailTrace_6226184
  have hstable : (prefixWord ++ tailWord_6226184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226184).length < 2 ^ (prefixWord ++ tailWord_6226184).sum := by decide
  have hdescent : baseEnd_6226184 < baseStart_6226184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226208 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 1, 4]
def baseStart_6226208 : Nat := 118140960795 + 6226208 * 2 ^ 59
def prefixEnd_6226208 : Nat := 4983230072969 + 3 ^ 40 * 6226208 * 2
def baseEnd_6226208 : Nat := 1065679119622960388755399

theorem tailTrace_6226208 : CollatzResearch.WordTrace tailWord_6226208 prefixEnd_6226208 1065679119622960388755399 := by
  unfold tailWord_6226208
  simp only [CollatzResearch.WordTrace]
  refine ⟨113544230913759621256879639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151392307885012828342506185 113544230913759621256879639)
  ·
    refine ⟨170316346370639431885319459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113544230913759621256879639 170316346370639431885319459)
    ·
      refine ⟨255474519555959147827979189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170316346370639431885319459 255474519555959147827979189)
      ·
        refine ⟨23950736208371170108873049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255474519555959147827979189 23950736208371170108873049)
        ·
          refine ⟨17963052156278377581654787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23950736208371170108873049 17963052156278377581654787)
          ·
            refine ⟨26944578234417566372482181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17963052156278377581654787 26944578234417566372482181)
            ·
              refine ⟨5052108418953293694840409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26944578234417566372482181 5052108418953293694840409)
              ·
                refine ⟨3789081314214970271130307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052108418953293694840409 3789081314214970271130307)
                ·
                  refine ⟨5683621971322455406695461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789081314214970271130307 5683621971322455406695461)
                  ·
                    refine ⟨1065679119622960388755399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683621971322455406695461 1065679119622960388755399)
                    ·
                      rfl

theorem cell23_6226208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 4].length) (baseStart_6226208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226208 prefixEnd_6226208 := by exact prefixLift 6226208
  have htrace : WordTrace (prefixWord ++ tailWord_6226208) baseStart_6226208 baseEnd_6226208 := by
    simpa [prefixWord, tailWord_6226208, baseEnd_6226208] using wordTrace_append hprefix tailTrace_6226208
  have hstable : (prefixWord ++ tailWord_6226208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226208).length < 2 ^ (prefixWord ++ tailWord_6226208).sum := by decide
  have hdescent : baseEnd_6226208 < baseStart_6226208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226215 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6226215 : Nat := 118140960795 + 6226215 * 2 ^ 59
def prefixEnd_6226215 : Nat := 4983230072969 + 3 ^ 40 * 6226215 * 2
def baseEnd_6226215 : Nat := 3197040953233462638878665

theorem tailTrace_6226215 : CollatzResearch.WordTrace tailWord_6226215 prefixEnd_6226215 3197040953233462638878665 := by
  unfold tailWord_6226215
  simp only [CollatzResearch.WordTrace]
  refine ⟨227088717138493882709264099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151392478092329255139509399 227088717138493882709264099)
  ·
    refine ⟨340633075707740824063896149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227088717138493882709264099 340633075707740824063896149)
    ·
      refine ⟨3991793855950087781998783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 340633075707740824063896149 3991793855950087781998783)
      ·
        refine ⟨5987690783925131672998175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991793855950087781998783 5987690783925131672998175)
        ·
          refine ⟨8981536175887697509497263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5987690783925131672998175 8981536175887697509497263)
          ·
            refine ⟨13472304263831546264245895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981536175887697509497263 13472304263831546264245895)
            ·
              refine ⟨20208456395747319396368843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13472304263831546264245895 20208456395747319396368843)
              ·
                refine ⟨30312684593620979094553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20208456395747319396368843 30312684593620979094553265)
                ·
                  refine ⟨22734513445215734320914949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30312684593620979094553265 22734513445215734320914949)
                  ·
                    refine ⟨4262721270977950185171553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22734513445215734320914949 4262721270977950185171553)
                    ·
                      refine ⟨3197040953233462638878665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262721270977950185171553 3197040953233462638878665)
                      ·
                        rfl

theorem cell23_6226215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6226215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226215 prefixEnd_6226215 := by exact prefixLift 6226215
  have htrace : WordTrace (prefixWord ++ tailWord_6226215) baseStart_6226215 baseEnd_6226215 := by
    simpa [prefixWord, tailWord_6226215, baseEnd_6226215] using wordTrace_append hprefix tailTrace_6226215
  have hstable : (prefixWord ++ tailWord_6226215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226215).length < 2 ^ (prefixWord ++ tailWord_6226215).sum := by decide
  have hdescent : baseEnd_6226215 < baseStart_6226215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226247 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 1, 6]
def baseStart_6226247 : Nat := 118140960795 + 6226247 * 2 ^ 59
def prefixEnd_6226247 : Nat := 4983230072969 + 3 ^ 40 * 6226247 * 2
def baseEnd_6226247 : Nat := 1065685794871468837892839

theorem tailTrace_6226247 : CollatzResearch.WordTrace tailWord_6226247 prefixEnd_6226247 1065685794871468837892839 := by
  unfold tailWord_6226247
  simp only [CollatzResearch.WordTrace]
  refine ⟨227089884274377952174428995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151393256182918634782952663 227089884274377952174428995)
  ·
    refine ⟨340634826411566928261643493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227089884274377952174428995 340634826411566928261643493)
    ·
      refine ⟨63869029952168799049058155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340634826411566928261643493 63869029952168799049058155)
      ·
        refine ⟨95803544928253198573587233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63869029952168799049058155 95803544928253198573587233)
        ·
          refine ⟨71852658696189898930190425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95803544928253198573587233 71852658696189898930190425)
          ·
            refine ⟨53889494022142424197642819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71852658696189898930190425 53889494022142424197642819)
            ·
              refine ⟨80834241033213636296464229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53889494022142424197642819 80834241033213636296464229)
              ·
                refine ⟨15156420193727556805587043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80834241033213636296464229 15156420193727556805587043)
                ·
                  refine ⟨22734630290591335208380565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15156420193727556805587043 22734630290591335208380565)
                  ·
                    refine ⟨1065685794871468837892839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22734630290591335208380565 1065685794871468837892839)
                    ·
                      rfl

theorem cell23_6226247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_6226247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226247 prefixEnd_6226247 := by exact prefixLift 6226247
  have htrace : WordTrace (prefixWord ++ tailWord_6226247) baseStart_6226247 baseEnd_6226247 := by
    simpa [prefixWord, tailWord_6226247, baseEnd_6226247] using wordTrace_append hprefix tailTrace_6226247
  have hstable : (prefixWord ++ tailWord_6226247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226247).length < 2 ^ (prefixWord ++ tailWord_6226247).sum := by decide
  have hdescent : baseEnd_6226247 < baseStart_6226247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226264 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 2, 4]
def baseStart_6226264 : Nat := 118140960795 + 6226264 * 2 ^ 59
def prefixEnd_6226264 : Nat := 4983230072969 + 3 ^ 40 * 6226264 * 2
def baseEnd_6226264 : Nat := 1065688704595177649055313

theorem tailTrace_6226264 : CollatzResearch.WordTrace tailWord_6226264 prefixEnd_6226264 1065688704595177649055313 := by
  unfold tailWord_6226264
  simp only [CollatzResearch.WordTrace]
  refine ⟨113545252157658182038898923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151393669543544242718531897 113545252157658182038898923)
  ·
    refine ⟨170317878236487273058348385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113545252157658182038898923 170317878236487273058348385)
    ·
      refine ⟨127738408677365454793761289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170317878236487273058348385 127738408677365454793761289)
      ·
        refine ⟨95803806508024091095320967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127738408677365454793761289 95803806508024091095320967)
        ·
          refine ⟨143705709762036136642981451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95803806508024091095320967 143705709762036136642981451)
          ·
            refine ⟨215558564643054204964472177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143705709762036136642981451 215558564643054204964472177)
            ·
              refine ⟨161668923482290653723354133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215558564643054204964472177 161668923482290653723354133)
              ·
                refine ⟨7578230788232374393282225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161668923482290653723354133 7578230788232374393282225)
                ·
                  refine ⟨5683673091174280794961669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578230788232374393282225 5683673091174280794961669)
                  ·
                    refine ⟨1065688704595177649055313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683673091174280794961669 1065688704595177649055313)
                    ·
                      rfl

theorem cell23_6226264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_6226264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226264 prefixEnd_6226264 := by exact prefixLift 6226264
  have htrace : WordTrace (prefixWord ++ tailWord_6226264) baseStart_6226264 baseEnd_6226264 := by
    simpa [prefixWord, tailWord_6226264, baseEnd_6226264] using wordTrace_append hprefix tailTrace_6226264
  have hstable : (prefixWord ++ tailWord_6226264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226264).length < 2 ^ (prefixWord ++ tailWord_6226264).sum := by decide
  have hdescent : baseEnd_6226264 < baseStart_6226264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226271 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 3, 2, 2]
def baseStart_6226271 : Nat := 118140960795 + 6226271 * 2 ^ 59
def prefixEnd_6226271 : Nat := 4983230072969 + 3 ^ 40 * 6226271 * 2
def baseEnd_6226271 : Nat := 3197069708150114419778407

theorem tailTrace_6226271 : CollatzResearch.WordTrace tailWord_6226271 prefixEnd_6226271 3197069708150114419778407 := by
  unfold tailWord_6226271
  simp only [CollatzResearch.WordTrace]
  refine ⟨227090759626291004273302667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151393839750860669515535111 227090759626291004273302667)
  ·
    refine ⟨340636139439436506409954001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227090759626291004273302667 340636139439436506409954001)
    ·
      refine ⟨255477104579577379807465501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340636139439436506409954001 255477104579577379807465501)
      ·
        refine ⟨95803914217341517427799563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255477104579577379807465501 95803914217341517427799563)
        ·
          refine ⟨143705871326012276141699345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95803914217341517427799563 143705871326012276141699345)
          ·
            refine ⟨107779403494509207106274509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143705871326012276141699345 107779403494509207106274509)
            ·
              refine ⟨40417276310440952664852941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107779403494509207106274509 40417276310440952664852941)
              ·
                refine ⟨15156478616415357249319853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40417276310440952664852941 15156478616415357249319853)
                ·
                  refine ⟨5683679481155758968494945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15156478616415357249319853 5683679481155758968494945)
                  ·
                    refine ⟨4262759610866819226371209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5683679481155758968494945 4262759610866819226371209)
                    ·
                      refine ⟨3197069708150114419778407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262759610866819226371209 3197069708150114419778407)
                      ·
                        rfl

theorem cell23_6226271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_6226271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226271 prefixEnd_6226271 := by exact prefixLift 6226271
  have htrace : WordTrace (prefixWord ++ tailWord_6226271) baseStart_6226271 baseEnd_6226271 := by
    simpa [prefixWord, tailWord_6226271, baseEnd_6226271] using wordTrace_append hprefix tailTrace_6226271
  have hstable : (prefixWord ++ tailWord_6226271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226271).length < 2 ^ (prefixWord ++ tailWord_6226271).sum := by decide
  have hdescent : baseEnd_6226271 < baseStart_6226271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226274 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6226274 : Nat := 118140960795 + 6226274 * 2 ^ 59
def prefixEnd_6226274 : Nat := 4983230072969 + 3 ^ 40 * 6226274 * 2
def baseEnd_6226274 : Nat := 3197071248592077908040893

theorem tailTrace_6226274 : CollatzResearch.WordTrace tailWord_6226274 prefixEnd_6226274 3197071248592077908040893 := by
  unfold tailWord_6226274
  simp only [CollatzResearch.WordTrace]
  refine ⟨56772717261320033946415469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151393912696853423857107917 56772717261320033946415469)
  ·
    refine ⟨21289768972995012729905801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56772717261320033946415469 21289768972995012729905801)
    ·
      refine ⟨15967326729746259547429351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21289768972995012729905801 15967326729746259547429351)
      ·
        refine ⟨23950990094619389321144027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15967326729746259547429351 23950990094619389321144027)
        ·
          refine ⟨35926485141929083981716041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23950990094619389321144027 35926485141929083981716041)
          ·
            refine ⟨26944863856446812986287031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35926485141929083981716041 26944863856446812986287031)
            ·
              refine ⟨40417295784670219479430547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26944863856446812986287031 40417295784670219479430547)
              ·
                refine ⟨60625943677005329219145821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40417295784670219479430547 60625943677005329219145821)
                ·
                  refine ⟨22734728878876998457179683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60625943677005329219145821 22734728878876998457179683)
                  ·
                    refine ⟨34102093318315497685769525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22734728878876998457179683 34102093318315497685769525)
                    ·
                      refine ⟨3197071248592077908040893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34102093318315497685769525 3197071248592077908040893)
                      ·
                        rfl

theorem cell23_6226274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6226274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226274 prefixEnd_6226274 := by exact prefixLift 6226274
  have htrace : WordTrace (prefixWord ++ tailWord_6226274) baseStart_6226274 baseEnd_6226274 := by
    simpa [prefixWord, tailWord_6226274, baseEnd_6226274] using wordTrace_append hprefix tailTrace_6226274
  have hstable : (prefixWord ++ tailWord_6226274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226274).length < 2 ^ (prefixWord ++ tailWord_6226274).sum := by decide
  have hdescent : baseEnd_6226274 < baseStart_6226274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226281 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 2, 4]
def baseStart_6226281 : Nat := 118140960795 + 6226281 * 2 ^ 59
def prefixEnd_6226281 : Nat := 4983230072969 + 3 ^ 40 * 6226281 * 2
def baseEnd_6226281 : Nat := 1065691614318886460217787

theorem tailTrace_6226281 : CollatzResearch.WordTrace tailWord_6226281 prefixEnd_6226281 1065691614318886460217787 := by
  unfold tailWord_6226281
  simp only [CollatzResearch.WordTrace]
  refine ⟨227091124356254775981166697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151394082904169850654111131 227091124356254775981166697)
  ·
    refine ⟨170318343267191081985875023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227091124356254775981166697 170318343267191081985875023)
    ·
      refine ⟨255477514900786622978812535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170318343267191081985875023 255477514900786622978812535)
      ·
        refine ⟨383216272351179934468218803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255477514900786622978812535 383216272351179934468218803)
        ·
          refine ⟨574824408526769901702328205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383216272351179934468218803 574824408526769901702328205)
          ·
            refine ⟨215559153197538713138373077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574824408526769901702328205 215559153197538713138373077)
            ·
              refine ⟨5052167653067313589180619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 215559153197538713138373077 5052167653067313589180619)
              ·
                refine ⟨7578251479600970383770929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052167653067313589180619 7578251479600970383770929)
                ·
                  refine ⟨5683688609700727787828197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578251479600970383770929 5683688609700727787828197)
                  ·
                    refine ⟨1065691614318886460217787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683688609700727787828197 1065691614318886460217787)
                    ·
                      rfl

theorem cell23_6226281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 4].length) (baseStart_6226281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226281 prefixEnd_6226281 := by exact prefixLift 6226281
  have htrace : WordTrace (prefixWord ++ tailWord_6226281) baseStart_6226281 baseEnd_6226281 := by
    simpa [prefixWord, tailWord_6226281, baseEnd_6226281] using wordTrace_append hprefix tailTrace_6226281
  have hstable : (prefixWord ++ tailWord_6226281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226281).length < 2 ^ (prefixWord ++ tailWord_6226281).sum := by decide
  have hdescent : baseEnd_6226281 < baseStart_6226281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226284 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_6226284 : Nat := 118140960795 + 6226284 * 2 ^ 59
def prefixEnd_6226284 : Nat := 4983230072969 + 3 ^ 40 * 6226284 * 2
def baseEnd_6226284 : Nat := 3197076383398622868915847

theorem tailTrace_6226284 : CollatzResearch.WordTrace tailWord_6226284 prefixEnd_6226284 3197076383398622868915847 := by
  unfold tailWord_6226284
  simp only [CollatzResearch.WordTrace]
  refine ⟨113545616887621953746762953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151394155850162604995683937 113545616887621953746762953)
  ·
    refine ⟨85159212665716465310072215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113545616887621953746762953 85159212665716465310072215)
    ·
      refine ⟨127738818998574697965108323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85159212665716465310072215 127738818998574697965108323)
      ·
        refine ⟨191608228497862046947662485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127738818998574697965108323 191608228497862046947662485)
        ·
          refine ⟨8981635710837283450671679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191608228497862046947662485 8981635710837283450671679)
          ·
            refine ⟨13472453566255925176007519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981635710837283450671679 13472453566255925176007519)
            ·
              refine ⟨20208680349383887764011279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13472453566255925176007519 20208680349383887764011279)
              ·
                refine ⟨30313020524075831646016919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20208680349383887764011279 30313020524075831646016919)
                ·
                  refine ⟨45469530786113747469025379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30313020524075831646016919 45469530786113747469025379)
                  ·
                    refine ⟨68204296179170621203538069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45469530786113747469025379 68204296179170621203538069)
                    ·
                      refine ⟨3197076383398622868915847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68204296179170621203538069 3197076383398622868915847)
                      ·
                        rfl

theorem cell23_6226284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_6226284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226284 prefixEnd_6226284 := by exact prefixLift 6226284
  have htrace : WordTrace (prefixWord ++ tailWord_6226284) baseStart_6226284 baseEnd_6226284 := by
    simpa [prefixWord, tailWord_6226284, baseEnd_6226284] using wordTrace_append hprefix tailTrace_6226284
  have hstable : (prefixWord ++ tailWord_6226284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226284).length < 2 ^ (prefixWord ++ tailWord_6226284).sum := by decide
  have hdescent : baseEnd_6226284 < baseStart_6226284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226338 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_6226338 : Nat := 118140960795 + 6226338 * 2 ^ 59
def prefixEnd_6226338 : Nat := 4983230072969 + 3 ^ 40 * 6226338 * 2
def baseEnd_6226338 : Nat := 3197104111353965657640599

theorem tailTrace_6226338 : CollatzResearch.WordTrace tailWord_6226338 prefixEnd_6226338 3197104111353965657640599 := by
  unfold tailWord_6226338
  simp only [CollatzResearch.WordTrace]
  refine ⟨56773300829262068678997917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151395468878032183143994445 56773300829262068678997917)
  ·
    refine ⟨21289987810973275754624219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56773300829262068678997917 21289987810973275754624219)
    ·
      refine ⟨31934981716459913631936329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21289987810973275754624219 31934981716459913631936329)
      ·
        refine ⟨23951236287344935223952247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31934981716459913631936329 23951236287344935223952247)
        ·
          refine ⟨35926854431017402835928371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23951236287344935223952247 35926854431017402835928371)
          ·
            refine ⟨53890281646526104253892557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35926854431017402835928371 53890281646526104253892557)
            ·
              refine ⟨20208855617447289095209709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53890281646526104253892557 20208855617447289095209709)
              ·
                refine ⟨7578320856542733410703641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20208855617447289095209709 7578320856542733410703641)
                ·
                  refine ⟨5683740642407050058027731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578320856542733410703641 5683740642407050058027731)
                  ·
                    refine ⟨8525610963610575087041597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683740642407050058027731 8525610963610575087041597)
                    ·
                      refine ⟨3197104111353965657640599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8525610963610575087041597 3197104111353965657640599)
                      ·
                        rfl

theorem cell23_6226338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_6226338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226338 prefixEnd_6226338 := by exact prefixLift 6226338
  have htrace : WordTrace (prefixWord ++ tailWord_6226338) baseStart_6226338 baseEnd_6226338 := by
    simpa [prefixWord, tailWord_6226338, baseEnd_6226338] using wordTrace_append hprefix tailTrace_6226338
  have hstable : (prefixWord ++ tailWord_6226338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226338).length < 2 ^ (prefixWord ++ tailWord_6226338).sum := by decide
  have hdescent : baseEnd_6226338 < baseStart_6226338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226361 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6226361 : Nat := 118140960795 + 6226361 * 2 ^ 59
def prefixEnd_6226361 : Nat := 4983230072969 + 3 ^ 40 * 6226361 * 2
def baseEnd_6226361 : Nat := 3197115921409019067652993

theorem tailTrace_6226361 : CollatzResearch.WordTrace tailWord_6226361 prefixEnd_6226361 3197115921409019067652993 := by
  unfold tailWord_6226361
  simp only [CollatzResearch.WordTrace]
  refine ⟨227094042195964949644078937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151396028130643299762719291 227094042195964949644078937)
  ·
    refine ⟨170320531646973712233059203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227094042195964949644078937 170320531646973712233059203)
    ·
      refine ⟨255480797470460568349588805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170320531646973712233059203 255480797470460568349588805)
      ·
        refine ⟨47902649525711356565547901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255480797470460568349588805 47902649525711356565547901)
        ·
          refine ⟨17963493572141758712080463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47902649525711356565547901 17963493572141758712080463)
          ·
            refine ⟨26945240358212638068120695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17963493572141758712080463 26945240358212638068120695)
            ·
              refine ⟨40417860537318957102181043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26945240358212638068120695 40417860537318957102181043)
              ·
                refine ⟨60626790805978435653271565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40417860537318957102181043 60626790805978435653271565)
                ·
                  refine ⟨22735046552241913369976837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60626790805978435653271565 22735046552241913369976837)
                  ·
                    refine ⟨4262821228545358756870657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22735046552241913369976837 4262821228545358756870657)
                    ·
                      refine ⟨3197115921409019067652993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262821228545358756870657 3197115921409019067652993)
                      ·
                        rfl

theorem cell23_6226361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6226361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226361 prefixEnd_6226361 := by exact prefixLift 6226361
  have htrace : WordTrace (prefixWord ++ tailWord_6226361) baseStart_6226361 baseEnd_6226361 := by
    simpa [prefixWord, tailWord_6226361, baseEnd_6226361] using wordTrace_append hprefix tailTrace_6226361
  have hstable : (prefixWord ++ tailWord_6226361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226361).length < 2 ^ (prefixWord ++ tailWord_6226361).sum := by decide
  have hdescent : baseEnd_6226361 < baseStart_6226361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226365 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_6226365 : Nat := 118140960795 + 6226365 * 2 ^ 59
def prefixEnd_6226365 : Nat := 4983230072969 + 3 ^ 40 * 6226365 * 2
def baseEnd_6226365 : Nat := 3197117975331637052002975

theorem tailTrace_6226365 : CollatzResearch.WordTrace tailWord_6226365 prefixEnd_6226365 3197117975331637052002975 := by
  unfold tailWord_6226365
  simp only [CollatzResearch.WordTrace]
  refine ⟨227094188087950458327224549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151396125391966972218149699 227094188087950458327224549)
  ·
    refine ⟨42580160266490710936354603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227094188087950458327224549 42580160266490710936354603)
    ·
      refine ⟨63870240399736066404531905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42580160266490710936354603 63870240399736066404531905)
      ·
        refine ⟨47902680299802049803398929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63870240399736066404531905 47902680299802049803398929)
        ·
          refine ⟨35927010224851537352549197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47902680299802049803398929 35927010224851537352549197)
          ·
            refine ⟨13472628834319326507205949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35927010224851537352549197 13472628834319326507205949)
            ·
              refine ⟨5052235812869747440202231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13472628834319326507205949 5052235812869747440202231)
              ·
                refine ⟨7578353719304621160303347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052235812869747440202231 7578353719304621160303347)
                ·
                  refine ⟨11367530578956931740455021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7578353719304621160303347 11367530578956931740455021)
                  ·
                    refine ⟨4262823967108849402670633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11367530578956931740455021 4262823967108849402670633)
                    ·
                      refine ⟨3197117975331637052002975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262823967108849402670633 3197117975331637052002975)
                      ·
                        rfl

theorem cell23_6226365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_6226365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226365 prefixEnd_6226365 := by exact prefixLift 6226365
  have htrace : WordTrace (prefixWord ++ tailWord_6226365) baseStart_6226365 baseEnd_6226365 := by
    simpa [prefixWord, tailWord_6226365, baseEnd_6226365] using wordTrace_append hprefix tailTrace_6226365
  have hstable : (prefixWord ++ tailWord_6226365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226365).length < 2 ^ (prefixWord ++ tailWord_6226365).sum := by decide
  have hdescent : baseEnd_6226365 < baseStart_6226365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226377 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_6226377 : Nat := 118140960795 + 6226377 * 2 ^ 59
def prefixEnd_6226377 : Nat := 4983230072969 + 3 ^ 40 * 6226377 * 2
def baseEnd_6226377 : Nat := 3197124137099491005052919

theorem tailTrace_6226377 : CollatzResearch.WordTrace tailWord_6226377 prefixEnd_6226377 3197124137099491005052919 := by
  unfold tailWord_6226377
  simp only [CollatzResearch.WordTrace]
  refine ⟨227094625763906984376661385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151396417175937989584440923 227094625763906984376661385)
  ·
    refine ⟨170320969322930238282496039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227094625763906984376661385 170320969322930238282496039)
    ·
      refine ⟨255481453984395357423744059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170320969322930238282496039 255481453984395357423744059)
      ·
        refine ⟨383222180976593036135616089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255481453984395357423744059 383222180976593036135616089)
        ·
          refine ⟨287416635732444777101712067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383222180976593036135616089 287416635732444777101712067)
          ·
            refine ⟨431124953598667165652568101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287416635732444777101712067 431124953598667165652568101)
            ·
              refine ⟨80835928799750093559856519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431124953598667165652568101 80835928799750093559856519)
              ·
                refine ⟨121253893199625140339784779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80835928799750093559856519 121253893199625140339784779)
                ·
                  refine ⟨181880839799437710509677169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121253893199625140339784779 181880839799437710509677169)
                  ·
                    refine ⟨136410629849578282882257877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181880839799437710509677169 136410629849578282882257877)
                    ·
                      refine ⟨3197124137099491005052919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136410629849578282882257877 3197124137099491005052919)
                      ·
                        rfl

theorem cell23_6226377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_6226377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226377 prefixEnd_6226377 := by exact prefixLift 6226377
  have htrace : WordTrace (prefixWord ++ tailWord_6226377) baseStart_6226377 baseEnd_6226377 := by
    simpa [prefixWord, tailWord_6226377, baseEnd_6226377] using wordTrace_append hprefix tailTrace_6226377
  have hstable : (prefixWord ++ tailWord_6226377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226377).length < 2 ^ (prefixWord ++ tailWord_6226377).sum := by decide
  have hdescent : baseEnd_6226377 < baseStart_6226377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226445 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6226445 : Nat := 118140960795 + 6226445 * 2 ^ 59
def prefixEnd_6226445 : Nat := 4983230072969 + 3 ^ 40 * 6226445 * 2
def baseEnd_6226445 : Nat := 3197159053783996739002607

theorem tailTrace_6226445 : CollatzResearch.WordTrace tailWord_6226445 prefixEnd_6226445 3197159053783996739002607 := by
  unfold tailWord_6226445
  simp only [CollatzResearch.WordTrace]
  refine ⟨227097105927660631990136789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151398070618440421326757859 227097105927660631990136789)
  ·
    refine ⟨5322588420179546062268831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 227097105927660631990136789 5322588420179546062268831)
    ·
      refine ⟨7983882630269319093403247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5322588420179546062268831 7983882630269319093403247)
      ·
        refine ⟨11975823945403978640104871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7983882630269319093403247 11975823945403978640104871)
        ·
          refine ⟨17963735918105967960157307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11975823945403978640104871 17963735918105967960157307)
          ·
            refine ⟨26945603877158951940235961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17963735918105967960157307 26945603877158951940235961)
            ·
              refine ⟨20209202907869213955176971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26945603877158951940235961 20209202907869213955176971)
              ·
                refine ⟨30313804361803820932765457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20209202907869213955176971 30313804361803820932765457)
                ·
                  refine ⟨22735353271352865699574093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30313804361803820932765457 22735353271352865699574093)
                  ·
                    refine ⟨8525757476757324637340285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22735353271352865699574093 8525757476757324637340285)
                    ·
                      refine ⟨3197159053783996739002607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8525757476757324637340285 3197159053783996739002607)
                      ·
                        rfl

theorem cell23_6226445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6226445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226445 prefixEnd_6226445 := by exact prefixLift 6226445
  have htrace : WordTrace (prefixWord ++ tailWord_6226445) baseStart_6226445 baseEnd_6226445 := by
    simpa [prefixWord, tailWord_6226445, baseEnd_6226445] using wordTrace_append hprefix tailTrace_6226445
  have hstable : (prefixWord ++ tailWord_6226445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226445).length < 2 ^ (prefixWord ++ tailWord_6226445).sum := by decide
  have hdescent : baseEnd_6226445 < baseStart_6226445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226451 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 2, 4, 2]
def baseStart_6226451 : Nat := 118140960795 + 6226451 * 2 ^ 59
def prefixEnd_6226451 : Nat := 4983230072969 + 3 ^ 40 * 6226451 * 2
def baseEnd_6226451 : Nat := 3197162134667923715527579

theorem tailTrace_6226451 : CollatzResearch.WordTrace tailWord_6226451 prefixEnd_6226451 3197162134667923715527579 := by
  unfold tailWord_6226451
  simp only [CollatzResearch.WordTrace]
  refine ⟨227097324765638895014855207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151398216510425930009903471 227097324765638895014855207)
  ·
    refine ⟨340645987148458342522282811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227097324765638895014855207 340645987148458342522282811)
    ·
      refine ⟨510968980722687513783424217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340645987148458342522282811 510968980722687513783424217)
      ·
        refine ⟨383226735542015635337568163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510968980722687513783424217 383226735542015635337568163)
        ·
          refine ⟨574840103313023453006352245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383226735542015635337568163 574840103313023453006352245)
          ·
            refine ⟨53891259685595948719345523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 574840103313023453006352245 53891259685595948719345523)
            ·
              refine ⟨80836889528393923079018285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53891259685595948719345523 80836889528393923079018285)
              ·
                refine ⟨30313833573147721154631857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80836889528393923079018285 30313833573147721154631857)
                ·
                  refine ⟨22735375179860790865973893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30313833573147721154631857 22735375179860790865973893)
                  ·
                    refine ⟨4262882846223898287370105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22735375179860790865973893 4262882846223898287370105)
                    ·
                      refine ⟨3197162134667923715527579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262882846223898287370105 3197162134667923715527579)
                      ·
                        rfl

theorem cell23_6226451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4, 2].length) (baseStart_6226451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226451 prefixEnd_6226451 := by exact prefixLift 6226451
  have htrace : WordTrace (prefixWord ++ tailWord_6226451) baseStart_6226451 baseEnd_6226451 := by
    simpa [prefixWord, tailWord_6226451, baseEnd_6226451] using wordTrace_append hprefix tailTrace_6226451
  have hstable : (prefixWord ++ tailWord_6226451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226451).length < 2 ^ (prefixWord ++ tailWord_6226451).sum := by decide
  have hdescent : baseEnd_6226451 < baseStart_6226451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226495 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 1, 4]
def baseStart_6226495 : Nat := 118140960795 + 6226495 * 2 ^ 59
def prefixEnd_6226495 : Nat := 4983230072969 + 3 ^ 40 * 6226495 * 2
def baseEnd_6226495 : Nat := 1065728242605573847792459

theorem tailTrace_6226495 : CollatzResearch.WordTrace tailWord_6226495 prefixEnd_6226495 1065728242605573847792459 := by
  unfold tailWord_6226495
  simp only [CollatzResearch.WordTrace]
  refine ⟨227098929577479490529456939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151399286384986327019637959 227098929577479490529456939)
  ·
    refine ⟨340648394366219235794185409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227098929577479490529456939 340648394366219235794185409)
    ·
      refine ⟨255486295774664426845639057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340648394366219235794185409 255486295774664426845639057)
      ·
        refine ⟨191614721830998320134229293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255486295774664426845639057 191614721830998320134229293)
        ·
          refine ⟨71855520686624370050335985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191614721830998320134229293 71855520686624370050335985)
          ·
            refine ⟨53891640514968277537751989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71855520686624370050335985 53891640514968277537751989)
            ·
              refine ⟨5052341298278276019164249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53891640514968277537751989 5052341298278276019164249)
              ·
                refine ⟨3789255973708707014373187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052341298278276019164249 3789255973708707014373187)
                ·
                  refine ⟨5683883960563060521559781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789255973708707014373187 5683883960563060521559781)
                  ·
                    refine ⟨1065728242605573847792459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683883960563060521559781 1065728242605573847792459)
                    ·
                      rfl

theorem cell23_6226495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 4].length) (baseStart_6226495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226495 prefixEnd_6226495 := by exact prefixLift 6226495
  have htrace : WordTrace (prefixWord ++ tailWord_6226495) baseStart_6226495 baseEnd_6226495 := by
    simpa [prefixWord, tailWord_6226495, baseEnd_6226495] using wordTrace_append hprefix tailTrace_6226495
  have hstable : (prefixWord ++ tailWord_6226495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226495).length < 2 ^ (prefixWord ++ tailWord_6226495).sum := by decide
  have hdescent : baseEnd_6226495 < baseStart_6226495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226511 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 3, 5, 2]
def baseStart_6226511 : Nat := 118140960795 + 6226511 * 2 ^ 59
def prefixEnd_6226511 : Nat := 4983230072969 + 3 ^ 40 * 6226511 * 2
def baseEnd_6226511 : Nat := 3197192943507193480777303

theorem tailTrace_6226511 : CollatzResearch.WordTrace tailWord_6226511 prefixEnd_6226511 3197192943507193480777303 := by
  unfold tailWord_6226511
  simp only [CollatzResearch.WordTrace]
  refine ⟨227099513145421525262039387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151399675430281016841359591 227099513145421525262039387)
  ·
    refine ⟨340649269718132287893059081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227099513145421525262039387 340649269718132287893059081)
    ·
      refine ⟨255486952288599215919794311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340649269718132287893059081 255486952288599215919794311)
      ·
        refine ⟨383230428432898823879691467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255486952288599215919794311 383230428432898823879691467)
        ·
          refine ⟨574845642649348235819537201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383230428432898823879691467 574845642649348235819537201)
          ·
            refine ⟨431134231987011176864652901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574845642649348235819537201 431134231987011176864652901)
            ·
              refine ⟨80837668497564595662122419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431134231987011176864652901 80837668497564595662122419)
              ·
                refine ⟨121256502746346893493183629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80837668497564595662122419 121256502746346893493183629)
                ·
                  refine ⟨45471188529880085059943861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121256502746346893493183629 45471188529880085059943861)
                  ·
                    refine ⟨4262923924676257974369737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45471188529880085059943861 4262923924676257974369737)
                    ·
                      refine ⟨3197192943507193480777303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262923924676257974369737 3197192943507193480777303)
                      ·
                        rfl

theorem cell23_6226511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5, 2].length) (baseStart_6226511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226511 prefixEnd_6226511 := by exact prefixLift 6226511
  have htrace : WordTrace (prefixWord ++ tailWord_6226511) baseStart_6226511 baseEnd_6226511 := by
    simpa [prefixWord, tailWord_6226511, baseEnd_6226511] using wordTrace_append hprefix tailTrace_6226511
  have hstable : (prefixWord ++ tailWord_6226511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226511).length < 2 ^ (prefixWord ++ tailWord_6226511).sum := by decide
  have hdescent : baseEnd_6226511 < baseStart_6226511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226528 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 2, 3, 2]
def baseStart_6226528 : Nat := 118140960795 + 6226528 * 2 ^ 59
def prefixEnd_6226528 : Nat := 4983230072969 + 3 ^ 40 * 6226528 * 2
def baseEnd_6226528 : Nat := 3197201672678319914264725

theorem tailTrace_6226528 : CollatzResearch.WordTrace tailWord_6226528 prefixEnd_6226528 3197201672678319914264725 := by
  unfold tailWord_6226528
  simp only [CollatzResearch.WordTrace]
  refine ⟨113550066593179968582704119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151400088790906624776938825 113550066593179968582704119)
  ·
    refine ⟨170325099889769952874056179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113550066593179968582704119 170325099889769952874056179)
    ·
      refine ⟨255487649834654929311084269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170325099889769952874056179 255487649834654929311084269)
      ·
        refine ⟨95807868687995598491656601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255487649834654929311084269 95807868687995598491656601)
        ·
          refine ⟨71855901515996698868742451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95807868687995598491656601 71855901515996698868742451)
          ·
            refine ⟨107783852273995048303113677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71855901515996698868742451 107783852273995048303113677)
            ·
              refine ⟨40418944602748143113667629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107783852273995048303113677 40418944602748143113667629)
              ·
                refine ⟨15157104226030553667625361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40418944602748143113667629 15157104226030553667625361)
                ·
                  refine ⟨11367828169522915250719021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15157104226030553667625361 11367828169522915250719021)
                  ·
                    refine ⟨4262935563571093219019633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11367828169522915250719021 4262935563571093219019633)
                    ·
                      refine ⟨3197201672678319914264725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262935563571093219019633 3197201672678319914264725)
                      ·
                        rfl

theorem cell23_6226528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_6226528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226528 prefixEnd_6226528 := by exact prefixLift 6226528
  have htrace : WordTrace (prefixWord ++ tailWord_6226528) baseStart_6226528 baseEnd_6226528 := by
    simpa [prefixWord, tailWord_6226528, baseEnd_6226528] using wordTrace_append hprefix tailTrace_6226528
  have hstable : (prefixWord ++ tailWord_6226528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226528).length < 2 ^ (prefixWord ++ tailWord_6226528).sum := by decide
  have hdescent : baseEnd_6226528 < baseStart_6226528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226535 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_6226535 : Nat := 118140960795 + 6226535 * 2 ^ 59
def prefixEnd_6226535 : Nat := 4983230072969 + 3 ^ 40 * 6226535 * 2
def baseEnd_6226535 : Nat := 3197205267042901386877193

theorem tailTrace_6226535 : CollatzResearch.WordTrace tailWord_6226535 prefixEnd_6226535 3197205267042901386877193 := by
  unfold tailWord_6226535
  simp only [CollatzResearch.WordTrace]
  refine ⟨227100388497334577360913059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151400258998223051573942039 227100388497334577360913059)
  ·
    refine ⟨340650582746001866041369589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227100388497334577360913059 340650582746001866041369589)
    ·
      refine ⟨31935992132437674941378399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340650582746001866041369589 31935992132437674941378399)
      ·
        refine ⟨47903988198656512412067599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31935992132437674941378399 47903988198656512412067599)
        ·
          refine ⟨71855982297984768618101399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47903988198656512412067599 71855982297984768618101399)
          ·
            refine ⟨107783973446977152927152099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71855982297984768618101399 107783973446977152927152099)
            ·
              refine ⟨161675960170465729390728149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107783973446977152927152099 161675960170465729390728149)
              ·
                refine ⟨3789280316495290532595191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161675960170465729390728149 3789280316495290532595191)
                ·
                  refine ⟨5683920474742935798892787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789280316495290532595191 5683920474742935798892787)
                  ·
                    refine ⟨8525880712114403698339181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683920474742935798892787 8525880712114403698339181)
                    ·
                      refine ⟨3197205267042901386877193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8525880712114403698339181 3197205267042901386877193)
                      ·
                        rfl

theorem cell23_6226535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_6226535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226535 prefixEnd_6226535 := by exact prefixLift 6226535
  have htrace : WordTrace (prefixWord ++ tailWord_6226535) baseStart_6226535 baseEnd_6226535 := by
    simpa [prefixWord, tailWord_6226535, baseEnd_6226535] using wordTrace_append hprefix tailTrace_6226535
  have hstable : (prefixWord ++ tailWord_6226535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226535).length < 2 ^ (prefixWord ++ tailWord_6226535).sum := by decide
  have hdescent : baseEnd_6226535 < baseStart_6226535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226551 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 4, 4]
def baseStart_6226551 : Nat := 118140960795 + 6226551 * 2 ^ 59
def prefixEnd_6226551 : Nat := 4983230072969 + 3 ^ 40 * 6226551 * 2
def baseEnd_6226551 : Nat := 1065737827577791108092373

theorem tailTrace_6226551 : CollatzResearch.WordTrace tailWord_6226551 prefixEnd_6226551 1065737827577791108092373 := by
  unfold tailWord_6226551
  simp only [CollatzResearch.WordTrace]
  refine ⟨227100972065276612093495507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151400648043517741395663671 227100972065276612093495507)
  ·
    refine ⟨340651458097914918140243261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227100972065276612093495507 340651458097914918140243261)
    ·
      refine ⟨127744296786718094302591223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340651458097914918140243261 127744296786718094302591223)
      ·
        refine ⟨191616445180077141453886835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127744296786718094302591223 191616445180077141453886835)
        ·
          refine ⟨287424667770115712180830253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191616445180077141453886835 287424667770115712180830253)
          ·
            refine ⟨107784250413793392067811345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287424667770115712180830253 107784250413793392067811345)
            ·
              refine ⟨80838187810345044050858509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107784250413793392067811345 80838187810345044050858509)
              ·
                refine ⟨30314320428879391519071941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80838187810345044050858509 30314320428879391519071941)
                ·
                  refine ⟨5683935080414885909825989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30314320428879391519071941 5683935080414885909825989)
                  ·
                    refine ⟨1065737827577791108092373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683935080414885909825989 1065737827577791108092373)
                    ·
                      rfl

theorem cell23_6226551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_6226551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226551 prefixEnd_6226551 := by exact prefixLift 6226551
  have htrace : WordTrace (prefixWord ++ tailWord_6226551) baseStart_6226551 baseEnd_6226551 := by
    simpa [prefixWord, tailWord_6226551, baseEnd_6226551] using wordTrace_append hprefix tailTrace_6226551
  have hstable : (prefixWord ++ tailWord_6226551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226551).length < 2 ^ (prefixWord ++ tailWord_6226551).sum := by decide
  have hdescent : baseEnd_6226551 < baseStart_6226551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226561 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6226561 : Nat := 118140960795 + 6226561 * 2 ^ 59
def prefixEnd_6226561 : Nat := 4983230072969 + 3 ^ 40 * 6226561 * 2
def baseEnd_6226561 : Nat := 3197218617539918285152073

theorem tailTrace_6226561 : CollatzResearch.WordTrace tailWord_6226561 prefixEnd_6226561 3197218617539918285152073 := by
  unfold tailWord_6226561
  simp only [CollatzResearch.WordTrace]
  refine ⟨227101336795240383801359537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151400891196826922534239691 227101336795240383801359537)
  ·
    refine ⟨170326002596430287851019653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227101336795240383801359537 170326002596430287851019653)
    ·
      refine ⟨31936125486830678972066185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170326002596430287851019653 31936125486830678972066185)
      ·
        refine ⟨23952094115123009229049639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31936125486830678972066185 23952094115123009229049639)
        ·
          refine ⟨35928141172684513843574459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23952094115123009229049639 35928141172684513843574459)
          ·
            refine ⟨53892211759026770765361689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35928141172684513843574459 53892211759026770765361689)
            ·
              refine ⟨40419158819270078074021267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53892211759026770765361689 40419158819270078074021267)
              ·
                refine ⟨60628738228905117111031901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40419158819270078074021267 60628738228905117111031901)
                ·
                  refine ⟨22735776835839418916636963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60628738228905117111031901 22735776835839418916636963)
                  ·
                    refine ⟨34103665253759128374955445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22735776835839418916636963 34103665253759128374955445)
                    ·
                      refine ⟨3197218617539918285152073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34103665253759128374955445 3197218617539918285152073)
                      ·
                        rfl

theorem cell23_6226561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6226561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226561 prefixEnd_6226561 := by exact prefixLift 6226561
  have htrace : WordTrace (prefixWord ++ tailWord_6226561) baseStart_6226561 baseEnd_6226561 := by
    simpa [prefixWord, tailWord_6226561, baseEnd_6226561] using wordTrace_append hprefix tailTrace_6226561
  have hstable : (prefixWord ++ tailWord_6226561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226561).length < 2 ^ (prefixWord ++ tailWord_6226561).sum := by decide
  have hdescent : baseEnd_6226561 < baseStart_6226561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226588 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6226588 : Nat := 118140960795 + 6226588 * 2 ^ 59
def prefixEnd_6226588 : Nat := 4983230072969 + 3 ^ 40 * 6226588 * 2
def baseEnd_6226588 : Nat := 3197232481517589679514449

theorem tailTrace_6226588 : CollatzResearch.WordTrace tailWord_6226588 prefixEnd_6226588 3197232481517589679514449 := by
  unfold tailWord_6226588
  simp only [CollatzResearch.WordTrace]
  refine ⟨113551160783071283706296209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151401547710761711608394945 113551160783071283706296209)
  ·
    refine ⟨85163370587303462779722157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113551160783071283706296209 85163370587303462779722157)
    ·
      refine ⟨31936263970238798542395809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85163370587303462779722157 31936263970238798542395809)
      ·
        refine ⟨23952197977679098906796857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31936263970238798542395809 23952197977679098906796857)
        ·
          refine ⟨17964148483259324180097643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23952197977679098906796857 17964148483259324180097643)
          ·
            refine ⟨26946222724888986270146465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17964148483259324180097643 26946222724888986270146465)
            ·
              refine ⟨20209667043666739702609849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26946222724888986270146465 20209667043666739702609849)
              ·
                refine ⟨15157250282750054776957387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20209667043666739702609849 15157250282750054776957387)
                ·
                  refine ⟨22735875424125082165436081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15157250282750054776957387 22735875424125082165436081)
                  ·
                    refine ⟨17051906568093811624077061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22735875424125082165436081 17051906568093811624077061)
                    ·
                      refine ⟨3197232481517589679514449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17051906568093811624077061 3197232481517589679514449)
                      ·
                        rfl

theorem cell23_6226588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6226588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226588 prefixEnd_6226588 := by exact prefixLift 6226588
  have htrace : WordTrace (prefixWord ++ tailWord_6226588) baseStart_6226588 baseEnd_6226588 := by
    simpa [prefixWord, tailWord_6226588, baseEnd_6226588] using wordTrace_append hprefix tailTrace_6226588
  have hstable : (prefixWord ++ tailWord_6226588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226588).length < 2 ^ (prefixWord ++ tailWord_6226588).sum := by decide
  have hdescent : baseEnd_6226588 < baseStart_6226588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226592 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 1, 1, 4]
def baseStart_6226592 : Nat := 118140960795 + 6226592 * 2 ^ 59
def prefixEnd_6226592 : Nat := 4983230072969 + 3 ^ 40 * 6226592 * 2
def baseEnd_6226592 : Nat := 3197234535440207663864431

theorem tailTrace_6226592 : CollatzResearch.WordTrace tailWord_6226592 prefixEnd_6226592 3197234535440207663864431 := by
  unfold tailWord_6226592
  simp only [CollatzResearch.WordTrace]
  refine ⟨113551233729064038047869015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151401644972085384063825353 113551233729064038047869015)
  ·
    refine ⟨170326850593596057071803523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113551233729064038047869015 170326850593596057071803523)
    ·
      refine ⟨255490275890394085607705285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170326850593596057071803523 255490275890394085607705285)
      ·
        refine ⟨47904426729448891051444741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255490275890394085607705285 47904426729448891051444741)
        ·
          refine ⟨8982080011771667072145889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47904426729448891051444741 8982080011771667072145889)
          ·
            refine ⟨6736560008828750304109417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8982080011771667072145889 6736560008828750304109417)
            ·
              refine ⟨5052420006621562728082063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6736560008828750304109417 5052420006621562728082063)
              ·
                refine ⟨7578630009932344092123095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052420006621562728082063 7578630009932344092123095)
                ·
                  refine ⟨11367945014898516138184643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7578630009932344092123095 11367945014898516138184643)
                  ·
                    refine ⟨17051917522347774207276965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11367945014898516138184643 17051917522347774207276965)
                    ·
                      refine ⟨3197234535440207663864431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17051917522347774207276965 3197234535440207663864431)
                      ·
                        rfl

theorem cell23_6226592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_6226592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226592 prefixEnd_6226592 := by exact prefixLift 6226592
  have htrace : WordTrace (prefixWord ++ tailWord_6226592) baseStart_6226592 baseEnd_6226592 := by
    simpa [prefixWord, tailWord_6226592, baseEnd_6226592] using wordTrace_append hprefix tailTrace_6226592
  have hstable : (prefixWord ++ tailWord_6226592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226592).length < 2 ^ (prefixWord ++ tailWord_6226592).sum := by decide
  have hdescent : baseEnd_6226592 < baseStart_6226592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226602 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6226602 : Nat := 118140960795 + 6226602 * 2 ^ 59
def prefixEnd_6226602 : Nat := 4983230072969 + 3 ^ 40 * 6226602 * 2
def baseEnd_6226602 : Nat := 1065746556748917541579795

theorem tailTrace_6226602 : CollatzResearch.WordTrace tailWord_6226602 prefixEnd_6226602 1065746556748917541579795 := by
  unfold tailWord_6226602
  simp only [CollatzResearch.WordTrace]
  refine ⟨56775708047022961950900515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151401888125394565202401373 56775708047022961950900515)
  ·
    refine ⟨85163562070534442926350773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56775708047022961950900515 85163562070534442926350773)
    ·
      refine ⟨7984083944112604024345385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85163562070534442926350773 7984083944112604024345385)
      ·
        refine ⟨5988062958084453018259039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7984083944112604024345385 5988062958084453018259039)
        ·
          refine ⟨8982094437126679527388559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988062958084453018259039 8982094437126679527388559)
          ·
            refine ⟨13473141655690019291082839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982094437126679527388559 13473141655690019291082839)
            ·
              refine ⟨20209712483535028936624259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13473141655690019291082839 20209712483535028936624259)
              ·
                refine ⟨30314568725302543404936389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20209712483535028936624259 30314568725302543404936389)
                ·
                  refine ⟨5683981635994226888425573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30314568725302543404936389 5683981635994226888425573)
                  ·
                    refine ⟨1065746556748917541579795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683981635994226888425573 1065746556748917541579795)
                    ·
                      rfl

theorem cell23_6226602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6226602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226602 prefixEnd_6226602 := by exact prefixLift 6226602
  have htrace : WordTrace (prefixWord ++ tailWord_6226602) baseStart_6226602 baseEnd_6226602 := by
    simpa [prefixWord, tailWord_6226602, baseEnd_6226602] using wordTrace_append hprefix tailTrace_6226602
  have hstable : (prefixWord ++ tailWord_6226602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226602).length < 2 ^ (prefixWord ++ tailWord_6226602).sum := by decide
  have hdescent : baseEnd_6226602 < baseStart_6226602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226609 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6226609 : Nat := 118140960795 + 6226609 * 2 ^ 59
def prefixEnd_6226609 : Nat := 4983230072969 + 3 ^ 40 * 6226609 * 2
def baseEnd_6226609 : Nat := 3197243264611334097351853

theorem tailTrace_6226609 : CollatzResearch.WordTrace tailWord_6226609 prefixEnd_6226609 3197243264611334097351853 := by
  unfold tailWord_6226609
  simp only [CollatzResearch.WordTrace]
  refine ⟨227103087499066487999106881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151402058332710991999404587 227103087499066487999106881)
  ·
    refine ⟨170327315624299865999330161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227103087499066487999106881 170327315624299865999330161)
    ·
      refine ⟨127745486718224899499497621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170327315624299865999330161 127745486718224899499497621)
      ·
        refine ⟨5988069689916792164038951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127745486718224899499497621 5988069689916792164038951)
        ·
          refine ⟨8982104534875188246058427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988069689916792164038951 8982104534875188246058427)
          ·
            refine ⟨13473156802312782369087641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982104534875188246058427 13473156802312782369087641)
            ·
              refine ⟨10104867601734586776815731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13473156802312782369087641 10104867601734586776815731)
              ·
                refine ⟨15157301402601880165223597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10104867601734586776815731 15157301402601880165223597)
                ·
                  refine ⟨5683988025975705061958849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15157301402601880165223597 5683988025975705061958849)
                  ·
                    refine ⟨4262991019481778796469137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5683988025975705061958849 4262991019481778796469137)
                    ·
                      refine ⟨3197243264611334097351853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4262991019481778796469137 3197243264611334097351853)
                      ·
                        rfl

theorem cell23_6226609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6226609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226609 prefixEnd_6226609 := by exact prefixLift 6226609
  have htrace : WordTrace (prefixWord ++ tailWord_6226609) baseStart_6226609 baseEnd_6226609 := by
    simpa [prefixWord, tailWord_6226609, baseEnd_6226609] using wordTrace_append hprefix tailTrace_6226609
  have hstable : (prefixWord ++ tailWord_6226609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226609).length < 2 ^ (prefixWord ++ tailWord_6226609).sum := by decide
  have hdescent : baseEnd_6226609 < baseStart_6226609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226651 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 3]
def baseStart_6226651 : Nat := 118140960795 + 6226651 * 2 ^ 59
def prefixEnd_6226651 : Nat := 4983230072969 + 3 ^ 40 * 6226651 * 2
def baseEnd_6226651 : Nat := 3197264830798822933026659

theorem tailTrace_6226651 : CollatzResearch.WordTrace tailWord_6226651 prefixEnd_6226651 3197264830798822933026659 := by
  unfold tailWord_6226651
  simp only [CollatzResearch.WordTrace]
  refine ⟨227104619364914329172135807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151403079576609552781423871 227104619364914329172135807)
  ·
    refine ⟨340656929047371493758203711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227104619364914329172135807 340656929047371493758203711)
    ·
      refine ⟨510985393571057240637305567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340656929047371493758203711 510985393571057240637305567)
      ·
        refine ⟨766478090356585860955958351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510985393571057240637305567 766478090356585860955958351)
        ·
          refine ⟨1149717135534878791433937527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766478090356585860955958351 1149717135534878791433937527)
          ·
            refine ⟨1724575703302318187150906291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149717135534878791433937527 1724575703302318187150906291)
            ·
              refine ⟨2586863554953477280726359437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724575703302318187150906291 2586863554953477280726359437)
              ·
                refine ⟨970073833107553980272384789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586863554953477280726359437 970073833107553980272384789)
                ·
                  refine ⟨45472210926916592825268037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 970073833107553980272384789 45472210926916592825268037)
                  ·
                    refine ⟨8526039548796861154737757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45472210926916592825268037 8526039548796861154737757)
                    ·
                      refine ⟨3197264830798822933026659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8526039548796861154737757 3197264830798822933026659)
                      ·
                        rfl

theorem cell23_6226651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 3].length) (baseStart_6226651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226651 prefixEnd_6226651 := by exact prefixLift 6226651
  have htrace : WordTrace (prefixWord ++ tailWord_6226651) baseStart_6226651 baseEnd_6226651 := by
    simpa [prefixWord, tailWord_6226651, baseEnd_6226651] using wordTrace_append hprefix tailTrace_6226651
  have hstable : (prefixWord ++ tailWord_6226651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226651).length < 2 ^ (prefixWord ++ tailWord_6226651).sum := by decide
  have hdescent : baseEnd_6226651 < baseStart_6226651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226665 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 4, 2, 2]
def baseStart_6226665 : Nat := 118140960795 + 6226665 * 2 ^ 59
def prefixEnd_6226665 : Nat := 4983230072969 + 3 ^ 40 * 6226665 * 2
def baseEnd_6226665 : Nat := 3197272019527985878251595

theorem tailTrace_6226665 : CollatzResearch.WordTrace tailWord_6226665 prefixEnd_6226665 3197272019527985878251595 := by
  unfold tailWord_6226665
  simp only [CollatzResearch.WordTrace]
  refine ⟨227105129986863609563145449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151403419991242406375430299 227105129986863609563145449)
  ·
    refine ⟨170328847490147707172359087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227105129986863609563145449 170328847490147707172359087)
    ·
      refine ⟨255493271235221560758538631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170328847490147707172359087 255493271235221560758538631)
      ·
        refine ⟨383239906852832341137807947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255493271235221560758538631 383239906852832341137807947)
        ·
          refine ⟨574859860279248511706711921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383239906852832341137807947 574859860279248511706711921)
          ·
            refine ⟨431144895209436383780033941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574859860279248511706711921 431144895209436383780033941)
            ·
              refine ⟨20209916962942330489689091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 431144895209436383780033941 20209916962942330489689091)
              ·
                refine ⟨30314875444413495734533637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20209916962942330489689091 30314875444413495734533637)
                ·
                  refine ⟨5684039145827530450225057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30314875444413495734533637 5684039145827530450225057)
                  ·
                    refine ⟨4263029359370647837668793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5684039145827530450225057 4263029359370647837668793)
                    ·
                      refine ⟨3197272019527985878251595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263029359370647837668793 3197272019527985878251595)
                      ·
                        rfl

theorem cell23_6226665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 2, 2].length) (baseStart_6226665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226665 prefixEnd_6226665 := by exact prefixLift 6226665
  have htrace : WordTrace (prefixWord ++ tailWord_6226665) baseStart_6226665 baseEnd_6226665 := by
    simpa [prefixWord, tailWord_6226665, baseEnd_6226665] using wordTrace_append hprefix tailTrace_6226665
  have hstable : (prefixWord ++ tailWord_6226665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226665).length < 2 ^ (prefixWord ++ tailWord_6226665).sum := by decide
  have hdescent : baseEnd_6226665 < baseStart_6226665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226676 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6226676 : Nat := 118140960795 + 6226676 * 2 ^ 59
def prefixEnd_6226676 : Nat := 4983230072969 + 3 ^ 40 * 6226676 * 2
def baseEnd_6226676 : Nat := 3197277667815185335214045

theorem tailTrace_6226676 : CollatzResearch.WordTrace tailWord_6226676 prefixEnd_6226676 3197277667815185335214045 := by
  unfold tailWord_6226676
  simp only [CollatzResearch.WordTrace]
  refine ⟨113552765594911879220897941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151403687459882505627863921 113552765594911879220897941)
  ·
    refine ⟨5322785887261494338479591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113552765594911879220897941 5322785887261494338479591)
    ·
      refine ⟨7984178830892241507719387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5322785887261494338479591 7984178830892241507719387)
      ·
        refine ⟨11976268246338362261579081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7984178830892241507719387 11976268246338362261579081)
        ·
          refine ⟨8982201184753771696184311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11976268246338362261579081 8982201184753771696184311)
          ·
            refine ⟨13473301777130657544276467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982201184753771696184311 13473301777130657544276467)
            ·
              refine ⟨20209952665695986316414701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13473301777130657544276467 20209952665695986316414701)
              ·
                refine ⟨7578732249635994868655513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20209952665695986316414701 7578732249635994868655513)
                ·
                  refine ⟨5684049187226996151491635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578732249635994868655513 5684049187226996151491635)
                  ·
                    refine ⟨8526073780840494227237453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5684049187226996151491635 8526073780840494227237453)
                    ·
                      refine ⟨3197277667815185335214045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8526073780840494227237453 3197277667815185335214045)
                      ·
                        rfl

theorem cell23_6226676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6226676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226676 prefixEnd_6226676 := by exact prefixLift 6226676
  have htrace : WordTrace (prefixWord ++ tailWord_6226676) baseStart_6226676 baseEnd_6226676 := by
    simpa [prefixWord, tailWord_6226676, baseEnd_6226676] using wordTrace_append hprefix tailTrace_6226676
  have hstable : (prefixWord ++ tailWord_6226676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226676).length < 2 ^ (prefixWord ++ tailWord_6226676).sum := by decide
  have hdescent : baseEnd_6226676 < baseStart_6226676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226678 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6226678 : Nat := 118140960795 + 6226678 * 2 ^ 59
def prefixEnd_6226678 : Nat := 4983230072969 + 3 ^ 40 * 6226678 * 2
def baseEnd_6226678 : Nat := 3197278694776494327389035

theorem tailTrace_6226678 : CollatzResearch.WordTrace tailWord_6226678 prefixEnd_6226678 3197278694776494327389035 := by
  unfold tailWord_6226678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194100258488532048960543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151403736090544341855579125 14194100258488532048960543)
  ·
    refine ⟨21291150387732798073440815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14194100258488532048960543 21291150387732798073440815)
    ·
      refine ⟨31936725581599197110161223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21291150387732798073440815 31936725581599197110161223)
      ·
        refine ⟨47905088372398795665241835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31936725581599197110161223 47905088372398795665241835)
        ·
          refine ⟨71857632558598193497862753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47905088372398795665241835 71857632558598193497862753)
          ·
            refine ⟨53893224418948645123397065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71857632558598193497862753 53893224418948645123397065)
            ·
              refine ⟨40419918314211483842547799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53893224418948645123397065 40419918314211483842547799)
              ·
                refine ⟨60629877471317225763821699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40419918314211483842547799 60629877471317225763821699)
                ·
                  refine ⟨90944816206975838645732549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60629877471317225763821699 90944816206975838645732549)
                  ·
                    refine ⟨17052153038807969746074853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90944816206975838645732549 17052153038807969746074853)
                    ·
                      refine ⟨3197278694776494327389035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17052153038807969746074853 3197278694776494327389035)
                      ·
                        rfl

theorem cell23_6226678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6226678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226678 prefixEnd_6226678 := by exact prefixLift 6226678
  have htrace : WordTrace (prefixWord ++ tailWord_6226678) baseStart_6226678 baseEnd_6226678 := by
    simpa [prefixWord, tailWord_6226678, baseEnd_6226678] using wordTrace_append hprefix tailTrace_6226678
  have hstable : (prefixWord ++ tailWord_6226678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226678).length < 2 ^ (prefixWord ++ tailWord_6226678).sum := by decide
  have hdescent : baseEnd_6226678 < baseStart_6226678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226722 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_6226722 : Nat := 118140960795 + 6226722 * 2 ^ 59
def prefixEnd_6226722 : Nat := 4983230072969 + 3 ^ 40 * 6226722 * 2
def baseEnd_6226722 : Nat := 355255698658365795026537

theorem tailTrace_6226722 : CollatzResearch.WordTrace tailWord_6226722 prefixEnd_6226722 355255698658365795026537 := by
  unfold tailWord_6226722
  simp only [CollatzResearch.WordTrace]
  refine ⟨56776802236914277074492605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151404805965104738865313613 56776802236914277074492605)
  ·
    refine ⟨21291300838842853902934727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56776802236914277074492605 21291300838842853902934727)
    ·
      refine ⟨31936951258264280854402091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21291300838842853902934727 31936951258264280854402091)
      ·
        refine ⟨47905426887396421281603137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31936951258264280854402091 47905426887396421281603137)
        ·
          refine ⟨35929070165547315961202353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47905426887396421281603137 35929070165547315961202353)
          ·
            refine ⟨26946802624160486970901765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35929070165547315961202353 26946802624160486970901765)
            ·
              refine ⟨5052525492030091307044081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26946802624160486970901765 5052525492030091307044081)
              ·
                refine ⟨3789394119022568480283061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052525492030091307044081 3789394119022568480283061)
                ·
                  refine ⟨355255698658365795026537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789394119022568480283061 355255698658365795026537)
                  ·
                    rfl

theorem cell23_6226722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_6226722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226722 prefixEnd_6226722 := by exact prefixLift 6226722
  have htrace : WordTrace (prefixWord ++ tailWord_6226722) baseStart_6226722 baseEnd_6226722 := by
    simpa [prefixWord, tailWord_6226722, baseEnd_6226722] using wordTrace_append hprefix tailTrace_6226722
  have hstable : (prefixWord ++ tailWord_6226722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226722).length < 2 ^ (prefixWord ++ tailWord_6226722).sum := by decide
  have hdescent : baseEnd_6226722 < baseStart_6226722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226728 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6226728 : Nat := 118140960795 + 6226728 * 2 ^ 59
def prefixEnd_6226728 : Nat := 4983230072969 + 3 ^ 40 * 6226728 * 2
def baseEnd_6226728 : Nat := 3197304368809219131763805

theorem tailTrace_6226728 : CollatzResearch.WordTrace tailWord_6226728 prefixEnd_6226728 3197304368809219131763805 := by
  unfold tailWord_6226728
  simp only [CollatzResearch.WordTrace]
  refine ⟨113553713892817685661344419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151404951857090247548459225 113553713892817685661344419)
  ·
    refine ⟨170330570839226528492016629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113553713892817685661344419 170330570839226528492016629)
    ·
      refine ⟨15968491016177487046126559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170330570839226528492016629 15968491016177487046126559)
      ·
        refine ⟨23952736524266230569189839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15968491016177487046126559 23952736524266230569189839)
        ·
          refine ⟨35929104786399345853784759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23952736524266230569189839 35929104786399345853784759)
          ·
            refine ⟨53893657179599018780677139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35929104786399345853784759 53893657179599018780677139)
            ·
              refine ⟨80840485769398528171015709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53893657179599018780677139 80840485769398528171015709)
              ·
                refine ⟨30315182163524448064130891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80840485769398528171015709 30315182163524448064130891)
                ·
                  refine ⟨45472773245286672096196337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30315182163524448064130891 45472773245286672096196337)
                  ·
                    refine ⟨34104579933965004072147253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45472773245286672096196337 34104579933965004072147253)
                    ·
                      refine ⟨3197304368809219131763805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34104579933965004072147253 3197304368809219131763805)
                      ·
                        rfl

theorem cell23_6226728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6226728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226728 prefixEnd_6226728 := by exact prefixLift 6226728
  have htrace : WordTrace (prefixWord ++ tailWord_6226728) baseStart_6226728 baseEnd_6226728 := by
    simpa [prefixWord, tailWord_6226728, baseEnd_6226728] using wordTrace_append hprefix tailTrace_6226728
  have hstable : (prefixWord ++ tailWord_6226728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226728).length < 2 ^ (prefixWord ++ tailWord_6226728).sum := by decide
  have hdescent : baseEnd_6226728 < baseStart_6226728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226738 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_6226738 : Nat := 118140960795 + 6226738 * 2 ^ 59
def prefixEnd_6226738 : Nat := 4983230072969 + 3 ^ 40 * 6226738 * 2
def baseEnd_6226738 : Nat := 3197309503615764092638759

theorem tailTrace_6226738 : CollatzResearch.WordTrace tailWord_6226738 prefixEnd_6226738 3197309503615764092638759 := by
  unfold tailWord_6226738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56776948128899785757638217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151405195010399428687035245 56776948128899785757638217)
  ·
    refine ⟨42582711096674839318228663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56776948128899785757638217 42582711096674839318228663)
    ·
      refine ⟨63874066645012258977342995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42582711096674839318228663 63874066645012258977342995)
      ·
        refine ⟨95811099967518388466014493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63874066645012258977342995 95811099967518388466014493)
        ·
          refine ⟨35929162487819395674755435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95811099967518388466014493 35929162487819395674755435)
          ·
            refine ⟨53893743731729093512133153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35929162487819395674755435 53893743731729093512133153)
            ·
              refine ⟨40420307798796820134099865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53893743731729093512133153 40420307798796820134099865)
              ·
                refine ⟨30315230849097615100574899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40420307798796820134099865 30315230849097615100574899)
                ·
                  refine ⟨45472846273646422650862349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30315230849097615100574899 45472846273646422650862349)
                  ·
                    refine ⟨17052317352617408494073381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45472846273646422650862349 17052317352617408494073381)
                    ·
                      refine ⟨3197309503615764092638759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17052317352617408494073381 3197309503615764092638759)
                      ·
                        rfl

theorem cell23_6226738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_6226738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226738 prefixEnd_6226738 := by exact prefixLift 6226738
  have htrace : WordTrace (prefixWord ++ tailWord_6226738) baseStart_6226738 baseEnd_6226738 := by
    simpa [prefixWord, tailWord_6226738, baseEnd_6226738] using wordTrace_append hprefix tailTrace_6226738
  have hstable : (prefixWord ++ tailWord_6226738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226738).length < 2 ^ (prefixWord ++ tailWord_6226738).sum := by decide
  have hdescent : baseEnd_6226738 < baseStart_6226738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226778 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_6226778 : Nat := 118140960795 + 6226778 * 2 ^ 59
def prefixEnd_6226778 : Nat := 4983230072969 + 3 ^ 40 * 6226778 * 2
def baseEnd_6226778 : Nat := 355258893649104881793175

theorem tailTrace_6226778 : CollatzResearch.WordTrace tailWord_6226778 prefixEnd_6226778 355258893649104881793175 := by
  unfold tailWord_6226778
  simp only [CollatzResearch.WordTrace]
  refine ⟨56777312858863557465502247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151406167623636153241339325 56777312858863557465502247)
  ·
    refine ⟨85165969288295336198253371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56777312858863557465502247 85165969288295336198253371)
    ·
      refine ⟨127748953932443004297380057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85165969288295336198253371 127748953932443004297380057)
      ·
        refine ⟨95811715449332253223035043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127748953932443004297380057 95811715449332253223035043)
        ·
          refine ⟨143717573173998379834552565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95811715449332253223035043 143717573173998379834552565)
          ·
            refine ⟨13473522485062348109489303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143717573173998379834552565 13473522485062348109489303)
            ·
              refine ⟨20210283727593522164233955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13473522485062348109489303 20210283727593522164233955)
              ·
                refine ⟨30315425591390283246350933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20210283727593522164233955 30315425591390283246350933)
                ·
                  refine ⟨355258893649104881793175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30315425591390283246350933 355258893649104881793175)
                  ·
                    rfl

theorem cell23_6226778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_6226778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226778 prefixEnd_6226778 := by exact prefixLift 6226778
  have htrace : WordTrace (prefixWord ++ tailWord_6226778) baseStart_6226778 baseEnd_6226778 := by
    simpa [prefixWord, tailWord_6226778, baseEnd_6226778] using wordTrace_append hprefix tailTrace_6226778
  have hstable : (prefixWord ++ tailWord_6226778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226778).length < 2 ^ (prefixWord ++ tailWord_6226778).sum := by decide
  have hdescent : baseEnd_6226778 < baseStart_6226778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226815 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 1, 5, 2]
def baseStart_6226815 : Nat := 118140960795 + 6226815 * 2 ^ 59
def prefixEnd_6226815 : Nat := 4983230072969 + 3 ^ 40 * 6226815 * 2
def baseEnd_6226815 : Nat := 3197349041626160291375905

theorem tailTrace_6226815 : CollatzResearch.WordTrace tailWord_6226815 prefixEnd_6226815 3197349041626160291375905 := by
  unfold tailWord_6226815
  simp only [CollatzResearch.WordTrace]
  refine ⟨227110600936320185181105899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151407067290880123454070599 227110600936320185181105899)
  ·
    refine ⟨340665901404480277771658849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227110600936320185181105899 340665901404480277771658849)
    ·
      refine ⟨255499426053360208328744137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340665901404480277771658849 255499426053360208328744137)
      ·
        refine ⟨191624569540020156246558103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255499426053360208328744137 191624569540020156246558103)
        ·
          refine ⟨287436854310030234369837155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191624569540020156246558103 287436854310030234369837155)
          ·
            refine ⟨431155281465045351554755733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287436854310030234369837155 431155281465045351554755733)
            ·
              refine ⟨20210403818674000854129175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 431155281465045351554755733 20210403818674000854129175)
              ·
                refine ⟨30315605728011001281193763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20210403818674000854129175 30315605728011001281193763)
                ·
                  refine ⟨45473408592016501921790645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30315605728011001281193763 45473408592016501921790645)
                  ·
                    refine ⟨4263132055501547055167873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45473408592016501921790645 4263132055501547055167873)
                    ·
                      refine ⟨3197349041626160291375905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263132055501547055167873 3197349041626160291375905)
                      ·
                        rfl

theorem cell23_6226815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_6226815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226815 prefixEnd_6226815 := by exact prefixLift 6226815
  have htrace : WordTrace (prefixWord ++ tailWord_6226815) baseStart_6226815 baseEnd_6226815 := by
    simpa [prefixWord, tailWord_6226815, baseEnd_6226815] using wordTrace_append hprefix tailTrace_6226815
  have hstable : (prefixWord ++ tailWord_6226815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226815).length < 2 ^ (prefixWord ++ tailWord_6226815).sum := by decide
  have hdescent : baseEnd_6226815 < baseStart_6226815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226825 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 1, 5]
def baseStart_6226825 : Nat := 118140960795 + 6226825 * 2 ^ 59
def prefixEnd_6226825 : Nat := 4983230072969 + 3 ^ 40 * 6226825 * 2
def baseEnd_6226825 : Nat := 1065784725477568417416953

theorem tailTrace_6226825 : CollatzResearch.WordTrace tailWord_6226825 prefixEnd_6226825 1065784725477568417416953 := by
  unfold tailWord_6226825
  simp only [CollatzResearch.WordTrace]
  refine ⟨227110965666283956888969929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151407310444189304592646619 227110965666283956888969929)
  ·
    refine ⟨170333224249712967666727447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227110965666283956888969929 170333224249712967666727447)
    ·
      refine ⟨255499836374569451500091171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170333224249712967666727447 255499836374569451500091171)
      ·
        refine ⟨383249754561854177250136757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255499836374569451500091171 383249754561854177250136757)
        ·
          refine ⟨35929664490173829117200321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 383249754561854177250136757 35929664490173829117200321)
          ·
            refine ⟨26947248367630371837900241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35929664490173829117200321 26947248367630371837900241)
            ·
              refine ⟨20210436275722778878425181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26947248367630371837900241 20210436275722778878425181)
              ·
                refine ⟨7578913603396042079409443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20210436275722778878425181 7578913603396042079409443)
                ·
                  refine ⟨11368370405094063119114165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7578913603396042079409443 11368370405094063119114165)
                  ·
                    refine ⟨1065784725477568417416953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11368370405094063119114165 1065784725477568417416953)
                    ·
                      rfl

theorem cell23_6226825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_6226825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226825 prefixEnd_6226825 := by exact prefixLift 6226825
  have htrace : WordTrace (prefixWord ++ tailWord_6226825) baseStart_6226825 baseEnd_6226825 := by
    simpa [prefixWord, tailWord_6226825, baseEnd_6226825] using wordTrace_append hprefix tailTrace_6226825
  have hstable : (prefixWord ++ tailWord_6226825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226825).length < 2 ^ (prefixWord ++ tailWord_6226825).sum := by decide
  have hdescent : baseEnd_6226825 < baseStart_6226825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226845 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_6226845 : Nat := 118140960795 + 6226845 * 2 ^ 59
def prefixEnd_6226845 : Nat := 4983230072969 + 3 ^ 40 * 6226845 * 2
def baseEnd_6226845 : Nat := 3197364446045795174000767

theorem tailTrace_6226845 : CollatzResearch.WordTrace tailWord_6226845 prefixEnd_6226845 3197364446045795174000767 := by
  unfold tailWord_6226845
  simp only [CollatzResearch.WordTrace]
  refine ⟨227111695126211500304697989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151407796750807666869798659 227111695126211500304697989)
  ·
    refine ⟨42583442836164656307130873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227111695126211500304697989 42583442836164656307130873)
    ·
      refine ⟨31937582127123492230348155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42583442836164656307130873 31937582127123492230348155)
      ·
        refine ⟨47906373190685238345522233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31937582127123492230348155 47906373190685238345522233)
        ·
          refine ⟨35929779893013928759141675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47906373190685238345522233 35929779893013928759141675)
          ·
            refine ⟨53894669839520893138712513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35929779893013928759141675 53894669839520893138712513)
            ·
              refine ⟨40421002379640669854034385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53894669839520893138712513 40421002379640669854034385)
              ·
                refine ⟨30315751784730502390525789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40421002379640669854034385 30315751784730502390525789)
                ·
                  refine ⟨11368406919273938396447171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30315751784730502390525789 11368406919273938396447171)
                  ·
                    refine ⟨17052610378910907594670757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11368406919273938396447171 17052610378910907594670757)
                    ·
                      refine ⟨3197364446045795174000767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17052610378910907594670757 3197364446045795174000767)
                      ·
                        rfl

theorem cell23_6226845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_6226845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226845 prefixEnd_6226845 := by exact prefixLift 6226845
  have htrace : WordTrace (prefixWord ++ tailWord_6226845) baseStart_6226845 baseEnd_6226845 := by
    simpa [prefixWord, tailWord_6226845, baseEnd_6226845] using wordTrace_append hprefix tailTrace_6226845
  have hstable : (prefixWord ++ tailWord_6226845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226845).length < 2 ^ (prefixWord ++ tailWord_6226845).sum := by decide
  have hdescent : baseEnd_6226845 < baseStart_6226845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226902 : List Nat := [5, 2, 1, 1, 2, 1, 3, 8]
def baseStart_6226902 : Nat := 118140960795 + 6226902 * 2 ^ 59
def prefixEnd_6226902 : Nat := 4983230072969 + 3 ^ 40 * 6226902 * 2
def baseEnd_6226902 : Nat := 118421989423818572258815

theorem tailTrace_6226902 : CollatzResearch.WordTrace tailWord_6226902 prefixEnd_6226902 118421989423818572258815 := by
  unfold tailWord_6226902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194610880437812439970185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151409182724669999359681973 14194610880437812439970185)
  ·
    refine ⟨10645958160328359329977639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14194610880437812439970185 10645958160328359329977639)
    ·
      refine ⟨15968937240492538994966459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10645958160328359329977639 15968937240492538994966459)
      ·
        refine ⟨23953405860738808492449689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15968937240492538994966459 23953405860738808492449689)
        ·
          refine ⟨17965054395554106369337267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23953405860738808492449689 17965054395554106369337267)
          ·
            refine ⟨26947581593331159554005901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17965054395554106369337267 26947581593331159554005901)
            ·
              refine ⟨10105343097499184832752213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26947581593331159554005901 10105343097499184832752213)
              ·
                refine ⟨118421989423818572258815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10105343097499184832752213 118421989423818572258815)
                ·
                  rfl

theorem cell23_6226902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_6226902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226902 prefixEnd_6226902 := by exact prefixLift 6226902
  have htrace : WordTrace (prefixWord ++ tailWord_6226902) baseStart_6226902 baseEnd_6226902 := by
    simpa [prefixWord, tailWord_6226902, baseEnd_6226902] using wordTrace_append hprefix tailTrace_6226902
  have hstable : (prefixWord ++ tailWord_6226902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226902).length < 2 ^ (prefixWord ++ tailWord_6226902).sum := by decide
  have hdescent : baseEnd_6226902 < baseStart_6226902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226928 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_6226928 : Nat := 118140960795 + 6226928 * 2 ^ 59
def prefixEnd_6226928 : Nat := 4983230072969 + 3 ^ 40 * 6226928 * 2
def baseEnd_6226928 : Nat := 1065802354980039449754295

theorem tailTrace_6226928 : CollatzResearch.WordTrace tailWord_6226928 prefixEnd_6226928 1065802354980039449754295 := by
  unfold tailWord_6226928
  simp only [CollatzResearch.WordTrace]
  refine ⟨113557361192455402739984719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151409814923273870319979625 113557361192455402739984719)
  ·
    refine ⟨170336041788683104109977079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113557361192455402739984719 170336041788683104109977079)
    ·
      refine ⟨255504062683024656164965619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170336041788683104109977079 255504062683024656164965619)
      ·
        refine ⟨383256094024536984247448429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255504062683024656164965619 383256094024536984247448429)
        ·
          refine ⟨143721035259201369092793161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383256094024536984247448429 143721035259201369092793161)
          ·
            refine ⟨107790776444401026819594871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143721035259201369092793161 107790776444401026819594871)
            ·
              refine ⟨161686164666601540229392307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107790776444401026819594871 161686164666601540229392307)
              ·
                refine ⟨242529246999902310344088461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161686164666601540229392307 242529246999902310344088461)
                ·
                  refine ⟨90948467624963366379033173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242529246999902310344088461 90948467624963366379033173)
                  ·
                    refine ⟨1065802354980039449754295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90948467624963366379033173 1065802354980039449754295)
                    ·
                      rfl

theorem cell23_6226928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_6226928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226928 prefixEnd_6226928 := by exact prefixLift 6226928
  have htrace : WordTrace (prefixWord ++ tailWord_6226928) baseStart_6226928 baseEnd_6226928 := by
    simpa [prefixWord, tailWord_6226928, baseEnd_6226928] using wordTrace_append hprefix tailTrace_6226928
  have hstable : (prefixWord ++ tailWord_6226928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226928).length < 2 ^ (prefixWord ++ tailWord_6226928).sum := by decide
  have hdescent : baseEnd_6226928 < baseStart_6226928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226930 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6226930 : Nat := 118140960795 + 6226930 * 2 ^ 59
def prefixEnd_6226930 : Nat := 4983230072969 + 3 ^ 40 * 6226930 * 2
def baseEnd_6226930 : Nat := 3197408091901427341437877

theorem tailTrace_6226930 : CollatzResearch.WordTrace tailWord_6226930 prefixEnd_6226930 3197408091901427341437877 := by
  unfold tailWord_6226930
  simp only [CollatzResearch.WordTrace]
  refine ⟨56778698832725889955385561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151409863553935706547694829 56778698832725889955385561)
  ·
    refine ⟨42584024124544417466539171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56778698832725889955385561 42584024124544417466539171)
    ·
      refine ⟨63876036186816626199808757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42584024124544417466539171 63876036186816626199808757)
      ·
        refine ⟨5988378392514058706232071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63876036186816626199808757 5988378392514058706232071)
        ·
          refine ⟨8982567588771088059348107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988378392514058706232071 8982567588771088059348107)
          ·
            refine ⟨13473851383156632089022161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982567588771088059348107 13473851383156632089022161)
            ·
              refine ⟨10105388537367474066766621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13473851383156632089022161 10105388537367474066766621)
              ·
                refine ⟨3789520701512802775037483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10105388537367474066766621 3789520701512802775037483)
                ·
                  refine ⟨5684281052269204162556225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789520701512802775037483 5684281052269204162556225)
                  ·
                    refine ⟨4263210789201903121917169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5684281052269204162556225 4263210789201903121917169)
                    ·
                      refine ⟨3197408091901427341437877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263210789201903121917169 3197408091901427341437877)
                      ·
                        rfl

theorem cell23_6226930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6226930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226930 prefixEnd_6226930 := by exact prefixLift 6226930
  have htrace : WordTrace (prefixWord ++ tailWord_6226930) baseStart_6226930 baseEnd_6226930 := by
    simpa [prefixWord, tailWord_6226930, baseEnd_6226930] using wordTrace_append hprefix tailTrace_6226930
  have hstable : (prefixWord ++ tailWord_6226930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226930).length < 2 ^ (prefixWord ++ tailWord_6226930).sum := by decide
  have hdescent : baseEnd_6226930 < baseStart_6226930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226945 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_6226945 : Nat := 118140960795 + 6226945 * 2 ^ 59
def prefixEnd_6226945 : Nat := 4983230072969 + 3 ^ 40 * 6226945 * 2
def baseEnd_6226945 : Nat := 1065805264703748260916769

theorem tailTrace_6226945 : CollatzResearch.WordTrace tailWord_6226945 prefixEnd_6226945 1065805264703748260916769 := by
  unfold tailWord_6226945
  simp only [CollatzResearch.WordTrace]
  refine ⟨227115342425849217383338289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151410228283899478255558859 227115342425849217383338289)
  ·
    refine ⟨170336506819386913037503717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227115342425849217383338289 170336506819386913037503717)
    ·
      refine ⟨31938095028635046194531947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170336506819386913037503717 31938095028635046194531947)
      ·
        refine ⟨47907142542952569291797921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31938095028635046194531947 47907142542952569291797921)
        ·
          refine ⟨35930356907214426968848441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47907142542952569291797921 35930356907214426968848441)
          ·
            refine ⟨26947767680410820226636331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35930356907214426968848441 26947767680410820226636331)
            ·
              refine ⟨40421651520616230339954497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26947767680410820226636331 40421651520616230339954497)
              ·
                refine ⟨30316238640462172754965873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40421651520616230339954497 30316238640462172754965873)
                ·
                  refine ⟨22737178980346629566224405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30316238640462172754965873 22737178980346629566224405)
                  ·
                    refine ⟨1065805264703748260916769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22737178980346629566224405 1065805264703748260916769)
                    ·
                      rfl

theorem cell23_6226945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_6226945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226945 prefixEnd_6226945 := by exact prefixLift 6226945
  have htrace : WordTrace (prefixWord ++ tailWord_6226945) baseStart_6226945 baseEnd_6226945 := by
    simpa [prefixWord, tailWord_6226945, baseEnd_6226945] using wordTrace_append hprefix tailTrace_6226945
  have hstable : (prefixWord ++ tailWord_6226945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226945).length < 2 ^ (prefixWord ++ tailWord_6226945).sum := by decide
  have hdescent : baseEnd_6226945 < baseStart_6226945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226969 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 2, 2, 2]
def baseStart_6226969 : Nat := 118140960795 + 6226969 * 2 ^ 59
def prefixEnd_6226969 : Nat := 4983230072969 + 3 ^ 40 * 6226969 * 2
def baseEnd_6226969 : Nat := 3197428117646952688850197

theorem tailTrace_6226969 : CollatzResearch.WordTrace tailWord_6226969 prefixEnd_6226969 3197428117646952688850197 := by
  unfold tailWord_6226969
  simp only [CollatzResearch.WordTrace]
  refine ⟨227116217777762269482211961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151410811851841512988141307 227116217777762269482211961)
  ·
    refine ⟨170337163333321702111658971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227116217777762269482211961 170337163333321702111658971)
    ·
      refine ⟨255505744999982553167488457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170337163333321702111658971 255505744999982553167488457)
      ·
        refine ⟨191629308749986914875616343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255505744999982553167488457 191629308749986914875616343)
        ·
          refine ⟨287443963124980372313424515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191629308749986914875616343 287443963124980372313424515)
          ·
            refine ⟨431165944687470558470136773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287443963124980372313424515 431165944687470558470136773)
            ·
              refine ⟨80843614628900729713150645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431165944687470558470136773 80843614628900729713150645)
              ·
                refine ⟨7579088871459443410607873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80843614628900729713150645 7579088871459443410607873)
                ·
                  refine ⟨5684316653594582557955905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7579088871459443410607873 5684316653594582557955905)
                  ·
                    refine ⟨4263237490195936918466929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5684316653594582557955905 4263237490195936918466929)
                    ·
                      refine ⟨3197428117646952688850197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263237490195936918466929 3197428117646952688850197)
                      ·
                        rfl

theorem cell23_6226969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_6226969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226969 prefixEnd_6226969 := by exact prefixLift 6226969
  have htrace : WordTrace (prefixWord ++ tailWord_6226969) baseStart_6226969 baseEnd_6226969 := by
    simpa [prefixWord, tailWord_6226969, baseEnd_6226969] using wordTrace_append hprefix tailTrace_6226969
  have hstable : (prefixWord ++ tailWord_6226969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226969).length < 2 ^ (prefixWord ++ tailWord_6226969).sum := by decide
  have hdescent : baseEnd_6226969 < baseStart_6226969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6226975 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 7]
def baseStart_6226975 : Nat := 118140960795 + 6226975 * 2 ^ 59
def prefixEnd_6226975 : Nat := 4983230072969 + 3 ^ 40 * 6226975 * 2
def baseEnd_6226975 : Nat := 355270133170097740597241

theorem tailTrace_6226975 : CollatzResearch.WordTrace tailWord_6226975 prefixEnd_6226975 355270133170097740597241 := by
  unfold tailWord_6226975
  simp only [CollatzResearch.WordTrace]
  refine ⟨227116436615740532506930379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151410957743827021671286919 227116436615740532506930379)
  ·
    refine ⟨340674654923610798760395569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227116436615740532506930379 340674654923610798760395569)
    ·
      refine ⟨255505991192708099070296677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340674654923610798760395569 255505991192708099070296677)
      ·
        refine ⟨47907373348632768575680627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255505991192708099070296677 47907373348632768575680627)
        ·
          refine ⟨71861060022949152863520941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47907373348632768575680627 71861060022949152863520941)
          ·
            refine ⟨26947897508605932323820353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71861060022949152863520941 26947897508605932323820353)
            ·
              refine ⟨20210923131454449242865265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26947897508605932323820353 20210923131454449242865265)
              ·
                refine ⟨15158192348590836932148949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20210923131454449242865265 15158192348590836932148949)
                ·
                  refine ⟨355270133170097740597241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15158192348590836932148949 355270133170097740597241)
                  ·
                    rfl

theorem cell23_6226975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 7].length) (baseStart_6226975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6226975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6226975 prefixEnd_6226975 := by exact prefixLift 6226975
  have htrace : WordTrace (prefixWord ++ tailWord_6226975) baseStart_6226975 baseEnd_6226975 := by
    simpa [prefixWord, tailWord_6226975, baseEnd_6226975] using wordTrace_append hprefix tailTrace_6226975
  have hstable : (prefixWord ++ tailWord_6226975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6226975).length < 2 ^ (prefixWord ++ tailWord_6226975).sum := by decide
  have hdescent : baseEnd_6226975 < baseStart_6226975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6226975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227009 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 7]
def baseStart_6227009 : Nat := 118140960795 + 6227009 * 2 ^ 59
def prefixEnd_6227009 : Nat := 4983230072969 + 3 ^ 40 * 6227009 * 2
def baseEnd_6227009 : Nat := 355272072985903614705557

theorem tailTrace_6227009 : CollatzResearch.WordTrace tailWord_6227009 prefixEnd_6227009 355272072985903614705557 := by
  unfold tailWord_6227009
  simp only [CollatzResearch.WordTrace]
  refine ⟨227117676697617356313668081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151411784465078237542445387 227117676697617356313668081)
  ·
    refine ⟨170338257523213017235251061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227117676697617356313668081 170338257523213017235251061)
    ·
      refine ⟨15969211642801220365804787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170338257523213017235251061 15969211642801220365804787)
      ·
        refine ⟨23953817464201830548707181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15969211642801220365804787 23953817464201830548707181)
        ·
          refine ⟨8982681549075686455765193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23953817464201830548707181 8982681549075686455765193)
          ·
            refine ⟨6737011161806764841823895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8982681549075686455765193 6737011161806764841823895)
            ·
              refine ⟨10105516742710147262735843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737011161806764841823895 10105516742710147262735843)
              ·
                refine ⟨15158275114065220894103765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10105516742710147262735843 15158275114065220894103765)
                ·
                  refine ⟨355272072985903614705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15158275114065220894103765 355272072985903614705557)
                  ·
                    rfl

theorem cell23_6227009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 7].length) (baseStart_6227009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227009 prefixEnd_6227009 := by exact prefixLift 6227009
  have htrace : WordTrace (prefixWord ++ tailWord_6227009) baseStart_6227009 baseEnd_6227009 := by
    simpa [prefixWord, tailWord_6227009, baseEnd_6227009] using wordTrace_append hprefix tailTrace_6227009
  have hstable : (prefixWord ++ tailWord_6227009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227009).length < 2 ^ (prefixWord ++ tailWord_6227009).sum := by decide
  have hdescent : baseEnd_6227009 < baseStart_6227009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227015 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_6227015 : Nat := 118140960795 + 6227015 * 2 ^ 59
def prefixEnd_6227015 : Nat := 4983230072969 + 3 ^ 40 * 6227015 * 2
def baseEnd_6227015 : Nat := 3197451737757059508874985

theorem tailTrace_6227015 : CollatzResearch.WordTrace tailWord_6227015 prefixEnd_6227015 3197451737757059508874985 := by
  unfold tailWord_6227015
  simp only [CollatzResearch.WordTrace]
  refine ⟨227117895535595619338386499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151411930357063746225590999 227117895535595619338386499)
  ·
    refine ⟨340676843303393429007579749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227117895535595619338386499 340676843303393429007579749)
    ·
      refine ⟨63876908119386267938921203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340676843303393429007579749 63876908119386267938921203)
      ·
        refine ⟨95815362179079401908381805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63876908119386267938921203 95815362179079401908381805)
        ·
          refine ⟨35930760817154775715643177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95815362179079401908381805 35930760817154775715643177)
          ·
            refine ⟨26948070612866081786732383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35930760817154775715643177 26948070612866081786732383)
            ·
              refine ⟨40422105919299122680098575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26948070612866081786732383 40422105919299122680098575)
              ·
                refine ⟨60633158878948684020147863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40422105919299122680098575 60633158878948684020147863)
                ·
                  refine ⟨90949738318423026030221795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60633158878948684020147863 90949738318423026030221795)
                  ·
                    refine ⟨136424607477634539045332693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90949738318423026030221795 136424607477634539045332693)
                    ·
                      refine ⟨3197451737757059508874985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136424607477634539045332693 3197451737757059508874985)
                      ·
                        rfl

theorem cell23_6227015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_6227015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227015 prefixEnd_6227015 := by exact prefixLift 6227015
  have htrace : WordTrace (prefixWord ++ tailWord_6227015) baseStart_6227015 baseEnd_6227015 := by
    simpa [prefixWord, tailWord_6227015, baseEnd_6227015] using wordTrace_append hprefix tailTrace_6227015
  have hstable : (prefixWord ++ tailWord_6227015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227015).length < 2 ^ (prefixWord ++ tailWord_6227015).sum := by decide
  have hdescent : baseEnd_6227015 < baseStart_6227015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227025 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_6227025 : Nat := 118140960795 + 6227025 * 2 ^ 59
def prefixEnd_6227025 : Nat := 4983230072969 + 3 ^ 40 * 6227025 * 2
def baseEnd_6227025 : Nat := 3197456872563604469749939

theorem tailTrace_6227025 : CollatzResearch.WordTrace tailWord_6227025 prefixEnd_6227025 3197456872563604469749939 := by
  unfold tailWord_6227025
  simp only [CollatzResearch.WordTrace]
  refine ⟨227118260265559391046250529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151412173510372927364167019 227118260265559391046250529)
  ·
    refine ⟨170338695199169543284687897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227118260265559391046250529 170338695199169543284687897)
    ·
      refine ⟨127754021399377157463515923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170338695199169543284687897 127754021399377157463515923)
      ·
        refine ⟨191631032099065736195273885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127754021399377157463515923 191631032099065736195273885)
        ·
          refine ⟨71861637037149651073227707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191631032099065736195273885 71861637037149651073227707)
          ·
            refine ⟨107792455555724476609841561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71861637037149651073227707 107792455555724476609841561)
            ·
              refine ⟨80844341666793357457381171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107792455555724476609841561 80844341666793357457381171)
              ·
                refine ⟨121266512500190036186071757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80844341666793357457381171 121266512500190036186071757)
                ·
                  refine ⟨45474942187571263569776909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121266512500190036186071757 45474942187571263569776909)
                  ·
                    refine ⟨17053103320339223838666341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45474942187571263569776909 17053103320339223838666341)
                    ·
                      refine ⟨3197456872563604469749939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17053103320339223838666341 3197456872563604469749939)
                      ·
                        rfl

theorem cell23_6227025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_6227025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227025 prefixEnd_6227025 := by exact prefixLift 6227025
  have htrace : WordTrace (prefixWord ++ tailWord_6227025) baseStart_6227025 baseEnd_6227025 := by
    simpa [prefixWord, tailWord_6227025, baseEnd_6227025] using wordTrace_append hprefix tailTrace_6227025
  have hstable : (prefixWord ++ tailWord_6227025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227025).length < 2 ^ (prefixWord ++ tailWord_6227025).sum := by decide
  have hdescent : baseEnd_6227025 < baseStart_6227025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227055 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_6227055 : Nat := 118140960795 + 6227055 * 2 ^ 59
def prefixEnd_6227055 : Nat := 4983230072969 + 3 ^ 40 * 6227055 * 2
def baseEnd_6227055 : Nat := 3197472276983239352374801

theorem tailTrace_6227055 : CollatzResearch.WordTrace tailWord_6227055 prefixEnd_6227055 3197472276983239352374801 := by
  unfold tailWord_6227055
  simp only [CollatzResearch.WordTrace]
  refine ⟨227119354455450706169842619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151412902970300470779895079 227119354455450706169842619)
  ·
    refine ⟨340679031683176059254763929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227119354455450706169842619 340679031683176059254763929)
    ·
      refine ⟨255509273762382044441072947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340679031683176059254763929 255509273762382044441072947)
      ·
        refine ⟨383263910643573066661609421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255509273762382044441072947 383263910643573066661609421)
        ·
          refine ⟨143723966491339899998103533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383263910643573066661609421 143723966491339899998103533)
          ·
            refine ⟨53896487434252462499288825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143723966491339899998103533 53896487434252462499288825)
            ·
              refine ⟨40422365575689346874466619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53896487434252462499288825 40422365575689346874466619)
              ·
                refine ⟨60633548363534020311699929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40422365575689346874466619 60633548363534020311699929)
                ·
                  refine ⟨45475161272650515233774947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60633548363534020311699929 45475161272650515233774947)
                  ·
                    refine ⟨68212741908975772850662421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45475161272650515233774947 68212741908975772850662421)
                    ·
                      refine ⟨3197472276983239352374801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68212741908975772850662421 3197472276983239352374801)
                      ·
                        rfl

theorem cell23_6227055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_6227055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227055 prefixEnd_6227055 := by exact prefixLift 6227055
  have htrace : WordTrace (prefixWord ++ tailWord_6227055) baseStart_6227055 baseEnd_6227055 := by
    simpa [prefixWord, tailWord_6227055, baseEnd_6227055] using wordTrace_append hprefix tailTrace_6227055
  have hstable : (prefixWord ++ tailWord_6227055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227055).length < 2 ^ (prefixWord ++ tailWord_6227055).sum := by decide
  have hdescent : baseEnd_6227055 < baseStart_6227055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227062 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6227062 : Nat := 118140960795 + 6227062 * 2 ^ 59
def prefixEnd_6227062 : Nat := 4983230072969 + 3 ^ 40 * 6227062 * 2
def baseEnd_6227062 : Nat := 3197475871347820824987269

theorem tailTrace_6227062 : CollatzResearch.WordTrace tailWord_6227062 prefixEnd_6227062 3197475871347820824987269 := by
  unfold tailWord_6227062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194975610401584147834215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151413073177616897576898293 14194975610401584147834215)
  ·
    refine ⟨21292463415602376221751323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14194975610401584147834215 21292463415602376221751323)
    ·
      refine ⟨31938695123403564332626985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21292463415602376221751323 31938695123403564332626985)
      ·
        refine ⟨23954021342552673249470239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31938695123403564332626985 23954021342552673249470239)
        ·
          refine ⟨35931032013829009874205359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23954021342552673249470239 35931032013829009874205359)
          ·
            refine ⟨53896548020743514811308039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35931032013829009874205359 53896548020743514811308039)
            ·
              refine ⟨80844822031115272216962059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53896548020743514811308039 80844822031115272216962059)
              ·
                refine ⟨121267233046672908325443089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80844822031115272216962059 121267233046672908325443089)
                ·
                  refine ⟨90950424785004681244082317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121267233046672908325443089 90950424785004681244082317)
                  ·
                    refine ⟨34106409294376755466530869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90950424785004681244082317 34106409294376755466530869)
                    ·
                      refine ⟨3197475871347820824987269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34106409294376755466530869 3197475871347820824987269)
                      ·
                        rfl

theorem cell23_6227062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6227062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227062 prefixEnd_6227062 := by exact prefixLift 6227062
  have htrace : WordTrace (prefixWord ++ tailWord_6227062) baseStart_6227062 baseEnd_6227062 := by
    simpa [prefixWord, tailWord_6227062, baseEnd_6227062] using wordTrace_append hprefix tailTrace_6227062
  have hstable : (prefixWord ++ tailWord_6227062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227062).length < 2 ^ (prefixWord ++ tailWord_6227062).sum := by decide
  have hdescent : baseEnd_6227062 < baseStart_6227062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227082 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_6227082 : Nat := 118140960795 + 6227082 * 2 ^ 59
def prefixEnd_6227082 : Nat := 4983230072969 + 3 ^ 40 * 6227082 * 2
def baseEnd_6227082 : Nat := 355276237884545638526353

theorem tailTrace_6227082 : CollatzResearch.WordTrace tailWord_6227082 prefixEnd_6227082 355276237884545638526353 := by
  unfold tailWord_6227082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56780084806588222445268875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151413559484235259854050333 56780084806588222445268875)
  ·
    refine ⟨85170127209882333667903313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56780084806588222445268875 85170127209882333667903313)
    ·
      refine ⟨63877595407411750250927485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85170127209882333667903313 63877595407411750250927485)
      ·
        refine ⟨23954098277779406344097807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63877595407411750250927485 23954098277779406344097807)
        ·
          refine ⟨35931147416669109516146711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23954098277779406344097807 35931147416669109516146711)
          ·
            refine ⟨53896721125003664274220067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35931147416669109516146711 53896721125003664274220067)
            ·
              refine ⟨80845081687505496411330101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53896721125003664274220067 80845081687505496411330101)
              ·
                refine ⟨7579226408203640288562197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80845081687505496411330101 7579226408203640288562197)
                ·
                  refine ⟨355276237884545638526353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7579226408203640288562197 355276237884545638526353)
                  ·
                    rfl

theorem cell23_6227082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_6227082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227082 prefixEnd_6227082 := by exact prefixLift 6227082
  have htrace : WordTrace (prefixWord ++ tailWord_6227082) baseStart_6227082 baseEnd_6227082 := by
    simpa [prefixWord, tailWord_6227082, baseEnd_6227082] using wordTrace_append hprefix tailTrace_6227082
  have hstable : (prefixWord ++ tailWord_6227082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227082).length < 2 ^ (prefixWord ++ tailWord_6227082).sum := by decide
  have hdescent : baseEnd_6227082 < baseStart_6227082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227096 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6227096 : Nat := 118140960795 + 6227096 * 2 ^ 59
def prefixEnd_6227096 : Nat := 4983230072969 + 3 ^ 40 * 6227096 * 2
def baseEnd_6227096 : Nat := 3197493329690073691962113

theorem tailTrace_6227096 : CollatzResearch.WordTrace tailWord_6227096 prefixEnd_6227096 3197493329690073691962113 := by
  unfold tailWord_6227096
  simp only [CollatzResearch.WordTrace]
  refine ⟨113560424924151085086042571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151413899898868113448056761 113560424924151085086042571)
  ·
    refine ⟨170340637386226627629063857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113560424924151085086042571 170340637386226627629063857)
    ·
      refine ⟨127755478039669970721797893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170340637386226627629063857 127755478039669970721797893)
      ·
        refine ⟨23954152132438119510337105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127755478039669970721797893 23954152132438119510337105)
        ·
          refine ⟨17965614099328589632752829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23954152132438119510337105 17965614099328589632752829)
          ·
            refine ⟨6737105287248221112282311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17965614099328589632752829 6737105287248221112282311)
            ·
              refine ⟨10105657930872331668423467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737105287248221112282311 10105657930872331668423467)
              ·
                refine ⟨15158486896308497502635201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10105657930872331668423467 15158486896308497502635201)
                ·
                  refine ⟨11368865172231373126976401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15158486896308497502635201 11368865172231373126976401)
                  ·
                    refine ⟨8526648879173529845232301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11368865172231373126976401 8526648879173529845232301)
                    ·
                      refine ⟨3197493329690073691962113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8526648879173529845232301 3197493329690073691962113)
                      ·
                        rfl

theorem cell23_6227096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6227096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227096 prefixEnd_6227096 := by exact prefixLift 6227096
  have htrace : WordTrace (prefixWord ++ tailWord_6227096) baseStart_6227096 baseEnd_6227096 := by
    simpa [prefixWord, tailWord_6227096, baseEnd_6227096] using wordTrace_append hprefix tailTrace_6227096
  have hstable : (prefixWord ++ tailWord_6227096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227096).length < 2 ^ (prefixWord ++ tailWord_6227096).sum := by decide
  have hdescent : baseEnd_6227096 < baseStart_6227096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227103 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 1, 4]
def baseStart_6227103 : Nat := 118140960795 + 6227103 * 2 ^ 59
def prefixEnd_6227103 : Nat := 4983230072969 + 3 ^ 40 * 6227103 * 2
def baseEnd_6227103 : Nat := 1065832308018218388191527

theorem tailTrace_6227103 : CollatzResearch.WordTrace tailWord_6227103 prefixEnd_6227103 1065832308018218388191527 := by
  unfold tailWord_6227103
  simp only [CollatzResearch.WordTrace]
  refine ⟨227121105159276810367589963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151414070106184540245059975 227121105159276810367589963)
  ·
    refine ⟨340681657738915215551384945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227121105159276810367589963 340681657738915215551384945)
    ·
      refine ⟨255511243304186411663538709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340681657738915215551384945 255511243304186411663538709)
      ·
        refine ⟨11977089529883738046728377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255511243304186411663538709 11977089529883738046728377)
        ·
          refine ⟨8982817147412803535046283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11977089529883738046728377 8982817147412803535046283)
          ·
            refine ⟨13474225721119205302569425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982817147412803535046283 13474225721119205302569425)
            ·
              refine ⟨10105669290839403976927069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13474225721119205302569425 10105669290839403976927069)
              ·
                refine ⟨3789625984064776491347651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10105669290839403976927069 3789625984064776491347651)
                ·
                  refine ⟨5684438976097164737021477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789625984064776491347651 5684438976097164737021477)
                  ·
                    refine ⟨1065832308018218388191527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5684438976097164737021477 1065832308018218388191527)
                    ·
                      rfl

theorem cell23_6227103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 4].length) (baseStart_6227103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227103 prefixEnd_6227103 := by exact prefixLift 6227103
  have htrace : WordTrace (prefixWord ++ tailWord_6227103) baseStart_6227103 baseEnd_6227103 := by
    simpa [prefixWord, tailWord_6227103, baseEnd_6227103] using wordTrace_append hprefix tailTrace_6227103
  have hstable : (prefixWord ++ tailWord_6227103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227103).length < 2 ^ (prefixWord ++ tailWord_6227103).sum := by decide
  have hdescent : baseEnd_6227103 < baseStart_6227103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227119 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 2, 3, 2]
def baseStart_6227119 : Nat := 118140960795 + 6227119 * 2 ^ 59
def prefixEnd_6227119 : Nat := 4983230072969 + 3 ^ 40 * 6227119 * 2
def baseEnd_6227119 : Nat := 3197505139745127101974507

theorem tailTrace_6227119 : CollatzResearch.WordTrace tailWord_6227119 prefixEnd_6227119 3197505139745127101974507 := by
  unfold tailWord_6227119
  simp only [CollatzResearch.WordTrace]
  refine ⟨227121688727218845100172411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151414459151479230066781607 227121688727218845100172411)
  ·
    refine ⟨340682533090828267650258617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227121688727218845100172411 340682533090828267650258617)
    ·
      refine ⟨255511899818121200737693963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340682533090828267650258617 255511899818121200737693963)
      ·
        refine ⟨383267849727181801106540945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255511899818121200737693963 383267849727181801106540945)
        ·
          refine ⟨287450887295386350829905709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383267849727181801106540945 287450887295386350829905709)
          ·
            refine ⟨107794082735769881561214641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287450887295386350829905709 107794082735769881561214641)
            ·
              refine ⟨80845562051827411170910981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107794082735769881561214641 80845562051827411170910981)
              ·
                refine ⟨15158542884717639594545809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80845562051827411170910981 15158542884717639594545809)
                ·
                  refine ⟨11368907163538229695909357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15158542884717639594545809 11368907163538229695909357)
                  ·
                    refine ⟨4263340186326836135966009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11368907163538229695909357 4263340186326836135966009)
                    ·
                      refine ⟨3197505139745127101974507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263340186326836135966009 3197505139745127101974507)
                      ·
                        rfl

theorem cell23_6227119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3, 2].length) (baseStart_6227119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227119 prefixEnd_6227119 := by exact prefixLift 6227119
  have htrace : WordTrace (prefixWord ++ tailWord_6227119) baseStart_6227119 baseEnd_6227119 := by
    simpa [prefixWord, tailWord_6227119, baseEnd_6227119] using wordTrace_append hprefix tailTrace_6227119
  have hstable : (prefixWord ++ tailWord_6227119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227119).length < 2 ^ (prefixWord ++ tailWord_6227119).sum := by decide
  have hdescent : baseEnd_6227119 < baseStart_6227119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227155 : List Nat := [1, 1, 1, 2, 1, 1, 1, 15]
def baseStart_6227155 : Nat := 118140960795 + 6227155 * 2 ^ 59
def prefixEnd_6227155 : Nat := 4983230072969 + 3 ^ 40 * 6227155 * 2
def baseEnd_6227155 : Nat := 118426800927729220782383

theorem tailTrace_6227155 : CollatzResearch.WordTrace tailWord_6227155 prefixEnd_6227155 118426800927729220782383 := by
  unfold tailWord_6227155
  simp only [CollatzResearch.WordTrace]
  refine ⟨227123001755088423248482919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151415334503392282165655279 227123001755088423248482919)
  ·
    refine ⟨340684502632632634872724379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227123001755088423248482919 340684502632632634872724379)
    ·
      refine ⟨511026753948948952309086569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340684502632632634872724379 511026753948948952309086569)
      ·
        refine ⟨383270065461711714231814927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511026753948948952309086569 383270065461711714231814927)
        ·
          refine ⟨574905098192567571347722391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383270065461711714231814927 574905098192567571347722391)
          ·
            refine ⟨862357647288851357021583587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574905098192567571347722391 862357647288851357021583587)
            ·
              refine ⟨1293536470933277035532375381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862357647288851357021583587 1293536470933277035532375381)
              ·
                refine ⟨118426800927729220782383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 1293536470933277035532375381 118426800927729220782383)
                ·
                  rfl

theorem cell23_6227155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 15].length) (baseStart_6227155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227155 prefixEnd_6227155 := by exact prefixLift 6227155
  have htrace : WordTrace (prefixWord ++ tailWord_6227155) baseStart_6227155 baseEnd_6227155 := by
    simpa [prefixWord, tailWord_6227155, baseEnd_6227155] using wordTrace_append hprefix tailTrace_6227155
  have hstable : (prefixWord ++ tailWord_6227155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227155).length < 2 ^ (prefixWord ++ tailWord_6227155).sum := by decide
  have hdescent : baseEnd_6227155 < baseStart_6227155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227160 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 1, 1, 3]
def baseStart_6227160 : Nat := 118140960795 + 6227160 * 2 ^ 59
def prefixEnd_6227160 : Nat := 4983230072969 + 3 ^ 40 * 6227160 * 2
def baseEnd_6227160 : Nat := 3197526192451961441561819

theorem tailTrace_6227160 : CollatzResearch.WordTrace tailWord_6227160 prefixEnd_6227160 3197526192451961441561819 := by
  unfold tailWord_6227160
  simp only [CollatzResearch.WordTrace]
  refine ⟨113561592060035154551207467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151415456080046872734943289 113561592060035154551207467)
  ·
    refine ⟨170342388090052731826811201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113561592060035154551207467 170342388090052731826811201)
    ·
      refine ⟨127756791067539548870108401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170342388090052731826811201 127756791067539548870108401)
      ·
        refine ⟨95817593300654661652581301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127756791067539548870108401 95817593300654661652581301)
        ·
          refine ⟨8982899371936374529929497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95817593300654661652581301 8982899371936374529929497)
          ·
            refine ⟨6737174528952280897447123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8982899371936374529929497 6737174528952280897447123)
            ·
              refine ⟨10105761793428421346170685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737174528952280897447123 10105761793428421346170685)
              ·
                refine ⟨3789660672535658004814007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10105761793428421346170685 3789660672535658004814007)
                ·
                  refine ⟨5684491008803487007221011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789660672535658004814007 5684491008803487007221011)
                  ·
                    refine ⟨8526736513205230510831517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5684491008803487007221011 8526736513205230510831517)
                    ·
                      refine ⟨3197526192451961441561819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8526736513205230510831517 3197526192451961441561819)
                      ·
                        rfl

theorem cell23_6227160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_6227160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227160 prefixEnd_6227160 := by exact prefixLift 6227160
  have htrace : WordTrace (prefixWord ++ tailWord_6227160) baseStart_6227160 baseEnd_6227160 := by
    simpa [prefixWord, tailWord_6227160, baseEnd_6227160] using wordTrace_append hprefix tailTrace_6227160
  have hstable : (prefixWord ++ tailWord_6227160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227160).length < 2 ^ (prefixWord ++ tailWord_6227160).sum := by decide
  have hdescent : baseEnd_6227160 < baseStart_6227160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227162 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_6227162 : Nat := 118140960795 + 6227162 * 2 ^ 59
def prefixEnd_6227162 : Nat := 4983230072969 + 3 ^ 40 * 6227162 * 2
def baseEnd_6227162 : Nat := 3197527219413270433736809

theorem tailTrace_6227162 : CollatzResearch.WordTrace tailWord_6227162 prefixEnd_6227162 3197527219413270433736809 := by
  unfold tailWord_6227162
  simp only [CollatzResearch.WordTrace]
  refine ⟨56780814266515765860996935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151415504710708708962658493 56780814266515765860996935)
  ·
    refine ⟨85171221399773648791495403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56780814266515765860996935 85171221399773648791495403)
    ·
      refine ⟨127756832099660473187243105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85171221399773648791495403 127756832099660473187243105)
      ·
        refine ⟨95817624074745354890432329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127756832099660473187243105 95817624074745354890432329)
        ·
          refine ⟨71863218056059016167824247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95817624074745354890432329 71863218056059016167824247)
          ·
            refine ⟨107794827084088524251736371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71863218056059016167824247 107794827084088524251736371)
            ·
              refine ⟨161692240626132786377604557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107794827084088524251736371 161692240626132786377604557)
              ·
                refine ⟨60634590234799794891601709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161692240626132786377604557 60634590234799794891601709)
                ·
                  refine ⟨22737971338049923084350641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60634590234799794891601709 22737971338049923084350641)
                  ·
                    refine ⟨17053478503537442313262981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22737971338049923084350641 17053478503537442313262981)
                    ·
                      refine ⟨3197527219413270433736809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17053478503537442313262981 3197527219413270433736809)
                      ·
                        rfl

theorem cell23_6227162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_6227162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227162 prefixEnd_6227162 := by exact prefixLift 6227162
  have htrace : WordTrace (prefixWord ++ tailWord_6227162) baseStart_6227162 baseEnd_6227162 := by
    simpa [prefixWord, tailWord_6227162, baseEnd_6227162] using wordTrace_append hprefix tailTrace_6227162
  have hstable : (prefixWord ++ tailWord_6227162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227162).length < 2 ^ (prefixWord ++ tailWord_6227162).sum := by decide
  have hdescent : baseEnd_6227162 < baseStart_6227162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227169 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_6227169 : Nat := 118140960795 + 6227169 * 2 ^ 59
def prefixEnd_6227169 : Nat := 4983230072969 + 3 ^ 40 * 6227169 * 2
def baseEnd_6227169 : Nat := 3197530813777851906349277

theorem tailTrace_6227169 : CollatzResearch.WordTrace tailWord_6227169 prefixEnd_6227169 3197530813777851906349277 := by
  unfold tailWord_6227169
  simp only [CollatzResearch.WordTrace]
  refine ⟨227123512377037703639492561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151415674918025135759661707 227123512377037703639492561)
  ·
    refine ⟨170342634282778277729619421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227123512377037703639492561 170342634282778277729619421)
    ·
      refine ⟨63878487856041854148607283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170342634282778277729619421 63878487856041854148607283)
      ·
        refine ⟨95817731784062781222910925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63878487856041854148607283 95817731784062781222910925)
        ·
          refine ⟨35931649419023542958591597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95817731784062781222910925 35931649419023542958591597)
          ·
            refine ⟨13474368532133828609471849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35931649419023542958591597 13474368532133828609471849)
            ·
              refine ⟨10105776399100371457103887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13474368532133828609471849 10105776399100371457103887)
              ·
                refine ⟨15158664598650557185655831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10105776399100371457103887 15158664598650557185655831)
                ·
                  refine ⟨22737996897975835778483747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15158664598650557185655831 22737996897975835778483747)
                  ·
                    refine ⟨34106995346963753667725621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22737996897975835778483747 34106995346963753667725621)
                    ·
                      refine ⟨3197530813777851906349277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34106995346963753667725621 3197530813777851906349277)
                      ·
                        rfl

theorem cell23_6227169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_6227169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227169 prefixEnd_6227169 := by exact prefixLift 6227169
  have htrace : WordTrace (prefixWord ++ tailWord_6227169) baseStart_6227169 baseEnd_6227169 := by
    simpa [prefixWord, tailWord_6227169, baseEnd_6227169] using wordTrace_append hprefix tailTrace_6227169
  have hstable : (prefixWord ++ tailWord_6227169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227169).length < 2 ^ (prefixWord ++ tailWord_6227169).sum := by decide
  have hdescent : baseEnd_6227169 < baseStart_6227169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227234 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_6227234 : Nat := 118140960795 + 6227234 * 2 ^ 59
def prefixEnd_6227234 : Nat := 4983230072969 + 3 ^ 40 * 6227234 * 2
def baseEnd_6227234 : Nat := 3197564190020394152036479

theorem tailTrace_6227234 : CollatzResearch.WordTrace tailWord_6227234 prefixEnd_6227234 3197564190020394152036479 := by
  unfold tailWord_6227234
  simp only [CollatzResearch.WordTrace]
  refine ⟨56781470780450554935152189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151417255414534813160405837 56781470780450554935152189)
  ·
    refine ⟨21293051542668958100682071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56781470780450554935152189 21293051542668958100682071)
    ·
      refine ⟨31939577314003437151023107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293051542668958100682071 31939577314003437151023107)
      ·
        refine ⟨47909365971005155726534661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31939577314003437151023107 47909365971005155726534661)
        ·
          refine ⟨8983006119563466698725249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47909365971005155726534661 8983006119563466698725249)
          ·
            refine ⟨6737254589672600024043937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8983006119563466698725249 6737254589672600024043937)
            ·
              refine ⟨5052940942254450018032953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6737254589672600024043937 5052940942254450018032953)
              ·
                refine ⟨3789705706690837513524715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052940942254450018032953 3789705706690837513524715)
                ·
                  refine ⟨5684558560036256270287073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789705706690837513524715 5684558560036256270287073)
                  ·
                    refine ⟨4263418920027192202715305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5684558560036256270287073 4263418920027192202715305)
                    ·
                      refine ⟨3197564190020394152036479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263418920027192202715305 3197564190020394152036479)
                      ·
                        rfl

theorem cell23_6227234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_6227234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227234 prefixEnd_6227234 := by exact prefixLift 6227234
  have htrace : WordTrace (prefixWord ++ tailWord_6227234) baseStart_6227234 baseEnd_6227234 := by
    simpa [prefixWord, tailWord_6227234, baseEnd_6227234] using wordTrace_append hprefix tailTrace_6227234
  have hstable : (prefixWord ++ tailWord_6227234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227234).length < 2 ^ (prefixWord ++ tailWord_6227234).sum := by decide
  have hdescent : baseEnd_6227234 < baseStart_6227234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227249 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_6227249 : Nat := 118140960795 + 6227249 * 2 ^ 59
def prefixEnd_6227249 : Nat := 4983230072969 + 3 ^ 40 * 6227249 * 2
def baseEnd_6227249 : Nat := 1065857297410070531116303

theorem tailTrace_6227249 : CollatzResearch.WordTrace tailWord_6227249 prefixEnd_6227249 1065857297410070531116303 := by
  unfold tailWord_6227249
  simp only [CollatzResearch.WordTrace]
  refine ⟨227126430216747877302404801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151417620144498584868269867 227126430216747877302404801)
  ·
    refine ⟨170344822662560907976803601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227126430216747877302404801 170344822662560907976803601)
    ·
      refine ⟨127758616996920680982602701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170344822662560907976803601 127758616996920680982602701)
      ·
        refine ⟨47909481373845255368476013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127758616996920680982602701 47909481373845255368476013)
        ·
          refine ⟨17966055515191970763178505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47909481373845255368476013 17966055515191970763178505)
          ·
            refine ⟨13474541636393978072383879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17966055515191970763178505 13474541636393978072383879)
            ·
              refine ⟨20211812454590967108575819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13474541636393978072383879 20211812454590967108575819)
              ·
                refine ⟨30317718681886450662863729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20211812454590967108575819 30317718681886450662863729)
                ·
                  refine ⟨22738289011414837997147797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30317718681886450662863729 22738289011414837997147797)
                  ·
                    refine ⟨1065857297410070531116303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22738289011414837997147797 1065857297410070531116303)
                    ·
                      rfl

theorem cell23_6227249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_6227249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227249 prefixEnd_6227249 := by exact prefixLift 6227249
  have htrace : WordTrace (prefixWord ++ tailWord_6227249) baseStart_6227249 baseEnd_6227249 := by
    simpa [prefixWord, tailWord_6227249, baseEnd_6227249] using wordTrace_append hprefix tailTrace_6227249
  have hstable : (prefixWord ++ tailWord_6227249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227249).length < 2 ^ (prefixWord ++ tailWord_6227249).sum := by decide
  have hdescent : baseEnd_6227249 < baseStart_6227249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227256 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 6, 2, 2]
def baseStart_6227256 : Nat := 118140960795 + 6227256 * 2 ^ 59
def prefixEnd_6227256 : Nat := 4983230072969 + 3 ^ 40 * 6227256 * 2
def baseEnd_6227256 : Nat := 3197575486594793065961377

theorem tailTrace_6227256 : CollatzResearch.WordTrace tailWord_6227256 prefixEnd_6227256 3197575486594793065961377 := by
  unfold tailWord_6227256
  simp only [CollatzResearch.WordTrace]
  refine ⟨113563342763861258748954811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151417790351815011665273081 113563342763861258748954811)
  ·
    refine ⟨170345014145791888123432217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113563342763861258748954811 170345014145791888123432217)
    ·
      refine ⟨127758760609343916092574163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170345014145791888123432217 127758760609343916092574163)
      ·
        refine ⟨191638140914015874138861245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127758760609343916092574163 191638140914015874138861245)
        ·
          refine ⟨71864302842755952802072967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191638140914015874138861245 71864302842755952802072967)
          ·
            refine ⟨107796454264133929203109451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71864302842755952802072967 107796454264133929203109451)
            ·
              refine ⟨161694681396200893804664177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107796454264133929203109451 161694681396200893804664177)
              ·
                refine ⟨121271011047150670353498133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161694681396200893804664177 121271011047150670353498133)
                ·
                  refine ⟨5684578642835187672820225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121271011047150670353498133 5684578642835187672820225)
                  ·
                    refine ⟨4263433982126390754615169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5684578642835187672820225 4263433982126390754615169)
                    ·
                      refine ⟨3197575486594793065961377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263433982126390754615169 3197575486594793065961377)
                      ·
                        rfl

theorem cell23_6227256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_6227256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227256 prefixEnd_6227256 := by exact prefixLift 6227256
  have htrace : WordTrace (prefixWord ++ tailWord_6227256) baseStart_6227256 baseEnd_6227256 := by
    simpa [prefixWord, tailWord_6227256, baseEnd_6227256] using wordTrace_append hprefix tailTrace_6227256
  have hstable : (prefixWord ++ tailWord_6227256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227256).length < 2 ^ (prefixWord ++ tailWord_6227256).sum := by decide
  have hdescent : baseEnd_6227256 < baseStart_6227256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227272 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_6227272 : Nat := 118140960795 + 6227272 * 2 ^ 59
def prefixEnd_6227272 : Nat := 4983230072969 + 3 ^ 40 * 6227272 * 2
def baseEnd_6227272 : Nat := 3197583702285265003361303

theorem tailTrace_6227272 : CollatzResearch.WordTrace tailWord_6227272 prefixEnd_6227272 3197583702285265003361303 := by
  unfold tailWord_6227272
  simp only [CollatzResearch.WordTrace]
  refine ⟨113563634547832276115246035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151418179397109701486994713 113563634547832276115246035)
  ·
    refine ⟨170345451821748414172869053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113563634547832276115246035 170345451821748414172869053)
    ·
      refine ⟨63879544433155655314825895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170345451821748414172869053 63879544433155655314825895)
      ·
        refine ⟨95819316649733482972238843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63879544433155655314825895 95819316649733482972238843)
        ·
          refine ⟨143728974974600224458358265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95819316649733482972238843 143728974974600224458358265)
          ·
            refine ⟨107796731230950168343768699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143728974974600224458358265 107796731230950168343768699)
            ·
              refine ⟨161695096846425252515653049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107796731230950168343768699 161695096846425252515653049)
              ·
                refine ⟨121271322634818939386739787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161695096846425252515653049 121271322634818939386739787)
                ·
                  refine ⟨181906983952228409080109681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121271322634818939386739787 181906983952228409080109681)
                  ·
                    refine ⟨136430237964171306810082261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181906983952228409080109681 136430237964171306810082261)
                    ·
                      refine ⟨3197583702285265003361303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136430237964171306810082261 3197583702285265003361303)
                      ·
                        rfl

theorem cell23_6227272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_6227272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227272 prefixEnd_6227272 := by exact prefixLift 6227272
  have htrace : WordTrace (prefixWord ++ tailWord_6227272) baseStart_6227272 baseEnd_6227272 := by
    simpa [prefixWord, tailWord_6227272, baseEnd_6227272] using wordTrace_append hprefix tailTrace_6227272
  have hstable : (prefixWord ++ tailWord_6227272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227272).length < 2 ^ (prefixWord ++ tailWord_6227272).sum := by decide
  have hdescent : baseEnd_6227272 < baseStart_6227272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227277 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6227277 : Nat := 118140960795 + 6227277 * 2 ^ 59
def prefixEnd_6227277 : Nat := 4983230072969 + 3 ^ 40 * 6227277 * 2
def baseEnd_6227277 : Nat := 3197586269688537483798781

theorem tailTrace_6227277 : CollatzResearch.WordTrace tailWord_6227277 prefixEnd_6227277 3197586269688537483798781 := by
  unfold tailWord_6227277
  simp only [CollatzResearch.WordTrace]
  refine ⟨227127451460646438084424085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151418300973764292056282723 227127451460646438084424085)
  ·
    refine ⟨10646599287217801785207379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227127451460646438084424085 10646599287217801785207379)
    ·
      refine ⟨15969898930826702677811069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10646599287217801785207379 15969898930826702677811069)
      ·
        refine ⟨5988712099060013504179151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15969898930826702677811069 5988712099060013504179151)
        ·
          refine ⟨8983068148590020256268727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988712099060013504179151 8983068148590020256268727)
          ·
            refine ⟨13474602222885030384403091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8983068148590020256268727 13474602222885030384403091)
            ·
              refine ⟨20211903334327545576604637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13474602222885030384403091 20211903334327545576604637)
              ·
                refine ⟨7579463750372829591226739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20211903334327545576604637 7579463750372829591226739)
                ·
                  refine ⟨11369195625559244386840109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7579463750372829591226739 11369195625559244386840109)
                  ·
                    refine ⟨4263448359584716645065041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11369195625559244386840109 4263448359584716645065041)
                    ·
                      refine ⟨3197586269688537483798781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263448359584716645065041 3197586269688537483798781)
                      ·
                        rfl

theorem cell23_6227277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6227277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227277 prefixEnd_6227277 := by exact prefixLift 6227277
  have htrace : WordTrace (prefixWord ++ tailWord_6227277) baseStart_6227277 baseEnd_6227277 := by
    simpa [prefixWord, tailWord_6227277, baseEnd_6227277] using wordTrace_append hprefix tailTrace_6227277
  have hstable : (prefixWord ++ tailWord_6227277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227277).length < 2 ^ (prefixWord ++ tailWord_6227277).sum := by decide
  have hdescent : baseEnd_6227277 < baseStart_6227277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227289 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_6227289 : Nat := 118140960795 + 6227289 * 2 ^ 59
def prefixEnd_6227289 : Nat := 4983230072969 + 3 ^ 40 * 6227289 * 2
def baseEnd_6227289 : Nat := 3197592431456391436848725

theorem tailTrace_6227289 : CollatzResearch.WordTrace tailWord_6227289 prefixEnd_6227289 3197592431456391436848725 := by
  unfold tailWord_6227289
  simp only [CollatzResearch.WordTrace]
  refine ⟨227127889136602964133860921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151418592757735309422573947 227127889136602964133860921)
  ·
    refine ⟨170345916852452223100395691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227127889136602964133860921 170345916852452223100395691)
    ·
      refine ⟨255518875278678334650593537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170345916852452223100395691 255518875278678334650593537)
      ·
        refine ⟨191639156459008750987945153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255518875278678334650593537 191639156459008750987945153)
        ·
          refine ⟨143729367344256563240958865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191639156459008750987945153 143729367344256563240958865)
          ·
            refine ⟨107797025508192422430719149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143729367344256563240958865 107797025508192422430719149)
            ·
              refine ⟨40423884565572158411519681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107797025508192422430719149 40423884565572158411519681)
              ·
                refine ⟨30317913424179118808639761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40423884565572158411519681 30317913424179118808639761)
                ·
                  refine ⟨22738435068134339106479821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30317913424179118808639761 22738435068134339106479821)
                  ·
                    refine ⟨8526913150550377164929933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22738435068134339106479821 8526913150550377164929933)
                    ·
                      refine ⟨3197592431456391436848725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8526913150550377164929933 3197592431456391436848725)
                      ·
                        rfl

theorem cell23_6227289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_6227289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227289 prefixEnd_6227289 := by exact prefixLift 6227289
  have htrace : WordTrace (prefixWord ++ tailWord_6227289) baseStart_6227289 baseEnd_6227289 := by
    simpa [prefixWord, tailWord_6227289, baseEnd_6227289] using wordTrace_append hprefix tailTrace_6227289
  have hstable : (prefixWord ++ tailWord_6227289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227289).length < 2 ^ (prefixWord ++ tailWord_6227289).sum := by decide
  have hdescent : baseEnd_6227289 < baseStart_6227289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227296 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 5]
def baseStart_6227296 : Nat := 118140960795 + 6227296 * 2 ^ 59
def prefixEnd_6227296 : Nat := 4983230072969 + 3 ^ 40 * 6227296 * 2
def baseEnd_6227296 : Nat := 355288447313441434384577

theorem tailTrace_6227296 : CollatzResearch.WordTrace tailWord_6227296 prefixEnd_6227296 355288447313441434384577 := by
  unfold tailWord_6227296
  simp only [CollatzResearch.WordTrace]
  refine ⟨113564072223788802164682871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151418762965051736219577161 113564072223788802164682871)
  ·
    refine ⟨170346108335683203247024307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113564072223788802164682871 170346108335683203247024307)
    ·
      refine ⟨255519162503524804870536461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170346108335683203247024307 255519162503524804870536461)
      ·
        refine ⟨95819685938821801826451173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255519162503524804870536461 95819685938821801826451173)
        ·
          refine ⟨17966191113529087842459595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95819685938821801826451173 17966191113529087842459595)
          ·
            refine ⟨26949286670293631763689393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17966191113529087842459595 26949286670293631763689393)
            ·
              refine ⟨20211965002720223822767045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26949286670293631763689393 20211965002720223822767045)
              ·
                refine ⟨3789743438010041966768821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20211965002720223822767045 3789743438010041966768821)
                ·
                  refine ⟨355288447313441434384577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789743438010041966768821 355288447313441434384577)
                  ·
                    rfl

theorem cell23_6227296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 5].length) (baseStart_6227296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227296 prefixEnd_6227296 := by exact prefixLift 6227296
  have htrace : WordTrace (prefixWord ++ tailWord_6227296) baseStart_6227296 baseEnd_6227296 := by
    simpa [prefixWord, tailWord_6227296, baseEnd_6227296] using wordTrace_append hprefix tailTrace_6227296
  have hstable : (prefixWord ++ tailWord_6227296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227296).length < 2 ^ (prefixWord ++ tailWord_6227296).sum := by decide
  have hdescent : baseEnd_6227296 < baseStart_6227296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227309 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_6227309 : Nat := 118140960795 + 6227309 * 2 ^ 59
def prefixEnd_6227309 : Nat := 4983230072969 + 3 ^ 40 * 6227309 * 2
def baseEnd_6227309 : Nat := 1065867567023160452866211

theorem tailTrace_6227309 : CollatzResearch.WordTrace tailWord_6227309 prefixEnd_6227309 1065867567023160452866211 := by
  unfold tailWord_6227309
  simp only [CollatzResearch.WordTrace]
  refine ⟨227128618596530507549588981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151419079064353671699725987 227128618596530507549588981)
  ·
    refine ⟨21293307993424735082773967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227128618596530507549588981 21293307993424735082773967)
    ·
      refine ⟨31939961990137102624160951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293307993424735082773967 31939961990137102624160951)
      ·
        refine ⟨47909942985205653936241427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31939961990137102624160951 47909942985205653936241427)
        ·
          refine ⟨71864914477808480904362141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47909942985205653936241427 71864914477808480904362141)
          ·
            refine ⟨26949342929178180339135803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71864914477808480904362141 26949342929178180339135803)
            ·
              refine ⟨40424014393767270508703705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26949342929178180339135803 40424014393767270508703705)
              ·
                refine ⟨30318010795325452881527779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40424014393767270508703705 30318010795325452881527779)
                ·
                  refine ⟨45477016192988179322291669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30318010795325452881527779 45477016192988179322291669)
                  ·
                    refine ⟨1065867567023160452866211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45477016192988179322291669 1065867567023160452866211)
                    ·
                      rfl

theorem cell23_6227309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_6227309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227309 prefixEnd_6227309 := by exact prefixLift 6227309
  have htrace : WordTrace (prefixWord ++ tailWord_6227309) baseStart_6227309 baseEnd_6227309 := by
    simpa [prefixWord, tailWord_6227309, baseEnd_6227309] using wordTrace_append hprefix tailTrace_6227309
  have hstable : (prefixWord ++ tailWord_6227309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227309).length < 2 ^ (prefixWord ++ tailWord_6227309).sum := by decide
  have hdescent : baseEnd_6227309 < baseStart_6227309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227330 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_6227330 : Nat := 118140960795 + 6227330 * 2 ^ 59
def prefixEnd_6227330 : Nat := 4983230072969 + 3 ^ 40 * 6227330 * 2
def baseEnd_6227330 : Nat := 355290387129247308492893

theorem tailTrace_6227330 : CollatzResearch.WordTrace tailWord_6227330 prefixEnd_6227330 355290387129247308492893 := by
  unfold tailWord_6227330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56782346132363607034025861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151419589686302952090735629 56782346132363607034025861)
  ·
    refine ⟨10646689899818176318879849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56782346132363607034025861 10646689899818176318879849)
    ·
      refine ⟨7985017424863632239159887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10646689899818176318879849 7985017424863632239159887)
      ·
        refine ⟨11977526137295448358739831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985017424863632239159887 11977526137295448358739831)
        ·
          refine ⟨17966289205943172538109747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11977526137295448358739831 17966289205943172538109747)
          ·
            refine ⟨26949433808914758807164621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17966289205943172538109747 26949433808914758807164621)
            ·
              refine ⟨10106037678343034552686733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26949433808914758807164621 10106037678343034552686733)
              ·
                refine ⟨3789764129378637957257525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10106037678343034552686733 3789764129378637957257525)
                ·
                  refine ⟨355290387129247308492893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789764129378637957257525 355290387129247308492893)
                  ·
                    rfl

theorem cell23_6227330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_6227330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227330 prefixEnd_6227330 := by exact prefixLift 6227330
  have htrace : WordTrace (prefixWord ++ tailWord_6227330) baseStart_6227330 baseEnd_6227330 := by
    simpa [prefixWord, tailWord_6227330, baseEnd_6227330] using wordTrace_append hprefix tailTrace_6227330
  have hstable : (prefixWord ++ tailWord_6227330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227330).length < 2 ^ (prefixWord ++ tailWord_6227330).sum := by decide
  have hdescent : baseEnd_6227330 < baseStart_6227330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227379 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 3]
def baseStart_6227379 : Nat := 118140960795 + 6227379 * 2 ^ 59
def prefixEnd_6227379 : Nat := 4983230072969 + 3 ^ 40 * 6227379 * 2
def baseEnd_6227379 : Nat := 3197638644715296084723311

theorem tailTrace_6227379 : CollatzResearch.WordTrace tailWord_6227379 prefixEnd_6227379 3197638644715296084723311 := by
  unfold tailWord_6227379
  simp only [CollatzResearch.WordTrace]
  refine ⟨227131171706276909504637191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151420781137517939669758127 227131171706276909504637191)
  ·
    refine ⟨340696757559415364256955787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227131171706276909504637191 340696757559415364256955787)
    ·
      refine ⟨511045136339123046385433681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340696757559415364256955787 511045136339123046385433681)
      ·
        refine ⟨383283852254342284789075261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511045136339123046385433681 383283852254342284789075261)
        ·
          refine ⟨143731444595378356795903223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383283852254342284789075261 143731444595378356795903223)
          ·
            refine ⟨215597166893067535193854835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143731444595378356795903223 215597166893067535193854835)
            ·
              refine ⟨323395750339601302790782253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215597166893067535193854835 323395750339601302790782253)
              ·
                refine ⟨121273406377350488546543345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323395750339601302790782253 121273406377350488546543345)
                ·
                  refine ⟨90955054783012866409907509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121273406377350488546543345 90955054783012866409907509)
                  ·
                    refine ⟨8527036385907456225928829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90955054783012866409907509 8527036385907456225928829)
                    ·
                      refine ⟨3197638644715296084723311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527036385907456225928829 3197638644715296084723311)
                      ·
                        rfl

theorem cell23_6227379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_6227379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227379 prefixEnd_6227379 := by exact prefixLift 6227379
  have htrace : WordTrace (prefixWord ++ tailWord_6227379) baseStart_6227379 baseEnd_6227379 := by
    simpa [prefixWord, tailWord_6227379, baseEnd_6227379] using wordTrace_append hprefix tailTrace_6227379
  have hstable : (prefixWord ++ tailWord_6227379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227379).length < 2 ^ (prefixWord ++ tailWord_6227379).sum := by decide
  have hdescent : baseEnd_6227379 < baseStart_6227379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227413 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6227413 : Nat := 118140960795 + 6227413 * 2 ^ 59
def prefixEnd_6227413 : Nat := 4983230072969 + 3 ^ 40 * 6227413 * 2
def baseEnd_6227413 : Nat := 3197656103057548951698155

theorem tailTrace_6227413 : CollatzResearch.WordTrace tailWord_6227413 prefixEnd_6227413 3197656103057548951698155 := by
  unfold tailWord_6227413
  simp only [CollatzResearch.WordTrace]
  refine ⟨227132411788153733311374893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151421607858769155540916595 227132411788153733311374893)
  ·
    refine ⟨85174654420557649991765585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227132411788153733311374893 85174654420557649991765585)
    ·
      refine ⟨63880990815418237493824189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85174654420557649991765585 63880990815418237493824189)
      ·
        refine ⟨23955371555781839060184071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63880990815418237493824189 23955371555781839060184071)
        ·
          refine ⟨35933057333672758590276107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23955371555781839060184071 35933057333672758590276107)
          ·
            refine ⟨53899586000509137885414161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35933057333672758590276107 53899586000509137885414161)
            ·
              refine ⟨40424689500381853414060621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53899586000509137885414161 40424689500381853414060621)
              ·
                refine ⟨15159258562643195030272733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40424689500381853414060621 15159258562643195030272733)
                ·
                  refine ⟨5684721960991198136352275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15159258562643195030272733 5684721960991198136352275)
                  ·
                    refine ⟨8527082941486797204528413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5684721960991198136352275 8527082941486797204528413)
                    ·
                      refine ⟨3197656103057548951698155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527082941486797204528413 3197656103057548951698155)
                      ·
                        rfl

theorem cell23_6227413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6227413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227413 prefixEnd_6227413 := by exact prefixLift 6227413
  have htrace : WordTrace (prefixWord ++ tailWord_6227413) baseStart_6227413 baseEnd_6227413 := by
    simpa [prefixWord, tailWord_6227413, baseEnd_6227413] using wordTrace_append hprefix tailTrace_6227413
  have hstable : (prefixWord ++ tailWord_6227413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227413).length < 2 ^ (prefixWord ++ tailWord_6227413).sum := by decide
  have hdescent : baseEnd_6227413 < baseStart_6227413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227436 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 8, 2]
def baseStart_6227436 : Nat := 118140960795 + 6227436 * 2 ^ 59
def prefixEnd_6227436 : Nat := 4983230072969 + 3 ^ 40 * 6227436 * 2
def baseEnd_6227436 : Nat := 3197667913112602361710549

theorem tailTrace_6227436 : CollatzResearch.WordTrace tailWord_6227436 prefixEnd_6227436 3197667913112602361710549 := by
  unfold tailWord_6227436
  simp only [CollatzResearch.WordTrace]
  refine ⟨113566625333535204119731081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151422167111380272159641441 113566625333535204119731081)
  ·
    refine ⟨85174969000151403089798311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113566625333535204119731081 85174969000151403089798311)
    ·
      refine ⟨127762453500227104634697467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85174969000151403089798311 127762453500227104634697467)
      ·
        refine ⟨191643680250340656952046201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127762453500227104634697467 191643680250340656952046201)
        ·
          refine ⟨143732760187755492714034651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191643680250340656952046201 143732760187755492714034651)
          ·
            refine ⟨215599140281633239071051977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143732760187755492714034651 215599140281633239071051977)
            ·
              refine ⟨161699355211224929303288983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215599140281633239071051977 161699355211224929303288983)
              ·
                refine ⟨242549032816837393954933475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161699355211224929303288983 242549032816837393954933475)
                ·
                  refine ⟨363823549225256090932400213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242549032816837393954933475 363823549225256090932400213)
                  ·
                    refine ⟨4263557217483469815614065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 363823549225256090932400213 4263557217483469815614065)
                    ·
                      refine ⟨3197667913112602361710549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263557217483469815614065 3197667913112602361710549)
                      ·
                        rfl

theorem cell23_6227436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_6227436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227436 prefixEnd_6227436 := by exact prefixLift 6227436
  have htrace : WordTrace (prefixWord ++ tailWord_6227436) baseStart_6227436 baseEnd_6227436 := by
    simpa [prefixWord, tailWord_6227436, baseEnd_6227436] using wordTrace_append hprefix tailTrace_6227436
  have hstable : (prefixWord ++ tailWord_6227436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227436).length < 2 ^ (prefixWord ++ tailWord_6227436).sum := by decide
  have hdescent : baseEnd_6227436 < baseStart_6227436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227440 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 2, 3, 2]
def baseStart_6227440 : Nat := 118140960795 + 6227440 * 2 ^ 59
def prefixEnd_6227440 : Nat := 4983230072969 + 3 ^ 40 * 6227440 * 2
def baseEnd_6227440 : Nat := 3197669967035220346060531

theorem tailTrace_6227440 : CollatzResearch.WordTrace tailWord_6227440 prefixEnd_6227440 3197669967035220346060531 := by
  unfold tailWord_6227440
  simp only [CollatzResearch.WordTrace]
  refine ⟨113566698279527958461303887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151422264372703944615071849 113566698279527958461303887)
  ·
    refine ⟨170350047419291937691955831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113566698279527958461303887 170350047419291937691955831)
    ·
      refine ⟨255525071128937906537933747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170350047419291937691955831 255525071128937906537933747)
      ·
        refine ⟨383287606693406859806900621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255525071128937906537933747 383287606693406859806900621)
        ·
          refine ⟨143732852510027572427587733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383287606693406859806900621 143732852510027572427587733)
          ·
            refine ⟨6737477461407542457543175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143732852510027572427587733 6737477461407542457543175)
            ·
              refine ⟨10106216192111313686314763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737477461407542457543175 10106216192111313686314763)
              ·
                refine ⟨15159324288166970529472145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10106216192111313686314763 15159324288166970529472145)
                ·
                  refine ⟨11369493216125227897104109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15159324288166970529472145 11369493216125227897104109)
                  ·
                    refine ⟨4263559956046960461414041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11369493216125227897104109 4263559956046960461414041)
                    ·
                      refine ⟨3197669967035220346060531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263559956046960461414041 3197669967035220346060531)
                      ·
                        rfl

theorem cell23_6227440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 3, 2].length) (baseStart_6227440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227440 prefixEnd_6227440 := by exact prefixLift 6227440
  have htrace : WordTrace (prefixWord ++ tailWord_6227440) baseStart_6227440 baseEnd_6227440 := by
    simpa [prefixWord, tailWord_6227440, baseEnd_6227440] using wordTrace_append hprefix tailTrace_6227440
  have hstable : (prefixWord ++ tailWord_6227440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227440).length < 2 ^ (prefixWord ++ tailWord_6227440).sum := by decide
  have hdescent : baseEnd_6227440 < baseStart_6227440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227449 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6227449 : Nat := 118140960795 + 6227449 * 2 ^ 59
def prefixEnd_6227449 : Nat := 4983230072969 + 3 ^ 40 * 6227449 * 2
def baseEnd_6227449 : Nat := 3197674588361110810847989

theorem tailTrace_6227449 : CollatzResearch.WordTrace tailWord_6227449 prefixEnd_6227449 3197674588361110810847989 := by
  unfold tailWord_6227449
  simp only [CollatzResearch.WordTrace]
  refine ⟨227133724816023311459685401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151422483210682207639790267 227133724816023311459685401)
  ·
    refine ⟨170350293612017483594764051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227133724816023311459685401 170350293612017483594764051)
    ·
      refine ⟨255525440418026225392146077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170350293612017483594764051 255525440418026225392146077)
      ·
        refine ⟨95822040156759834522054779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255525440418026225392146077 95822040156759834522054779)
        ·
          refine ⟨143733060235139751783082169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95822040156759834522054779 143733060235139751783082169)
          ·
            refine ⟨107799795176354813837311627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143733060235139751783082169 107799795176354813837311627)
            ·
              refine ⟨161699692764532220755967441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107799795176354813837311627 161699692764532220755967441)
              ·
                refine ⟨121274769573399165566975581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161699692764532220755967441 121274769573399165566975581)
                ·
                  refine ⟨45478038590024687087615843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121274769573399165566975581 45478038590024687087615843)
                  ·
                    refine ⟨68217057885037030631423765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45478038590024687087615843 68217057885037030631423765)
                    ·
                      refine ⟨3197674588361110810847989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68217057885037030631423765 3197674588361110810847989)
                      ·
                        rfl

theorem cell23_6227449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6227449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227449 prefixEnd_6227449 := by exact prefixLift 6227449
  have htrace : WordTrace (prefixWord ++ tailWord_6227449) baseStart_6227449 baseEnd_6227449 := by
    simpa [prefixWord, tailWord_6227449, baseEnd_6227449] using wordTrace_append hprefix tailTrace_6227449
  have hstable : (prefixWord ++ tailWord_6227449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227449).length < 2 ^ (prefixWord ++ tailWord_6227449).sum := by decide
  have hdescent : baseEnd_6227449 < baseStart_6227449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227453 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_6227453 : Nat := 118140960795 + 6227453 * 2 ^ 59
def prefixEnd_6227453 : Nat := 4983230072969 + 3 ^ 40 * 6227453 * 2
def baseEnd_6227453 : Nat := 3197676642283728795197971

theorem tailTrace_6227453 : CollatzResearch.WordTrace tailWord_6227453 prefixEnd_6227453 3197676642283728795197971 := by
  unfold tailWord_6227453
  simp only [CollatzResearch.WordTrace]
  refine ⟨227133870708008820142831013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151422580472005880095220675 227133870708008820142831013)
  ·
    refine ⟨42587600757751653776780815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227133870708008820142831013 42587600757751653776780815)
    ·
      refine ⟨63881401136627480665171223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42587600757751653776780815 63881401136627480665171223)
      ·
        refine ⟨95822101704941220997756835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63881401136627480665171223 95822101704941220997756835)
        ·
          refine ⟨143733152557411831496635253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95822101704941220997756835 143733152557411831496635253)
          ·
            refine ⟨13474983052257359202809555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143733152557411831496635253 13474983052257359202809555)
            ·
              refine ⟨20212474578386038804214333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13474983052257359202809555 20212474578386038804214333)
              ·
                refine ⟨7579677966894764551580375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20212474578386038804214333 7579677966894764551580375)
                ·
                  refine ⟨11369516950342146827370563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7579677966894764551580375 11369516950342146827370563)
                  ·
                    refine ⟨17054275425513220241055845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11369516950342146827370563 17054275425513220241055845)
                    ·
                      refine ⟨3197676642283728795197971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17054275425513220241055845 3197676642283728795197971)
                      ·
                        rfl

theorem cell23_6227453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_6227453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227453 prefixEnd_6227453 := by exact prefixLift 6227453
  have htrace : WordTrace (prefixWord ++ tailWord_6227453) baseStart_6227453 baseEnd_6227453 := by
    simpa [prefixWord, tailWord_6227453, baseEnd_6227453] using wordTrace_append hprefix tailTrace_6227453
  have hstable : (prefixWord ++ tailWord_6227453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227453).length < 2 ^ (prefixWord ++ tailWord_6227453).sum := by decide
  have hdescent : baseEnd_6227453 < baseStart_6227453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227463 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 4, 4]
def baseStart_6227463 : Nat := 118140960795 + 6227463 * 2 ^ 59
def prefixEnd_6227463 : Nat := 4983230072969 + 3 ^ 40 * 6227463 * 2
def baseEnd_6227463 : Nat := 1065893925696757918690975

theorem tailTrace_6227463 : CollatzResearch.WordTrace tailWord_6227463 prefixEnd_6227463 1065893925696757918690975 := by
  unfold tailWord_6227463
  simp only [CollatzResearch.WordTrace]
  refine ⟨227134235437972591850695043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151422823625315061233796695 227134235437972591850695043)
  ·
    refine ⟨340701353156958887776042565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227134235437972591850695043 340701353156958887776042565)
    ·
      refine ⟨63881503716929791458007981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340701353156958887776042565 63881503716929791458007981)
      ·
        refine ⟨23955563893848671796752993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63881503716929791458007981 23955563893848671796752993)
        ·
          refine ⟨17966672920386503847564745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23955563893848671796752993 17966672920386503847564745)
          ·
            refine ⟨13475004690289877885673559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17966672920386503847564745 13475004690289877885673559)
            ·
              refine ⟨20212507035434816828510339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13475004690289877885673559 20212507035434816828510339)
              ·
                refine ⟨30318760553152225242765509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20212507035434816828510339 30318760553152225242765509)
                ·
                  refine ⟨5684767603716042233018533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30318760553152225242765509 5684767603716042233018533)
                  ·
                    refine ⟨1065893925696757918690975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5684767603716042233018533 1065893925696757918690975)
                    ·
                      rfl

theorem cell23_6227463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_6227463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227463 prefixEnd_6227463 := by exact prefixLift 6227463
  have htrace : WordTrace (prefixWord ++ tailWord_6227463) baseStart_6227463 baseEnd_6227463 := by
    simpa [prefixWord, tailWord_6227463, baseEnd_6227463] using wordTrace_append hprefix tailTrace_6227463
  have hstable : (prefixWord ++ tailWord_6227463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227463).length < 2 ^ (prefixWord ++ tailWord_6227463).sum := by decide
  have hdescent : baseEnd_6227463 < baseStart_6227463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227480 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 1, 6]
def baseStart_6227480 : Nat := 118140960795 + 6227480 * 2 ^ 59
def prefixEnd_6227480 : Nat := 4983230072969 + 3 ^ 40 * 6227480 * 2
def baseEnd_6227480 : Nat := 1065896835420466729853449

theorem tailTrace_6227480 : CollatzResearch.WordTrace tailWord_6227480 prefixEnd_6227480 1065896835420466729853449 := by
  unfold tailWord_6227480
  simp only [CollatzResearch.WordTrace]
  refine ⟨113567427739455501877031947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151423236985940669169375929 113567427739455501877031947)
  ·
    refine ⟨170351141609183252815547921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113567427739455501877031947 170351141609183252815547921)
    ·
      refine ⟨127763356206887439611660941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170351141609183252815547921 127763356206887439611660941)
      ·
        refine ⟨47911258577582789854372853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127763356206887439611660941 47911258577582789854372853)
        ·
          refine ⟨4491680491648386548847455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47911258577582789854372853 4491680491648386548847455)
          ·
            refine ⟨6737520737472579823271183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491680491648386548847455 6737520737472579823271183)
            ·
              refine ⟨10106281106208869734906775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737520737472579823271183 10106281106208869734906775)
              ·
                refine ⟨15159421659313304602360163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10106281106208869734906775 15159421659313304602360163)
                ·
                  refine ⟨22739132488969956903540245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15159421659313304602360163 22739132488969956903540245)
                  ·
                    refine ⟨1065896835420466729853449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22739132488969956903540245 1065896835420466729853449)
                    ·
                      rfl

theorem cell23_6227480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_6227480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227480 prefixEnd_6227480 := by exact prefixLift 6227480
  have htrace : WordTrace (prefixWord ++ tailWord_6227480) baseStart_6227480 baseEnd_6227480 := by
    simpa [prefixWord, tailWord_6227480, baseEnd_6227480] using wordTrace_append hprefix tailTrace_6227480
  have hstable : (prefixWord ++ tailWord_6227480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227480).length < 2 ^ (prefixWord ++ tailWord_6227480).sum := by decide
  have hdescent : baseEnd_6227480 < baseStart_6227480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227510 : List Nat := [5, 1, 2, 1, 4, 1, 9]
def baseStart_6227510 : Nat := 118140960795 + 6227510 * 2 ^ 59
def prefixEnd_6227510 : Nat := 4983230072969 + 3 ^ 40 * 6227510 * 2
def baseEnd_6227510 : Nat := 39477850749148581138089

theorem tailTrace_6227510 : CollatzResearch.WordTrace tailWord_6227510 prefixEnd_6227510 39477850749148581138089 := by
  unfold tailWord_6227510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14195996854300144929853499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151423966445868212585103989 14195996854300144929853499)
  ·
    refine ⟨21293995281450217394780249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14195996854300144929853499 21293995281450217394780249)
    ·
      refine ⟨15970496461087663046085187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21293995281450217394780249 15970496461087663046085187)
      ·
        refine ⟨23955744691631494569127781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15970496461087663046085187 23955744691631494569127781)
        ·
          refine ⟨4491702129680905231711459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23955744691631494569127781 4491702129680905231711459)
          ·
            refine ⟨6737553194521357847567189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491702129680905231711459 6737553194521357847567189)
            ·
              refine ⟨39477850749148581138089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6737553194521357847567189 39477850749148581138089)
              ·
                rfl

theorem cell23_6227510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 9].length) (baseStart_6227510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227510 prefixEnd_6227510 := by exact prefixLift 6227510
  have htrace : WordTrace (prefixWord ++ tailWord_6227510) baseStart_6227510 baseEnd_6227510 := by
    simpa [prefixWord, tailWord_6227510, baseEnd_6227510] using wordTrace_append hprefix tailTrace_6227510
  have hstable : (prefixWord ++ tailWord_6227510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227510).length < 2 ^ (prefixWord ++ tailWord_6227510).sum := by decide
  have hdescent : baseEnd_6227510 < baseStart_6227510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227560 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6227560 : Nat := 118140960795 + 6227560 * 2 ^ 59
def prefixEnd_6227560 : Nat := 4983230072969 + 3 ^ 40 * 6227560 * 2
def baseEnd_6227560 : Nat := 3197731584713759876559979

theorem tailTrace_6227560 : CollatzResearch.WordTrace tailWord_6227560 prefixEnd_6227560 3197731584713759876559979 := by
  unfold tailWord_6227560
  simp only [CollatzResearch.WordTrace]
  refine ⟨113568886659310588708488067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151425182212414118277984089 113568886659310588708488067)
  ·
    refine ⟨170353329988965883062732101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113568886659310588708488067 170353329988965883062732101)
    ·
      refine ⟨31941249372931103074262269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170353329988965883062732101 31941249372931103074262269)
      ·
        refine ⟨11977968514849163652848351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31941249372931103074262269 11977968514849163652848351)
        ·
          refine ⟨17966952772273745479272527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11977968514849163652848351 17966952772273745479272527)
          ·
            refine ⟨26950429158410618218908791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17966952772273745479272527 26950429158410618218908791)
            ·
              refine ⟨40425643737615927328363187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26950429158410618218908791 40425643737615927328363187)
              ·
                refine ⟨60638465606423890992544781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40425643737615927328363187 60638465606423890992544781)
                ·
                  refine ⟨22739424602408959122204293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60638465606423890992544781 22739424602408959122204293)
                  ·
                    refine ⟨4263642112951679835413305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22739424602408959122204293 4263642112951679835413305)
                    ·
                      refine ⟨3197731584713759876559979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263642112951679835413305 3197731584713759876559979)
                      ·
                        rfl

theorem cell23_6227560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6227560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227560 prefixEnd_6227560 := by exact prefixLift 6227560
  have htrace : WordTrace (prefixWord ++ tailWord_6227560) baseStart_6227560 baseEnd_6227560 := by
    simpa [prefixWord, tailWord_6227560, baseEnd_6227560] using wordTrace_append hprefix tailTrace_6227560
  have hstable : (prefixWord ++ tailWord_6227560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227560).length < 2 ^ (prefixWord ++ tailWord_6227560).sum := by decide
  have hdescent : baseEnd_6227560 < baseStart_6227560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227577 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 2, 2, 2]
def baseStart_6227577 : Nat := 118140960795 + 6227577 * 2 ^ 59
def prefixEnd_6227577 : Nat := 4983230072969 + 3 ^ 40 * 6227577 * 2
def baseEnd_6227577 : Nat := 3197740313884886310047401

theorem tailTrace_6227577 : CollatzResearch.WordTrace tailWord_6227577 prefixEnd_6227577 3197740313884886310047401 := by
  unfold tailWord_6227577
  simp only [CollatzResearch.WordTrace]
  refine ⟨227138393359559589320344985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151425595573039726213563323 227138393359559589320344985)
  ·
    refine ⟨170353795019669691990258739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227138393359559589320344985 170353795019669691990258739)
    ·
      refine ⟨255530692529504537985388109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170353795019669691990258739 255530692529504537985388109)
      ·
        refine ⟨95824009698564201744520541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255530692529504537985388109 95824009698564201744520541)
        ·
          refine ⟨35934003636961575654195203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95824009698564201744520541 35934003636961575654195203)
          ·
            refine ⟨53901005455442363481292805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35934003636961575654195203 53901005455442363481292805)
            ·
              refine ⟨10106438522895443152742401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53901005455442363481292805 10106438522895443152742401)
              ·
                refine ⟨7579828892171582364556801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10106438522895443152742401 7579828892171582364556801)
                ·
                  refine ⟨5684871669128686773417601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7579828892171582364556801 5684871669128686773417601)
                  ·
                    refine ⟨4263653751846515080063201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5684871669128686773417601 4263653751846515080063201)
                    ·
                      refine ⟨3197740313884886310047401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263653751846515080063201 3197740313884886310047401)
                      ·
                        rfl

theorem cell23_6227577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_6227577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227577 prefixEnd_6227577 := by exact prefixLift 6227577
  have htrace : WordTrace (prefixWord ++ tailWord_6227577) baseStart_6227577 baseEnd_6227577 := by
    simpa [prefixWord, tailWord_6227577, baseEnd_6227577] using wordTrace_append hprefix tailTrace_6227577
  have hstable : (prefixWord ++ tailWord_6227577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227577).length < 2 ^ (prefixWord ++ tailWord_6227577).sum := by decide
  have hdescent : baseEnd_6227577 < baseStart_6227577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227596 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_6227596 : Nat := 118140960795 + 6227596 * 2 ^ 59
def prefixEnd_6227596 : Nat := 4983230072969 + 3 ^ 40 * 6227596 * 2
def baseEnd_6227596 : Nat := 1065916690005773911903271

theorem tailTrace_6227596 : CollatzResearch.WordTrace tailWord_6227596 prefixEnd_6227596 1065916690005773911903271 := by
  unfold tailWord_6227596
  simp only [CollatzResearch.WordTrace]
  refine ⟨113569543173245377782643321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151426057564327170376857761 113569543173245377782643321)
  ·
    refine ⟨85177157379934033336982491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113569543173245377782643321 85177157379934033336982491)
    ·
      refine ⟨127765736069901050005473737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85177157379934033336982491 127765736069901050005473737)
      ·
        refine ⟨95824302052425787504105303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127765736069901050005473737 95824302052425787504105303)
        ·
          refine ⟨143736453078638681256157955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95824302052425787504105303 143736453078638681256157955)
          ·
            refine ⟨215604679617958021884236933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143736453078638681256157955 215604679617958021884236933)
            ·
              refine ⟨40425877428367129103294425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215604679617958021884236933 40425877428367129103294425)
              ·
                refine ⟨30319408071275346827470819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40425877428367129103294425 30319408071275346827470819)
                ·
                  refine ⟨45479112106913020241206229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30319408071275346827470819 45479112106913020241206229)
                  ·
                    refine ⟨1065916690005773911903271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45479112106913020241206229 1065916690005773911903271)
                    ·
                      rfl

theorem cell23_6227596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_6227596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227596 prefixEnd_6227596 := by exact prefixLift 6227596
  have htrace : WordTrace (prefixWord ++ tailWord_6227596) baseStart_6227596 baseEnd_6227596 := by
    simpa [prefixWord, tailWord_6227596, baseEnd_6227596] using wordTrace_append hprefix tailTrace_6227596
  have hstable : (prefixWord ++ tailWord_6227596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227596).length < 2 ^ (prefixWord ++ tailWord_6227596).sum := by decide
  have hdescent : baseEnd_6227596 < baseStart_6227596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227653 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_6227653 : Nat := 118140960795 + 6227653 * 2 ^ 59
def prefixEnd_6227653 : Nat := 4983230072969 + 3 ^ 40 * 6227653 * 2
def baseEnd_6227653 : Nat := 3197779338414628012697051

theorem tailTrace_6227653 : CollatzResearch.WordTrace tailWord_6227653 prefixEnd_6227653 3197779338414628012697051 := by
  unfold tailWord_6227653
  simp only [CollatzResearch.WordTrace]
  refine ⟨227141165307284254300111613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151427443538189502866741075 227141165307284254300111613)
  ·
    refine ⟨85177936990231595362541855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227141165307284254300111613 85177936990231595362541855)
    ·
      refine ⟨127766905485347393043812783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85177936990231595362541855 127766905485347393043812783)
      ·
        refine ⟨191650358228021089565719175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127766905485347393043812783 191650358228021089565719175)
        ·
          refine ⟨287475537342031634348578763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191650358228021089565719175 287475537342031634348578763)
          ·
            refine ⟨431213306013047451522868145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287475537342031634348578763 431213306013047451522868145)
            ·
              refine ⟨323409979509785588642151109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431213306013047451522868145 323409979509785588642151109)
              ·
                refine ⟨60639371158084797870403333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323409979509785588642151109 60639371158084797870403333)
                ·
                  refine ⟨11369882092140899600700625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60639371158084797870403333 11369882092140899600700625)
                  ·
                    refine ⟨8527411569105674700525469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11369882092140899600700625 8527411569105674700525469)
                    ·
                      refine ⟨3197779338414628012697051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527411569105674700525469 3197779338414628012697051)
                      ·
                        rfl

theorem cell23_6227653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_6227653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227653 prefixEnd_6227653 := by exact prefixLift 6227653
  have htrace : WordTrace (prefixWord ++ tailWord_6227653) baseStart_6227653 baseEnd_6227653 := by
    simpa [prefixWord, tailWord_6227653, baseEnd_6227653] using wordTrace_append hprefix tailTrace_6227653
  have hstable : (prefixWord ++ tailWord_6227653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227653).length < 2 ^ (prefixWord ++ tailWord_6227653).sum := by decide
  have hdescent : baseEnd_6227653 < baseStart_6227653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227694 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_6227694 : Nat := 118140960795 + 6227694 * 2 ^ 59
def prefixEnd_6227694 : Nat := 4983230072969 + 3 ^ 40 * 6227694 * 2
def baseEnd_6227694 : Nat := 1065933463707154117428121

theorem tailTrace_6227694 : CollatzResearch.WordTrace tailWord_6227694 prefixEnd_6227694 1065933463707154117428121 := by
  unfold tailWord_6227694
  simp only [CollatzResearch.WordTrace]
  refine ⟨28392832587516964787794267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151428440466757145534902757 28392832587516964787794267)
  ·
    refine ⟨42589248881275447181691401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28392832587516964787794267 42589248881275447181691401)
    ·
      refine ⟨31941936660956585386268551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42589248881275447181691401 31941936660956585386268551)
      ·
        refine ⟨47912904991434878079402827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31941936660956585386268551 47912904991434878079402827)
        ·
          refine ⟨71869357487152317119104241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47912904991434878079402827 71869357487152317119104241)
          ·
            refine ⟨53902018115364237839328181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71869357487152317119104241 53902018115364237839328181)
            ·
              refine ⟨5053314198315397297437017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53902018115364237839328181 5053314198315397297437017)
              ·
                refine ⟨3789985648736547973077763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053314198315397297437017 3789985648736547973077763)
                ·
                  refine ⟨5684978473104821959616645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789985648736547973077763 5684978473104821959616645)
                  ·
                    refine ⟨1065933463707154117428121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5684978473104821959616645 1065933463707154117428121)
                    ·
                      rfl

theorem cell23_6227694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_6227694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227694 prefixEnd_6227694 := by exact prefixLift 6227694
  have htrace : WordTrace (prefixWord ++ tailWord_6227694) baseStart_6227694 baseEnd_6227694 := by
    simpa [prefixWord, tailWord_6227694, baseEnd_6227694] using wordTrace_append hprefix tailTrace_6227694
  have hstable : (prefixWord ++ tailWord_6227694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227694).length < 2 ^ (prefixWord ++ tailWord_6227694).sum := by decide
  have hdescent : baseEnd_6227694 < baseStart_6227694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227733 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_6227733 : Nat := 118140960795 + 6227733 * 2 ^ 59
def prefixEnd_6227733 : Nat := 4983230072969 + 3 ^ 40 * 6227733 * 2
def baseEnd_6227733 : Nat := 1065940138955662566565561

theorem tailTrace_6227733 : CollatzResearch.WordTrace tailWord_6227733 prefixEnd_6227733 1065940138955662566565561 := by
  unfold tailWord_6227733
  simp only [CollatzResearch.WordTrace]
  refine ⟨227144083146994427963023853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151429388764662951975349235 227144083146994427963023853)
  ·
    refine ⟨85179031180122910486133945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227144083146994427963023853 85179031180122910486133945)
    ·
      refine ⟨63884273385092182864600459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85179031180122910486133945 63884273385092182864600459)
      ·
        refine ⟨95826410077638274296900689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63884273385092182864600459 95826410077638274296900689)
        ·
          refine ⟨71869807558228705722675517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95826410077638274296900689 71869807558228705722675517)
          ·
            refine ⟨26951177834335764646003319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71869807558228705722675517 26951177834335764646003319)
            ·
              refine ⟨40426766751503646969004979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26951177834335764646003319 40426766751503646969004979)
              ·
                refine ⟨60640150127255470453507469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40426766751503646969004979 60640150127255470453507469)
                ·
                  refine ⟨22740056297720801420065301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60640150127255470453507469 22740056297720801420065301)
                  ·
                    refine ⟨1065940138955662566565561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22740056297720801420065301 1065940138955662566565561)
                    ·
                      rfl

theorem cell23_6227733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_6227733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227733 prefixEnd_6227733 := by exact prefixLift 6227733
  have htrace : WordTrace (prefixWord ++ tailWord_6227733) baseStart_6227733 baseEnd_6227733 := by
    simpa [prefixWord, tailWord_6227733, baseEnd_6227733] using wordTrace_append hprefix tailTrace_6227733
  have hstable : (prefixWord ++ tailWord_6227733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227733).length < 2 ^ (prefixWord ++ tailWord_6227733).sum := by decide
  have hdescent : baseEnd_6227733 < baseStart_6227733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227770 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_6227770 : Nat := 118140960795 + 6227770 * 2 ^ 59
def prefixEnd_6227770 : Nat := 4983230072969 + 3 ^ 40 * 6227770 * 2
def baseEnd_6227770 : Nat := 3197839415651204054934013

theorem tailTrace_6227770 : CollatzResearch.WordTrace tailWord_6227770 prefixEnd_6227770 3197839415651204054934013 := by
  unfold tailWord_6227770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56786358161965095820530191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151430288431906922188080509 56786358161965095820530191)
  ·
    refine ⟨85179537242947643730795287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56786358161965095820530191 85179537242947643730795287)
    ·
      refine ⟨127769305864421465596192931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85179537242947643730795287 127769305864421465596192931)
      ·
        refine ⟨191653958796632198394289397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127769305864421465596192931 191653958796632198394289397)
        ·
          refine ⟨17967558637184268599464631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191653958796632198394289397 17967558637184268599464631)
          ·
            refine ⟨26951337955776402899196947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17967558637184268599464631 26951337955776402899196947)
            ·
              refine ⟨40427006933664604348795421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26951337955776402899196947 40427006933664604348795421)
              ·
                refine ⟨15160127600124226630798283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40427006933664604348795421 15160127600124226630798283)
                ·
                  refine ⟨22740191400186339946197425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15160127600124226630798283 22740191400186339946197425)
                  ·
                    refine ⟨17055143550139754959648069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22740191400186339946197425 17055143550139754959648069)
                    ·
                      refine ⟨3197839415651204054934013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17055143550139754959648069 3197839415651204054934013)
                      ·
                        rfl

theorem cell23_6227770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_6227770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227770 prefixEnd_6227770 := by exact prefixLift 6227770
  have htrace : WordTrace (prefixWord ++ tailWord_6227770) baseStart_6227770 baseEnd_6227770 := by
    simpa [prefixWord, tailWord_6227770, baseEnd_6227770] using wordTrace_append hprefix tailTrace_6227770
  have hstable : (prefixWord ++ tailWord_6227770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227770).length < 2 ^ (prefixWord ++ tailWord_6227770).sum := by decide
  have hdescent : baseEnd_6227770 < baseStart_6227770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227774 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_6227774 : Nat := 118140960795 + 6227774 * 2 ^ 59
def prefixEnd_6227774 : Nat := 4983230072969 + 3 ^ 40 * 6227774 * 2
def baseEnd_6227774 : Nat := 3197841469573822039283995

theorem tailTrace_6227774 : CollatzResearch.WordTrace tailWord_6227774 prefixEnd_6227774 3197841469573822039283995 := by
  unfold tailWord_6227774
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393197317480736495658297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151430385693230594643510917 28393197317480736495658297)
  ·
    refine ⟨21294897988110552371743723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28393197317480736495658297 21294897988110552371743723)
    ·
      refine ⟨31942346982165828557615585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21294897988110552371743723 31942346982165828557615585)
      ·
        refine ⟨23956760236624371418211689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31942346982165828557615585 23956760236624371418211689)
        ·
          refine ⟨17967570177468278563658767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23956760236624371418211689 17967570177468278563658767)
          ·
            refine ⟨26951355266202417845488151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17967570177468278563658767 26951355266202417845488151)
            ·
              refine ⟨40427032899303626768232227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26951355266202417845488151 40427032899303626768232227)
              ·
                refine ⟨60640549348955440152348341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40427032899303626768232227 60640549348955440152348341)
                ·
                  refine ⟨5685051501464572514282657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60640549348955440152348341 5685051501464572514282657)
                  ·
                    refine ⟨4263788626098429385711993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5685051501464572514282657 4263788626098429385711993)
                    ·
                      refine ⟨3197841469573822039283995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263788626098429385711993 3197841469573822039283995)
                      ·
                        rfl

theorem cell23_6227774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_6227774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227774 prefixEnd_6227774 := by exact prefixLift 6227774
  have htrace : WordTrace (prefixWord ++ tailWord_6227774) baseStart_6227774 baseEnd_6227774 := by
    simpa [prefixWord, tailWord_6227774, baseEnd_6227774] using wordTrace_append hprefix tailTrace_6227774
  have hstable : (prefixWord ++ tailWord_6227774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227774).length < 2 ^ (prefixWord ++ tailWord_6227774).sum := by decide
  have hdescent : baseEnd_6227774 < baseStart_6227774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227794 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_6227794 : Nat := 118140960795 + 6227794 * 2 ^ 59
def prefixEnd_6227794 : Nat := 4983230072969 + 3 ^ 40 * 6227794 * 2
def baseEnd_6227794 : Nat := 3197851739186911961033903

theorem tailTrace_6227794 : CollatzResearch.WordTrace tailWord_6227794 prefixEnd_6227794 3197851739186911961033903 := by
  unfold tailWord_6227794
  simp only [CollatzResearch.WordTrace]
  refine ⟨56786576999943358845248609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151430871999848956920662957 56786576999943358845248609)
  ·
    refine ⟨42589932749957519133936457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56786576999943358845248609 42589932749957519133936457)
    ·
      refine ⟨31942449562468139350452343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42589932749957519133936457 31942449562468139350452343)
      ·
        refine ⟨47913674343702209025678515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31942449562468139350452343 47913674343702209025678515)
        ·
          refine ⟨71870511515553313538517773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47913674343702209025678515 71870511515553313538517773)
          ·
            refine ⟨26951441818332492576944165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71870511515553313538517773 26951441818332492576944165)
            ·
              refine ⟨5053395340937342358177031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26951441818332492576944165 5053395340937342358177031)
              ·
                refine ⟨7580093011406013537265547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053395340937342358177031 7580093011406013537265547)
                ·
                  refine ⟨11370139517109020305898321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7580093011406013537265547 11370139517109020305898321)
                  ·
                    refine ⟨8527604637831765229423741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11370139517109020305898321 8527604637831765229423741)
                    ·
                      refine ⟨3197851739186911961033903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527604637831765229423741 3197851739186911961033903)
                      ·
                        rfl

theorem cell23_6227794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_6227794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227794 prefixEnd_6227794 := by exact prefixLift 6227794
  have htrace : WordTrace (prefixWord ++ tailWord_6227794) baseStart_6227794 baseEnd_6227794 := by
    simpa [prefixWord, tailWord_6227794, baseEnd_6227794] using wordTrace_append hprefix tailTrace_6227794
  have hstable : (prefixWord ++ tailWord_6227794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227794).length < 2 ^ (prefixWord ++ tailWord_6227794).sum := by decide
  have hdescent : baseEnd_6227794 < baseStart_6227794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227807 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 3]
def baseStart_6227807 : Nat := 118140960795 + 6227807 * 2 ^ 59
def prefixEnd_6227807 : Nat := 4983230072969 + 3 ^ 40 * 6227807 * 2
def baseEnd_6227807 : Nat := 3197858414435420410171343

theorem tailTrace_6227807 : CollatzResearch.WordTrace tailWord_6227807 prefixEnd_6227807 3197858414435420410171343 := by
  unfold tailWord_6227807
  simp only [CollatzResearch.WordTrace]
  refine ⟨227146782148726338601217675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151431188099150892400811783 227146782148726338601217675)
  ·
    refine ⟨340720173223089507901826513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227146782148726338601217675 340720173223089507901826513)
    ·
      refine ⟨255540129917317130926369885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340720173223089507901826513 255540129917317130926369885)
      ·
        refine ⟨95827548718993924097388707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255540129917317130926369885 95827548718993924097388707)
        ·
          refine ⟨143741323078490886146083061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95827548718993924097388707 143741323078490886146083061)
          ·
            refine ⟨13475749038608520576195287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143741323078490886146083061 13475749038608520576195287)
            ·
              refine ⟨20213623557912780864292931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13475749038608520576195287 20213623557912780864292931)
              ·
                refine ⟨30320435336869171296439397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20213623557912780864292931 30320435336869171296439397)
                ·
                  refine ⟨5685081625662969618082387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30320435336869171296439397 5685081625662969618082387)
                  ·
                    refine ⟨8527622438494454427123581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5685081625662969618082387 8527622438494454427123581)
                    ·
                      refine ⟨3197858414435420410171343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527622438494454427123581 3197858414435420410171343)
                      ·
                        rfl

theorem cell23_6227807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_6227807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227807 prefixEnd_6227807 := by exact prefixLift 6227807
  have htrace : WordTrace (prefixWord ++ tailWord_6227807) baseStart_6227807 baseEnd_6227807 := by
    simpa [prefixWord, tailWord_6227807, baseEnd_6227807] using wordTrace_append hprefix tailTrace_6227807
  have hstable : (prefixWord ++ tailWord_6227807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227807).length < 2 ^ (prefixWord ++ tailWord_6227807).sum := by decide
  have hdescent : baseEnd_6227807 < baseStart_6227807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227937 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_6227937 : Nat := 118140960795 + 6227937 * 2 ^ 59
def prefixEnd_6227937 : Nat := 4983230072969 + 3 ^ 40 * 6227937 * 2
def baseEnd_6227937 : Nat := 3197925166920504901545745

theorem tailTrace_6227937 : CollatzResearch.WordTrace tailWord_6227937 prefixEnd_6227937 3197925166920504901545745 := by
  unfold tailWord_6227937
  simp only [CollatzResearch.WordTrace]
  refine ⟨227151523638255370803450065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151434349092170247202300043 227151523638255370803450065)
  ·
    refine ⟨170363642728691528102587549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227151523638255370803450065 170363642728691528102587549)
    ·
      refine ⟨63886366023259323038470331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170363642728691528102587549 63886366023259323038470331)
      ·
        refine ⟨95829549034888984557705497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63886366023259323038470331 95829549034888984557705497)
        ·
          refine ⟨71872161776166738418279123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95829549034888984557705497 71872161776166738418279123)
          ·
            refine ⟨107808242664250107627418685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71872161776166738418279123 107808242664250107627418685)
            ·
              refine ⟨40428090999093790360282007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107808242664250107627418685 40428090999093790360282007)
              ·
                refine ⟨60642136498640685540423011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40428090999093790360282007 60642136498640685540423011)
                ·
                  refine ⟨90963204747961028310634517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60642136498640685540423011 90963204747961028310634517)
                  ·
                    refine ⟨4263900222560673202060993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90963204747961028310634517 4263900222560673202060993)
                    ·
                      refine ⟨3197925166920504901545745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263900222560673202060993 3197925166920504901545745)
                      ·
                        rfl

theorem cell23_6227937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_6227937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227937 prefixEnd_6227937 := by exact prefixLift 6227937
  have htrace : WordTrace (prefixWord ++ tailWord_6227937) baseStart_6227937 baseEnd_6227937 := by
    simpa [prefixWord, tailWord_6227937, baseEnd_6227937] using wordTrace_append hprefix tailTrace_6227937
  have hstable : (prefixWord ++ tailWord_6227937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227937).length < 2 ^ (prefixWord ++ tailWord_6227937).sum := by decide
  have hdescent : baseEnd_6227937 < baseStart_6227937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227980 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6227980 : Nat := 118140960795 + 6227980 * 2 ^ 59
def prefixEnd_6227980 : Nat := 4983230072969 + 3 ^ 40 * 6227980 * 2
def baseEnd_6227980 : Nat := 3197947246588648233308047

theorem tailTrace_6227980 : CollatzResearch.WordTrace tailWord_6227980 prefixEnd_6227980 3197947246588648233308047 := by
  unfold tailWord_6227980
  simp only [CollatzResearch.WordTrace]
  refine ⟨113576545988549794573632697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151435394651399726098176929 113576545988549794573632697)
  ·
    refine ⟨85182409491412345930224523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113576545988549794573632697 85182409491412345930224523)
    ·
      refine ⟨127773614237118518895336785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85182409491412345930224523 127773614237118518895336785)
      ·
        refine ⟨95830210677838889171502589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127773614237118518895336785 95830210677838889171502589)
        ·
          refine ⟨35936329004189583439313471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95830210677838889171502589 35936329004189583439313471)
          ·
            refine ⟨53904493506284375158970207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35936329004189583439313471 53904493506284375158970207)
            ·
              refine ⟨80856740259426562738455311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53904493506284375158970207 80856740259426562738455311)
              ·
                refine ⟨121285110389139844107682967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80856740259426562738455311 121285110389139844107682967)
                ·
                  refine ⟨181927665583709766161524451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121285110389139844107682967 181927665583709766161524451)
                  ·
                    refine ⟨272891498375564649242286677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181927665583709766161524451 272891498375564649242286677)
                    ·
                      refine ⟨3197947246588648233308047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 272891498375564649242286677 3197947246588648233308047)
                      ·
                        rfl

theorem cell23_6227980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6227980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227980 prefixEnd_6227980 := by exact prefixLift 6227980
  have htrace : WordTrace (prefixWord ++ tailWord_6227980) baseStart_6227980 baseEnd_6227980 := by
    simpa [prefixWord, tailWord_6227980, baseEnd_6227980] using wordTrace_append hprefix tailTrace_6227980
  have hstable : (prefixWord ++ tailWord_6227980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227980).length < 2 ^ (prefixWord ++ tailWord_6227980).sum := by decide
  have hdescent : baseEnd_6227980 < baseStart_6227980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6227994 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_6227994 : Nat := 118140960795 + 6227994 * 2 ^ 59
def prefixEnd_6227994 : Nat := 4983230072969 + 3 ^ 40 * 6227994 * 2
def baseEnd_6227994 : Nat := 355328270590867908725887

theorem tailTrace_6227994 : CollatzResearch.WordTrace tailWord_6227994 prefixEnd_6227994 355328270590867908725887 := by
  unfold tailWord_6227994
  simp only [CollatzResearch.WordTrace]
  refine ⟨56788400649762217384568759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151435735066032579692183357 56788400649762217384568759)
  ·
    refine ⟨85182600974643326076853139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56788400649762217384568759 85182600974643326076853139)
    ·
      refine ⟨127773901461964989115279709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85182600974643326076853139 127773901461964989115279709)
      ·
        refine ⟨47915213048236870918229891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127773901461964989115279709 47915213048236870918229891)
        ·
          refine ⟨71872819572355306377344837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47915213048236870918229891 71872819572355306377344837)
          ·
            refine ⟨13476153669816619945752157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71872819572355306377344837 13476153669816619945752157)
            ·
              refine ⟨5053557626181232479657059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13476153669816619945752157 5053557626181232479657059)
              ·
                refine ⟨7580336439271848719485589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053557626181232479657059 7580336439271848719485589)
                ·
                  refine ⟨355328270590867908725887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7580336439271848719485589 355328270590867908725887)
                  ·
                    rfl

theorem cell23_6227994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_6227994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6227994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6227994 prefixEnd_6227994 := by exact prefixLift 6227994
  have htrace : WordTrace (prefixWord ++ tailWord_6227994) baseStart_6227994 baseEnd_6227994 := by
    simpa [prefixWord, tailWord_6227994, baseEnd_6227994] using wordTrace_append hprefix tailTrace_6227994
  have hstable : (prefixWord ++ tailWord_6227994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6227994).length < 2 ^ (prefixWord ++ tailWord_6227994).sum := by decide
  have hdescent : baseEnd_6227994 < baseStart_6227994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6227994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228027 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 8, 2]
def baseStart_6228027 : Nat := 118140960795 + 6228027 * 2 ^ 59
def prefixEnd_6228027 : Nat := 4983230072969 + 3 ^ 40 * 6228027 * 2
def baseEnd_6228027 : Nat := 3197971380179409549420331

theorem tailTrace_6228027 : CollatzResearch.WordTrace tailWord_6228027 prefixEnd_6228027 3197971380179409549420331 := by
  unfold tailWord_6228027
  simp only [CollatzResearch.WordTrace]
  refine ⟨227154806207929316174226335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151436537471952877449484223 227154806207929316174226335)
  ·
    refine ⟨340732209311893974261339503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227154806207929316174226335 340732209311893974261339503)
    ·
      refine ⟨511098313967840961392009255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340732209311893974261339503 511098313967840961392009255)
      ·
        refine ⟨766647470951761442088013883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511098313967840961392009255 766647470951761442088013883)
        ·
          refine ⟨1149971206427642163132020825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766647470951761442088013883 1149971206427642163132020825)
          ·
            refine ⟨862478404820731622349015619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149971206427642163132020825 862478404820731622349015619)
            ·
              refine ⟨1293717607231097433523523429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862478404820731622349015619 1293717607231097433523523429)
              ·
                refine ⟨242572051355830768785660643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1293717607231097433523523429 242572051355830768785660643)
                ·
                  refine ⟨363858077033746153178490965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242572051355830768785660643 363858077033746153178490965)
                  ·
                    refine ⟨4263961840239212732560441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 363858077033746153178490965 4263961840239212732560441)
                    ·
                      refine ⟨3197971380179409549420331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4263961840239212732560441 3197971380179409549420331)
                      ·
                        rfl

theorem cell23_6228027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8, 2].length) (baseStart_6228027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228027 prefixEnd_6228027 := by exact prefixLift 6228027
  have htrace : WordTrace (prefixWord ++ tailWord_6228027) baseStart_6228027 baseEnd_6228027 := by
    simpa [prefixWord, tailWord_6228027, baseEnd_6228027] using wordTrace_append hprefix tailTrace_6228027
  have hstable : (prefixWord ++ tailWord_6228027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228027).length < 2 ^ (prefixWord ++ tailWord_6228027).sum := by decide
  have hdescent : baseEnd_6228027 < baseStart_6228027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228047 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_6228047 : Nat := 118140960795 + 6228047 * 2 ^ 59
def prefixEnd_6228047 : Nat := 4983230072969 + 3 ^ 40 * 6228047 * 2
def baseEnd_6228047 : Nat := 3197981649792499471170239

theorem tailTrace_6228047 : CollatzResearch.WordTrace tailWord_6228047 prefixEnd_6228047 3197981649792499471170239 := by
  unfold tailWord_6228047
  simp only [CollatzResearch.WordTrace]
  refine ⟨227155535667856859589954395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151437023778571239726636263 227155535667856859589954395)
  ·
    refine ⟨340733303501785289384931593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227155535667856859589954395 340733303501785289384931593)
    ·
      refine ⟨255549977626338967038698695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340733303501785289384931593 255549977626338967038698695)
      ·
        refine ⟨383324966439508450558048043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255549977626338967038698695 383324966439508450558048043)
        ·
          refine ⟨574987449659262675837072065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383324966439508450558048043 574987449659262675837072065)
          ·
            refine ⟨431240587244447006877804049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574987449659262675837072065 431240587244447006877804049)
            ·
              refine ⟨323430440433335255158353037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431240587244447006877804049 323430440433335255158353037)
              ·
                refine ⟨121286415162500720684382389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323430440433335255158353037 121286415162500720684382389)
                ·
                  refine ⟨11370601421484442564160849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121286415162500720684382389 11370601421484442564160849)
                  ·
                    refine ⟨8527951066113331923120637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11370601421484442564160849 8527951066113331923120637)
                    ·
                      refine ⟨3197981649792499471170239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527951066113331923120637 3197981649792499471170239)
                      ·
                        rfl

theorem cell23_6228047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_6228047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228047 prefixEnd_6228047 := by exact prefixLift 6228047
  have htrace : WordTrace (prefixWord ++ tailWord_6228047) baseStart_6228047 baseEnd_6228047 := by
    simpa [prefixWord, tailWord_6228047, baseEnd_6228047] using wordTrace_append hprefix tailTrace_6228047
  have hstable : (prefixWord ++ tailWord_6228047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228047).length < 2 ^ (prefixWord ++ tailWord_6228047).sum := by decide
  have hdescent : baseEnd_6228047 < baseStart_6228047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228057 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_6228057 : Nat := 118140960795 + 6228057 * 2 ^ 59
def prefixEnd_6228057 : Nat := 4983230072969 + 3 ^ 40 * 6228057 * 2
def baseEnd_6228057 : Nat := 3197986784599044432045193

theorem tailTrace_6228057 : CollatzResearch.WordTrace tailWord_6228057 prefixEnd_6228057 3197986784599044432045193 := by
  unfold tailWord_6228057
  simp only [CollatzResearch.WordTrace]
  refine ⟨227155900397820631297818425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151437266931880420865212283 227155900397820631297818425)
  ·
    refine ⟨170366925298365473473363819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227155900397820631297818425 170366925298365473473363819)
    ·
      refine ⟨255550387947548210210045729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170366925298365473473363819 255550387947548210210045729)
      ·
        refine ⟨191662790960661157657534297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255550387947548210210045729 191662790960661157657534297)
        ·
          refine ⟨143747093220495868243150723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191662790960661157657534297 143747093220495868243150723)
          ·
            refine ⟨215620639830743802364726085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143747093220495868243150723 215620639830743802364726085)
            ·
              refine ⟨40428869968264462943386141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215620639830743802364726085 40428869968264462943386141)
              ·
                refine ⟨15160826238099173603769803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40428869968264462943386141 15160826238099173603769803)
                ·
                  refine ⟨22741239357148760405654705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15160826238099173603769803 22741239357148760405654705)
                  ·
                    refine ⟨17055929517861570304241029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22741239357148760405654705 17055929517861570304241029)
                    ·
                      refine ⟨3197986784599044432045193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17055929517861570304241029 3197986784599044432045193)
                      ·
                        rfl

theorem cell23_6228057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_6228057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228057 prefixEnd_6228057 := by exact prefixLift 6228057
  have htrace : WordTrace (prefixWord ++ tailWord_6228057) baseStart_6228057 baseEnd_6228057 := by
    simpa [prefixWord, tailWord_6228057, baseEnd_6228057] using wordTrace_append hprefix tailTrace_6228057
  have hstable : (prefixWord ++ tailWord_6228057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228057).length < 2 ^ (prefixWord ++ tailWord_6228057).sum := by decide
  have hdescent : baseEnd_6228057 < baseStart_6228057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228061 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6228061 : Nat := 118140960795 + 6228061 * 2 ^ 59
def prefixEnd_6228061 : Nat := 4983230072969 + 3 ^ 40 * 6228061 * 2
def baseEnd_6228061 : Nat := 3197988838521662416395175

theorem tailTrace_6228061 : CollatzResearch.WordTrace tailWord_6228061 prefixEnd_6228061 3197988838521662416395175 := by
  unfold tailWord_6228061
  simp only [CollatzResearch.WordTrace]
  refine ⟨227156046289806139980964037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151437364193204093320642691 227156046289806139980964037)
  ·
    refine ⟨42591758679338651246430757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227156046289806139980964037 42591758679338651246430757)
    ·
      refine ⟨7985954752375997108705767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42591758679338651246430757 7985954752375997108705767)
      ·
        refine ⟨11978932128563995663058651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985954752375997108705767 11978932128563995663058651)
        ·
          refine ⟨17968398192845993494587977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11978932128563995663058651 17968398192845993494587977)
          ·
            refine ⟨13476298644634495120940983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17968398192845993494587977 13476298644634495120940983)
            ·
              refine ⟨20214447966951742681411475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476298644634495120940983 20214447966951742681411475)
              ·
                refine ⟨30321671950427614022117213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20214447966951742681411475 30321671950427614022117213)
                ·
                  refine ⟨11370626981410355258293955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30321671950427614022117213 11370626981410355258293955)
                  ·
                    refine ⟨17055940472115532887440933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11370626981410355258293955 17055940472115532887440933)
                    ·
                      refine ⟨3197988838521662416395175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17055940472115532887440933 3197988838521662416395175)
                      ·
                        rfl

theorem cell23_6228061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6228061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228061 prefixEnd_6228061 := by exact prefixLift 6228061
  have htrace : WordTrace (prefixWord ++ tailWord_6228061) baseStart_6228061 baseEnd_6228061 := by
    simpa [prefixWord, tailWord_6228061, baseEnd_6228061] using wordTrace_append hprefix tailTrace_6228061
  have hstable : (prefixWord ++ tailWord_6228061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228061).length < 2 ^ (prefixWord ++ tailWord_6228061).sum := by decide
  have hdescent : baseEnd_6228061 < baseStart_6228061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228064 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_6228064 : Nat := 118140960795 + 6228064 * 2 ^ 59
def prefixEnd_6228064 : Nat := 4983230072969 + 3 ^ 40 * 6228064 * 2
def baseEnd_6228064 : Nat := 3197990378963625904657661

theorem tailTrace_6228064 : CollatzResearch.WordTrace tailWord_6228064 prefixEnd_6228064 3197990378963625904657661 := by
  unfold tailWord_6228064
  simp only [CollatzResearch.WordTrace]
  refine ⟨113578077854397635746661623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151437437139196847662215497 113578077854397635746661623)
  ·
    refine ⟨170367116781596453619992435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113578077854397635746661623 170367116781596453619992435)
    ·
      refine ⟨255550675172394680429988653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170367116781596453619992435 255550675172394680429988653)
      ·
        refine ⟨95831503189648005161245745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255550675172394680429988653 95831503189648005161245745)
        ·
          refine ⟨71873627392236003870934309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95831503189648005161245745 71873627392236003870934309)
          ·
            refine ⟨13476305136044250725800183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71873627392236003870934309 13476305136044250725800183)
            ·
              refine ⟨20214457704066376088700275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476305136044250725800183 20214457704066376088700275)
              ·
                refine ⟨30321686556099564133050413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20214457704066376088700275 30321686556099564133050413)
                ·
                  refine ⟨11370632458537336549893905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30321686556099564133050413 11370632458537336549893905)
                  ·
                    refine ⟨8527974343903002412420429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11370632458537336549893905 8527974343903002412420429)
                    ·
                      refine ⟨3197990378963625904657661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527974343903002412420429 3197990378963625904657661)
                      ·
                        rfl

theorem cell23_6228064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_6228064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228064 prefixEnd_6228064 := by exact prefixLift 6228064
  have htrace : WordTrace (prefixWord ++ tailWord_6228064) baseStart_6228064 baseEnd_6228064 := by
    simpa [prefixWord, tailWord_6228064, baseEnd_6228064] using wordTrace_append hprefix tailTrace_6228064
  have hstable : (prefixWord ++ tailWord_6228064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228064).length < 2 ^ (prefixWord ++ tailWord_6228064).sum := by decide
  have hdescent : baseEnd_6228064 < baseStart_6228064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228081 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 1, 2, 3]
def baseStart_6228081 : Nat := 118140960795 + 6228081 * 2 ^ 59
def prefixEnd_6228081 : Nat := 4983230072969 + 3 ^ 40 * 6228081 * 2
def baseEnd_6228081 : Nat := 3197999108134752338145083

theorem tailTrace_6228081 : CollatzResearch.WordTrace tailWord_6228081 prefixEnd_6228081 3197999108134752338145083 := by
  unfold tailWord_6228081
  simp only [CollatzResearch.WordTrace]
  refine ⟨227156775749733683396692097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151437850499822455597794731 227156775749733683396692097)
  ·
    refine ⟨170367581812300262547519073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227156775749733683396692097 170367581812300262547519073)
    ·
      refine ⟨127775686359225196910639305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170367581812300262547519073 127775686359225196910639305)
      ·
        refine ⟨95831764769418897682979479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127775686359225196910639305 95831764769418897682979479)
        ·
          refine ⟨143747647154128346524469219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95831764769418897682979479 143747647154128346524469219)
          ·
            refine ⟨215621470731192519786703829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143747647154128346524469219 215621470731192519786703829)
            ·
              refine ⟨5053628220262324682500871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 215621470731192519786703829 5053628220262324682500871)
              ·
                refine ⟨7580442330393487023751307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053628220262324682500871 7580442330393487023751307)
                ·
                  refine ⟨11370663495590230535626961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7580442330393487023751307 11370663495590230535626961)
                  ·
                    refine ⟨8527997621692672901720221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11370663495590230535626961 8527997621692672901720221)
                    ·
                      refine ⟨3197999108134752338145083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8527997621692672901720221 3197999108134752338145083)
                      ·
                        rfl

theorem cell23_6228081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_6228081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228081 prefixEnd_6228081 := by exact prefixLift 6228081
  have htrace : WordTrace (prefixWord ++ tailWord_6228081) baseStart_6228081 baseEnd_6228081 := by
    simpa [prefixWord, tailWord_6228081, baseEnd_6228081] using wordTrace_append hprefix tailTrace_6228081
  have hstable : (prefixWord ++ tailWord_6228081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228081).length < 2 ^ (prefixWord ++ tailWord_6228081).sum := by decide
  have hdescent : baseEnd_6228081 < baseStart_6228081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228117 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_6228117 : Nat := 118140960795 + 6228117 * 2 ^ 59
def prefixEnd_6228117 : Nat := 4983230072969 + 3 ^ 40 * 6228117 * 2
def baseEnd_6228117 : Nat := 3198017593438314197294917

theorem tailTrace_6228117 : CollatzResearch.WordTrace tailWord_6228117 prefixEnd_6228117 3198017593438314197294917 := by
  unfold tailWord_6228117
  simp only [CollatzResearch.WordTrace]
  refine ⟨227158088777603261545002605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151438725851735507696668403 227158088777603261545002605)
  ·
    refine ⟨85184283291601223079375977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227158088777603261545002605 85184283291601223079375977)
    ·
      refine ⟨63888212468700917309531983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85184283291601223079375977 63888212468700917309531983)
      ·
        refine ⟨95832318703051375964297975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63888212468700917309531983 95832318703051375964297975)
        ·
          refine ⟨143748478054577063946446963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95832318703051375964297975 143748478054577063946446963)
          ·
            refine ⟨215622717081865595919670445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143748478054577063946446963 215622717081865595919670445)
            ·
              refine ⟨80858518905699598469876417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215622717081865595919670445 80858518905699598469876417)
              ·
                refine ⟨60643889179274698852407313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80858518905699598469876417 60643889179274698852407313)
                ·
                  refine ⟨45482916884456024139305485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60643889179274698852407313 45482916884456024139305485)
                  ·
                    refine ⟨17056093831671009052239557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45482916884456024139305485 17056093831671009052239557)
                    ·
                      refine ⟨3198017593438314197294917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17056093831671009052239557 3198017593438314197294917)
                      ·
                        rfl

theorem cell23_6228117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_6228117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228117 prefixEnd_6228117 := by exact prefixLift 6228117
  have htrace : WordTrace (prefixWord ++ tailWord_6228117) baseStart_6228117 baseEnd_6228117 := by
    simpa [prefixWord, tailWord_6228117, baseEnd_6228117] using wordTrace_append hprefix tailTrace_6228117
  have hstable : (prefixWord ++ tailWord_6228117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228117).length < 2 ^ (prefixWord ++ tailWord_6228117).sum := by decide
  have hdescent : baseEnd_6228117 < baseStart_6228117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228145 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6228145 : Nat := 118140960795 + 6228145 * 2 ^ 59
def prefixEnd_6228145 : Nat := 4983230072969 + 3 ^ 40 * 6228145 * 2
def baseEnd_6228145 : Nat := 3198031970896640087744789

theorem tailTrace_6228145 : CollatzResearch.WordTrace tailWord_6228145 prefixEnd_6228145 3198031970896640087744789 := by
  unfold tailWord_6228145
  simp only [CollatzResearch.WordTrace]
  refine ⟨227159110021501822327021889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151439406681001214884681259 227159110021501822327021889)
  ·
    refine ⟨170369332516126366745266417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227159110021501822327021889 170369332516126366745266417)
    ·
      refine ⟨127776999387094775058949813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170369332516126366745266417 127776999387094775058949813)
      ·
        refine ⟨11979093692540135161776545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127776999387094775058949813 11979093692540135161776545)
        ·
          refine ⟨8984320269405101371332409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11979093692540135161776545 8984320269405101371332409)
          ·
            refine ⟨6738240202053826028499307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8984320269405101371332409 6738240202053826028499307)
            ·
              refine ⟨10107360303080739042748961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738240202053826028499307 10107360303080739042748961)
              ·
                refine ⟨7580520227310554282061721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10107360303080739042748961 7580520227310554282061721)
                ·
                  refine ⟨5685390170482915711546291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7580520227310554282061721 5685390170482915711546291)
                  ·
                    refine ⟨8528085255724373567319437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5685390170482915711546291 8528085255724373567319437)
                    ·
                      refine ⟨3198031970896640087744789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8528085255724373567319437 3198031970896640087744789)
                      ·
                        rfl

theorem cell23_6228145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6228145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228145 prefixEnd_6228145 := by exact prefixLift 6228145
  have htrace : WordTrace (prefixWord ++ tailWord_6228145) baseStart_6228145 baseEnd_6228145 := by
    simpa [prefixWord, tailWord_6228145, baseEnd_6228145] using wordTrace_append hprefix tailTrace_6228145
  have hstable : (prefixWord ++ tailWord_6228145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228145).length < 2 ^ (prefixWord ++ tailWord_6228145).sum := by decide
  have hdescent : baseEnd_6228145 < baseStart_6228145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228174 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_6228174 : Nat := 118140960795 + 6228174 * 2 ^ 59
def prefixEnd_6228174 : Nat := 4983230072969 + 3 ^ 40 * 6228174 * 2
def baseEnd_6228174 : Nat := 355338540203957830475795

theorem tailTrace_6228174 : CollatzResearch.WordTrace tailWord_6228174 prefixEnd_6228174 355338540203957830475795 := by
  unfold tailWord_6228174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28395020967299595034978447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151440111825597840186551717 28395020967299595034978447)
  ·
    refine ⟨42592531450949392552467671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28395020967299595034978447 42592531450949392552467671)
    ·
      refine ⟨63888797176424088828701507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42592531450949392552467671 63888797176424088828701507)
      ·
        refine ⟨95833195764636133243052261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63888797176424088828701507 95833195764636133243052261)
        ·
          refine ⟨17968724205869274983072299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95833195764636133243052261 17968724205869274983072299)
          ·
            refine ⟨26953086308803912474608449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17968724205869274983072299 26953086308803912474608449)
            ·
              refine ⟨20214814731602934355956337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26953086308803912474608449 20214814731602934355956337)
              ·
                refine ⟨15161111048702200766967253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20214814731602934355956337 15161111048702200766967253)
                ·
                  refine ⟨355338540203957830475795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15161111048702200766967253 355338540203957830475795)
                  ·
                    rfl

theorem cell23_6228174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_6228174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228174 prefixEnd_6228174 := by exact prefixLift 6228174
  have htrace : WordTrace (prefixWord ++ tailWord_6228174) baseStart_6228174 baseEnd_6228174 := by
    simpa [prefixWord, tailWord_6228174, baseEnd_6228174] using wordTrace_append hprefix tailTrace_6228174
  have hstable : (prefixWord ++ tailWord_6228174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228174).length < 2 ^ (prefixWord ++ tailWord_6228174).sum := by decide
  have hdescent : baseEnd_6228174 < baseStart_6228174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228188 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6228188 : Nat := 118140960795 + 6228188 * 2 ^ 59
def prefixEnd_6228188 : Nat := 4983230072969 + 3 ^ 40 * 6228188 * 2
def baseEnd_6228188 : Nat := 3198054050564783419507091

theorem tailTrace_6228188 : CollatzResearch.WordTrace tailWord_6228188 prefixEnd_6228188 3198054050564783419507091 := by
  unfold tailWord_6228188
  simp only [CollatzResearch.WordTrace]
  refine ⟨113580339180173020335418609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151440452240230693780558145 113580339180173020335418609)
  ·
    refine ⟨85185254385129765251563957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113580339180173020335418609 85185254385129765251563957)
    ·
      refine ⟨7986117598605915492334121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85185254385129765251563957 7986117598605915492334121)
      ·
        refine ⟨5989588198954436619250591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7986117598605915492334121 5989588198954436619250591)
        ·
          refine ⟨8984382298431654928875887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989588198954436619250591 8984382298431654928875887)
          ·
            refine ⟨13476573447647482393313831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8984382298431654928875887 13476573447647482393313831)
            ·
              refine ⟨20214860171471223589970747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476573447647482393313831 20214860171471223589970747)
              ·
                refine ⟨30322290257206835384956121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20214860171471223589970747 30322290257206835384956121)
                ·
                  refine ⟨22741717692905126538717091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30322290257206835384956121 22741717692905126538717091)
                  ·
                    refine ⟨34112576539357689808075637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22741717692905126538717091 34112576539357689808075637)
                    ·
                      refine ⟨3198054050564783419507091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34112576539357689808075637 3198054050564783419507091)
                      ·
                        rfl

theorem cell23_6228188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6228188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228188 prefixEnd_6228188 := by exact prefixLift 6228188
  have htrace : WordTrace (prefixWord ++ tailWord_6228188) baseStart_6228188 baseEnd_6228188 := by
    simpa [prefixWord, tailWord_6228188, baseEnd_6228188] using wordTrace_append hprefix tailTrace_6228188
  have hstable : (prefixWord ++ tailWord_6228188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228188).length < 2 ^ (prefixWord ++ tailWord_6228188).sum := by decide
  have hdescent : baseEnd_6228188 < baseStart_6228188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6228204 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_6228204 : Nat := 118140960795 + 6228204 * 2 ^ 59
def prefixEnd_6228204 : Nat := 4983230072969 + 3 ^ 40 * 6228204 * 2
def baseEnd_6228204 : Nat := 1066020755418418452302339

theorem tailTrace_6228204 : CollatzResearch.WordTrace tailWord_6228204 prefixEnd_6228204 1066020755418418452302339 := by
  unfold tailWord_6228204
  simp only [CollatzResearch.WordTrace]
  refine ⟨113580630964144037701709833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151440841285525383602279777 113580630964144037701709833)
  ·
    refine ⟨85185473223108028276282375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113580630964144037701709833 85185473223108028276282375)
    ·
      refine ⟨127778209834662042414423563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85185473223108028276282375 127778209834662042414423563)
      ·
        refine ⟨191667314751993063621635345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127778209834662042414423563 191667314751993063621635345)
        ·
          refine ⟨143750486063994797716226509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191667314751993063621635345 143750486063994797716226509)
          ·
            refine ⟨53906432273998049143584941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143750486063994797716226509 53906432273998049143584941)
            ·
              refine ⟨20214912102749268428844353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53906432273998049143584941 20214912102749268428844353)
              ·
                refine ⟨15161184077061951321633265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20214912102749268428844353 15161184077061951321633265)
                ·
                  refine ⟨11370888057796463491224949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15161184077061951321633265 11370888057796463491224949)
                  ·
                    refine ⟨1066020755418418452302339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11370888057796463491224949 1066020755418418452302339)
                    ·
                      rfl

theorem cell23_6228204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_6228204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6228204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6228204 prefixEnd_6228204 := by exact prefixLift 6228204
  have htrace : WordTrace (prefixWord ++ tailWord_6228204) baseStart_6228204 baseEnd_6228204 := by
    simpa [prefixWord, tailWord_6228204, baseEnd_6228204] using wordTrace_append hprefix tailTrace_6228204
  have hstable : (prefixWord ++ tailWord_6228204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6228204).length < 2 ^ (prefixWord ++ tailWord_6228204).sum := by decide
  have hdescent : baseEnd_6228204 < baseStart_6228204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6228204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
